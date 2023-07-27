import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import LeanCircuit
import LeanCircuit.Poseidon.Spec
import LeanCircuit.Poseidon.Correctness

abbrev Order := Semaphore.Order
variable [Fact (Nat.Prime Order)]
abbrev F := Semaphore.F

def nat_to_dir : Fin 2 -> Dir
    | 0 => Dir.right
    | 1 => Dir.left

def poseidon₁ : Hash F 1 := fun a => (Poseidon.perm Constants.x5_254_2 vec![0, a.get 0]).get 0
def poseidon₂ : Hash F 2 := fun a => (Poseidon.perm Constants.x5_254_3 vec![0, a.get 0, a.get 1]).get 0

def create_dir_vec {depth} (ix: Vector F depth) : Vector Dir depth :=
    Vector.map nat_to_dir (Vector.map (fun v => v.val) ix)

abbrev secret (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
    poseidon₂ vec![IdentityNullifier, IdentityTrapdoor]

abbrev identity_commitment (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
    poseidon₁ vec![(secret IdentityNullifier IdentityTrapdoor)]

abbrev nullifier_hash (ExternalNullifier: F) (IdentityNullifier: F) : F :=
    poseidon₂ vec![ExternalNullifier, IdentityNullifier]

theorem same_hash_same_identity (IdentityNullifier₁ IdentityNullifier₂ IdentityTrapdoor₁ IdentityTrapdoor₂ : F)
    [Fact (perfect_hash poseidon₂)]
    [Fact (perfect_hash poseidon₁)]:
    identity_commitment IdentityNullifier₁ IdentityTrapdoor₁ = identity_commitment IdentityNullifier₂ IdentityTrapdoor₂ ↔
    (IdentityNullifier₁ = IdentityNullifier₂ ∧ IdentityTrapdoor₁ = IdentityTrapdoor₂) := by
    apply Iff.intro
    case mp => {
        intro h
        simp [Vector.eq_cons_iff] at h
        assumption
    }
    case mpr => { intro h; simp [h] }

def circuit_simpl (IdentityNullifier IdentityTrapdoor ExternalNullifier NullifierHash Root: F) (Path Proof: Vector F 3): Prop :=
    NullifierHash = nullifier_hash ExternalNullifier IdentityNullifier ∧
    MerkleTree.recover poseidon₂ (create_dir_vec Path) Proof (identity_commitment IdentityNullifier IdentityTrapdoor) = Root

lemma get_vec_0 {d : Nat} {a : Vector α (Nat.succ d)} : (Vector.get a 0) = a[0] := by rfl
lemma get_vec_1 {d : Nat} {a : Vector α (Nat.succ (Nat.succ d))} : (Vector.get a 1) = a[1] := by rfl

lemma head_is_get {d : Nat} {v : Vector α (Nat.succ d)} : (Vector.head v) = v[0] := by sorry

lemma replace_get_1 {a b : F} : (Vector.get vec![a, b] 1) = b := by rfl

theorem merkle_recover_correct (Leaf: F) (PathIndices: Vector F 3) (Siblings: Vector F 3) (k: F -> Prop):
  Semaphore.MerkleTreeInclusionProof_3_3 Leaf PathIndices Siblings k = k (MerkleTree.recover poseidon₂ (create_dir_vec PathIndices) Siblings Leaf) := by
    unfold Semaphore.MerkleTreeInclusionProof_3_3
    unfold MerkleTree.recover
    unfold Semaphore.Poseidon2
    simp [poseidon_3_correct]
    unfold poseidon₂
    simp [get_vec_0]
    simp [get_vec_1]
    simp [head_is_get]

    sorry

lemma circuit_simplified {IdentityNullifier IdentityTrapdoor SignalHash ExternalNullifier NullifierHash Root: F} {Path Proof: Vector F 3}:
    Semaphore.circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExternalNullifier NullifierHash Root ↔
    circuit_simpl IdentityNullifier IdentityTrapdoor ExternalNullifier NullifierHash Root Path Proof := by
    unfold Semaphore.circuit
    unfold circuit_simpl
    unfold Semaphore.Poseidon2
    unfold Semaphore.Poseidon1
    unfold nullifier_hash
    unfold identity_commitment
    unfold secret
    unfold poseidon₂
    unfold poseidon₁
    unfold Gates.eq
    simp [poseidon_3_correct, poseidon_2_correct, merkle_recover_correct]
    unfold poseidon₂
    simp [poseidon_2_correct, fold_vec_3]
    apply Iff.intro
    case _ => {
        intro h
        cases h
        rename_i h₁ h₂
        apply And.intro
        case _ => {
            rw [<-h₁]
            simp [replace_get_1, head_is_get]
            rfl
        }
        case _ => {
            rw [<-h₂]
            simp [replace_get_1, head_is_get]
            rfl
        }
    }
    case _ => {
        intro h
        cases h
        rename_i h₁ h₂
        apply And.intro
        case _ => {
            rw [h₁]
            simp [replace_get_1, head_is_get]
            rfl
        }
        case _ => {
            rw [<-h₂]
            simp [replace_get_1, head_is_get]
            rfl
        }
    }

theorem always_possible_to_signal
    (IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier : F)
    (Tree : MerkleTree F poseidon₂ 3)
    (Path : Vector F 3)
    (comm_in_tree : Tree.item_at (create_dir_vec Path) = identity_commitment IdentityNullifier IdentityTrapdoor)
    :
    Semaphore.circuit
        IdentityNullifier
        IdentityTrapdoor
        Path
        (Tree.proof (create_dir_vec Path)) -- Siblings
        SignalHash
        ExtNullifier
        (nullifier_hash ExtNullifier IdentityNullifier) -- NullifierHash
        Tree.root := by
        rw [circuit_simplified]
        rw [←MerkleTree.recover_proof_is_root]
        rw [comm_in_tree]
        unfold circuit_simpl
        simp

theorem signaller_is_in_tree
    (IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier NullifierHash : F)
    (Tree : MerkleTree F poseidon₂ 3)
    (Path Proof: Vector F 3)
    [Fact (perfect_hash poseidon₂)]
    :
    Semaphore.circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExtNullifier NullifierHash Tree.root →
    Tree.item_at (create_dir_vec Path) = identity_commitment IdentityNullifier IdentityTrapdoor := by
    rw [circuit_simplified]
    intro h
    unfold circuit_simpl at h
    cases h
    rw [<-MerkleTree.proof_ceritfies_item (create_dir_vec Path) Tree Proof (identity_commitment IdentityNullifier IdentityTrapdoor)]
    assumption

theorem no_double_signal_with_same_commitment
    (IdentityNullifier₁ IdentityNullifier₂ IdentityTrapdoor₁ IdentityTrapdoor₂ SignalHash₁ SignalHash₂ ExtNullifier₁ ExtNullifier₂ NullifierHash₁ NullifierHash₂ Root₁ Root₂ : F)
    (Path₁ Proof₁ Path₂ Proof₂: Vector F 3)
    [Fact (perfect_hash poseidon₁)]
    [Fact (perfect_hash poseidon₂)]
    :
    Semaphore.circuit IdentityNullifier₁ IdentityTrapdoor₁ Path₁ Proof₁ SignalHash₁ ExtNullifier₁ NullifierHash₁ Root₁ →
    Semaphore.circuit IdentityNullifier₂ IdentityTrapdoor₂ Path₂ Proof₂ SignalHash₂ ExtNullifier₂ NullifierHash₂ Root₂ →
    ExtNullifier₁ = ExtNullifier₂ →
    identity_commitment IdentityNullifier₁ IdentityTrapdoor₁ = identity_commitment IdentityNullifier₂ IdentityTrapdoor₂ →
    NullifierHash₁ = NullifierHash₂ := by
    simp [circuit_simplified, circuit_simpl]
    intro _ _ _ _ _ idCommEq
    simp [secret, Vector.eq_cons_iff] at idCommEq
    simp [*]

def main : IO Unit := do
    IO.println "Hello, world!"