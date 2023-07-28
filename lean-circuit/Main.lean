import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import LeanCircuit
import LeanCircuit.Poseidon.Spec
import LeanCircuit.Poseidon.Correctness

abbrev Order := Semaphore.Order
variable [Fact (Nat.Prime Order)]
abbrev F := Semaphore.F

def nat_to_dir : Nat -> Dir
    | 0 => Dir.right
    | 1 => Dir.left
    | Nat.succ (Nat.succ _) => panic "Dir can be 0 or 1"

def poseidon₁ : Hash F 1 := fun a => (Poseidon.perm Constants.x5_254_2 vec![0, a.get 0]).get 0
def poseidon₂ : Hash F 2 := fun a => (Poseidon.perm Constants.x5_254_3 vec![0, a.get 0, a.get 1]).get 0

def create_dir_vec {depth} (ix: Vector F depth) : Vector Dir depth :=
    Vector.map nat_to_dir (Vector.map ZMod.val ix)

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

def merkle_tree_recover_round (path : F) (node : F) (sibling : F) : F := match nat_to_dir path.val with
    | Dir.left => poseidon₂ vec![node, sibling]
    | Dir.right => poseidon₂ vec![sibling, node]

theorem merkle_recover_round_correct (Direction: F) (Hash: F) (Sibling: F) (k: F -> Prop) : 
    Semaphore.MerkleTreeRecoverRound Direction Hash Sibling k = k (merkle_tree_recover_round Direction Hash Sibling) := by
    sorry

def merkle_tree_recover_rounds_cps (merkle_tree_recover_round : F -> F -> F -> (F -> Prop) -> Prop) (Leaf : F) (PathIndices Siblings : Vector F n) (k : F -> Prop) : Prop := match n with
    | Nat.zero => k Leaf
    | Nat.succ _ => 
        merkle_tree_recover_round PathIndices.head Leaf Siblings.head fun next =>
            merkle_tree_recover_rounds_cps merkle_tree_recover_round next PathIndices.tail Siblings.tail k

theorem merkle_tree_recover_rounds_uncps
    {Leaf : F}
    {PathIndices Siblings : Vector F n}
    {k : F -> Prop} 
    {merkle_tree_recover_round_cps : F -> F -> F -> (F -> Prop) -> Prop}
    -- {merkle_tree_recover_round_uncps : ∀ Leaf PathIndices Siblings k, merkle_tree_recover_round_cps Leaf PathIndices Siblings k = k (merkle_tree_recover_round Leaf PathIndices Siblings)}
    : 
    merkle_tree_recover_rounds_cps merkle_tree_recover_round_cps Leaf PathIndices Siblings k = k (MerkleTree.recover poseidon₂ (create_dir_vec PathIndices) Siblings Leaf) := by
    induction n with
    | zero => 
        unfold merkle_tree_recover_rounds_cps
        unfold MerkleTree.recover
        rfl
    | succ _ ih =>
        unfold merkle_tree_recover_rounds_cps
        simp [<-MerkleTree.recover_tail_reverse_equals_recover]
        unfold MerkleTree.recover_tail
        simp
        
        sorry

def looped_merkle_tree_inclusion_proof (Leaf: F) (PathIndices: Vector F n) (Siblings: Vector F n) (k: F -> Prop): Prop :=
    merkle_tree_recover_rounds_cps Semaphore.MerkleTreeRecoverRound Leaf PathIndices Siblings k

theorem looped_merkle_tree_inclusion_proof_go (Leaf: F) (PathIndices: Vector F 3) (Siblings: Vector F 3) (k: F -> Prop):
    Semaphore.MerkleTreeInclusionProof_3_3 Leaf PathIndices Siblings k = looped_merkle_tree_inclusion_proof Leaf PathIndices Siblings k := by
    unfold Semaphore.MerkleTreeInclusionProof_3_3
    unfold looped_merkle_tree_inclusion_proof
    simp [merkle_tree_recover_rounds_cps]
    simp [merkle_tree_recover_rounds_cps]
    rw [←Vector.ofFn_get (v := PathIndices)]
    rw [←Vector.ofFn_get (v := Siblings)]
    rfl

theorem merkle_tree_inclusion_proof_correct (Leaf: F) (PathIndices: Vector F 3) (Siblings: Vector F 3) (k: F -> Prop):
  Semaphore.MerkleTreeInclusionProof_3_3 Leaf PathIndices Siblings k = k (MerkleTree.recover poseidon₂ (create_dir_vec PathIndices) Siblings Leaf) := by
    simp [looped_merkle_tree_inclusion_proof_go]
    simp [looped_merkle_tree_inclusion_proof]
    simp [merkle_tree_recover_rounds_uncps]

lemma circuit_simplified {IdentityNullifier IdentityTrapdoor SignalHash ExternalNullifier NullifierHash Root: F} {Path Proof: Vector F 3}:
    Semaphore.circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExternalNullifier NullifierHash Root ↔
    circuit_simpl IdentityNullifier IdentityTrapdoor ExternalNullifier NullifierHash Root Path Proof := by
    simp [
        Semaphore.circuit,
        circuit_simpl,
        Semaphore.Poseidon2,
        Semaphore.Poseidon1,
        nullifier_hash,
        identity_commitment,
        secret, poseidon₂,
        poseidon₁,
        Gates.eq,
        poseidon_3_correct,
        poseidon_2_correct,
        merkle_tree_inclusion_proof_correct,
        fold_vec_3
    ]
    apply Iff.intro <;> {
        intro h
        cases h
        subst_vars
        simp [getElem]
        tauto
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