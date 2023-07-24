import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import LeanCircuit

abbrev Order := Semaphore.Order
variable [Fact (Nat.Prime Order)]
abbrev F := Semaphore.F

def nat_to_dir : Nat -> Dir
    | 0 => Dir.right
    | 1 => Dir.left
    | Nat.succ (Nat.succ _) => panic "Dir can be 0 or 1"

def create_dir_vec {depth} (ix: Vector F depth) : Vector Dir depth :=
    Vector.map nat_to_dir (Vector.map ZMod.val ix)

def identity_commitment {F: Type} (H₁: Hash F 1) (H₂: Hash F 2) (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
    H₁ vec![H₂ vec![IdentityNullifier, IdentityTrapdoor]]

def nullifier_hash {F: Type} (H₂: Hash F 2) (IdentityNullifier: F) (ExternalNullifier: F) : F :=
    H₂ vec![ExternalNullifier, IdentityNullifier]

def dummy_hash₁ : Hash F 1 := fun a => a[0] * a[0]
def dummy_hash₂ : Hash F 2 := fun a => a[0] * a[1]

theorem same_hash_same_identity (IdentityNullifier₁ IdentityNullifier₂ IdentityTrapdoor₁ IdentityTrapdoor₂ : F)
    [Fact (perfect_hash dummy_hash₂)]
    [Fact (perfect_hash dummy_hash₁)]:
    identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier₁ IdentityTrapdoor₁ = identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier₂ IdentityTrapdoor₂ ↔
    (IdentityNullifier₁ = IdentityNullifier₂ ∧ IdentityTrapdoor₁ = IdentityTrapdoor₂) :=
    by sorry

def circuit_simpl (H₁: Hash F 1) (H₂: Hash F 2) (IdentityNullifier IdentityTrapdoor _ ExternalNullifier NullifierHash Root: F) (Path Proof: Vector F 3): Prop :=
    NullifierHash = nullifier_hash H₂ ExternalNullifier IdentityNullifier ∧
    MerkleTree.recover H₂ (create_dir_vec Path) Proof (identity_commitment H₁ H₂ IdentityNullifier IdentityTrapdoor) = Root

lemma circuit_simplified {IdentityNullifier IdentityTrapdoor SignalHash ExternalNullifier NullifierHash Root: F} {Path Proof: Vector F 3}:
    Semaphore.circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExternalNullifier NullifierHash Root ↔
    circuit_simpl dummy_hash₁ dummy_hash₂ IdentityNullifier IdentityTrapdoor SignalHash ExternalNullifier NullifierHash Root Path Proof := by
    sorry

theorem always_possible_to_signal
    (IdentityNullifier IdentitityTrapdoor SignalHash ExtNullifier : F)
    (Tree : MerkleTree F dummy_hash₂ 3)
    (Path : Vector F 3)
    (comm_in_tree : Tree.item_at (create_dir_vec Path) = identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier IdentitityTrapdoor)
    :
    Semaphore.circuit
        IdentityNullifier
        IdentitityTrapdoor
        Path
        (Tree.proof (create_dir_vec Path)) -- Siblings
        SignalHash
        ExtNullifier
        (nullifier_hash dummy_hash₂ ExtNullifier IdentityNullifier) -- NullifierHash
        Tree.root := by
        rw [circuit_simplified]
        rw [<-MerkleTree.recover_proof_is_root _ (create_dir_vec Path) Tree]
        rw [comm_in_tree]
        unfold circuit_simpl
        simp

theorem circuit_proof (IdentityNullifier IdentityTrapdoor SignalHash ExternalNullifier NullifierHash : F) (Path Proof: Vector F 3) (Tree : MerkleTree F dummy_hash₂ 3) 
    [Fact (perfect_hash dummy_hash₂)]:
    Semaphore.circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExternalNullifier NullifierHash Tree.root =
    Semaphore.circuit IdentityNullifier IdentityTrapdoor Path (MerkleTree.proof Tree (create_dir_vec Path)) SignalHash ExternalNullifier NullifierHash Tree.root := by
    rw [circuit_simplified]
    rw [circuit_simplified]
    unfold circuit_simpl
    simp
    intro
    rw [MerkleTree.same_root_same_proof]
    simp

theorem signaller_is_in_tree
    (IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier NullifierHash : F)
    (Tree : MerkleTree F dummy_hash₂ 3)
    (Path Proof: Vector F 3)
    [Fact (perfect_hash dummy_hash₂)]
    :
    Semaphore.circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExtNullifier NullifierHash Tree.root →
    Tree.item_at (create_dir_vec Path) = identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier IdentityTrapdoor := by
    rw [circuit_proof IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier NullifierHash Path Proof Tree]
    rw [circuit_simplified]
    unfold circuit_simpl
    rw [<-MerkleTree.recover_proof_is_root _ (create_dir_vec Path) Tree]
    let path := create_dir_vec Path
    let proof := MerkleTree.proof Tree (create_dir_vec Path)
    rw [MerkleTree.equal_recover_equal_tree dummy_hash₂ path proof (identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier IdentityTrapdoor)
                                                                   (MerkleTree.item_at Tree (create_dir_vec Path))]
    intro h
    cases h
    apply Eq.symm
    assumption

theorem no_double_signal_with_same_commitment
    (IdentityNullifier₁ IdentityNullifier₂ IdentityTrapdoor₁ IdentityTrapdoor₂ SignalHash₁ SignalHash₂ ExtNullifier₁ ExtNullifier₂ NullifierHash₁ NullifierHash₂ Root₁ Root₂ : F)
    (Path₁ Proof₁ Path₂ Proof₂: Vector F 3)
    [Fact (perfect_hash dummy_hash₂)]
    [Fact (perfect_hash dummy_hash₁)]
    :
    Semaphore.circuit IdentityNullifier₁ IdentityTrapdoor₁ Path₁ Proof₁ SignalHash₁ ExtNullifier₁ NullifierHash₁ Root₁ →
    Semaphore.circuit IdentityNullifier₂ IdentityTrapdoor₂ Path₂ Proof₂ SignalHash₂ ExtNullifier₂ NullifierHash₂ Root₂ →
    ExtNullifier₁ = ExtNullifier₂ →
    identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier₁ IdentityTrapdoor₁ = identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier₂ IdentityTrapdoor₂ →
    NullifierHash₁ = NullifierHash₂ := by
    rw [circuit_simplified]
    rw [circuit_simplified]
    unfold circuit_simpl
    intro h₁ h₂ h₃ h₄
    cases h₁
    rename_i hl₁ hr₁
    cases h₂
    rename_i hl₂ hr₂ 
    rw [hl₂, hl₁]
    rw [same_hash_same_identity] at h₄
    cases h₄
    rename_i hl₄ hr₄
    rw [h₃, hl₄]
