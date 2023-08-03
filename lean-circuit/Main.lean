import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import LeanCircuit
import LeanCircuit.SemanticEquivalence

open Semaphore (F Order)

variable [Fact (Nat.Prime Order)]

-- always_possible_to_signal proves the "No Censorship" property of the Semaphore protocol.
-- Given an identity_commitment (identity hash) already present in Tree, it is always possible to signal.
-- Path is the direction vector to walk from the root to the identity hash (leaf)
theorem always_possible_to_signal
  (IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier : F)
  (Tree : MerkleTree F poseidon₂ 20)
  (Path : Vector Dir 20)
  (commitment_in_tree : Tree.item_at Path = identity_commitment IdentityNullifier IdentityTrapdoor)
  :
  Semaphore.circuit
    IdentityNullifier
    IdentityTrapdoor
    (embed_dir_vector Path.reverse)
    (Tree.proof Path).reverse
    SignalHash
    ExtNullifier
    (nullifier_hash ExtNullifier IdentityNullifier)
    Tree.root
  := by
    rw [circuit_semantics, ←MerkleTree.recover_proof_is_root, commitment_in_tree]
    simp [circuit_sem]
    apply embed_dir_vector_is_binary

-- signaller_is_in_tree proves the "No Unauthorized Signalling" property of the Semaphore protocol
-- If the circuit is successful, then it means that the identity_commitment (identity hash) is a leaf
-- of the Tree which means the identity has signed up.
-- Path is the direction vector to walk from the identity hash (leaf) to the root
theorem signaller_is_in_tree
    (IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier NullifierHash : F)
    (Tree : MerkleTree F poseidon₂ 20)
    (Path Proof: Vector F 20)
    [Fact (perfect_hash poseidon₂)]
    :
    Semaphore.circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExtNullifier NullifierHash Tree.root →
    Tree.item_at (Dir.create_dir_vec Path.reverse) = identity_commitment IdentityNullifier IdentityTrapdoor := by
    simp [circuit_semantics, circuit_sem]
    intros
    apply MerkleTree.proof_ceritfies_item
    assumption

-- no_double_signal_with_same_commitment proves the "No Double Signalling" property of the Semaphore protocol.
-- If there are two signals with the same ExtNullifier and identity_commitment, then it means they must have
-- the same NullifierHash which means the user has already submitted a signal because nullifier hash
-- is made up of identity hash (identity_commitment) and external voting hash (ExtNullifier).
theorem no_double_signal_with_same_commitment
    (IdentityNullifier₁ IdentityNullifier₂ IdentityTrapdoor₁ IdentityTrapdoor₂ SignalHash₁ SignalHash₂ ExtNullifier₁ ExtNullifier₂ NullifierHash₁ NullifierHash₂ Root₁ Root₂ : F)
    (Path₁ Proof₁ Path₂ Proof₂: Vector F 20)
    [Fact (perfect_hash poseidon₁)]
    [Fact (perfect_hash poseidon₂)]
    :
    Semaphore.circuit IdentityNullifier₁ IdentityTrapdoor₁ Path₁ Proof₁ SignalHash₁ ExtNullifier₁ NullifierHash₁ Root₁ →
    Semaphore.circuit IdentityNullifier₂ IdentityTrapdoor₂ Path₂ Proof₂ SignalHash₂ ExtNullifier₂ NullifierHash₂ Root₂ →
    ExtNullifier₁ = ExtNullifier₂ →
    identity_commitment IdentityNullifier₁ IdentityTrapdoor₁ = identity_commitment IdentityNullifier₂ IdentityTrapdoor₂ →
    NullifierHash₁ = NullifierHash₂ := by
    simp [circuit_semantics, circuit_sem, secret, Vector.eq_cons_iff]
    intros
    subst_vars
    rfl

def main : IO Unit := pure ()