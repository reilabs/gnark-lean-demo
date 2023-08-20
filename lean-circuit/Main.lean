import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import LeanCircuit
import LeanCircuit.SemanticEquivalence

open Semaphore (F Order)

variable [Fact (Nat.Prime Order)]

theorem embed_dir_vector_cons {depth} {ix: Dir} {ixes: Vector Dir depth} :
  (embed_dir_vector (ix ::ᵥ ixes)) = (embed_dir ix) ::ᵥ (embed_dir_vector ixes) := by
    conv => lhs; unfold embed_dir_vector; unfold Vector.map

def dir_vec_is_dir {depth : Nat} {ix: Vector Dir depth} :
  mcreate_dir_vec (embed_dir_vector ix) = some ix := by
  induction ix using Vector.inductionOn
  case h_nil => {
    simp
  }
  case h_cons => {
    rename_i ih
    rename_i ixes
    rename_i ix
    cases ix
    case left => {
      simp [embed_dir_vector_cons]
      unfold embed_dir
      unfold Dir.toZMod
      simp
      simp [mcreate_dir_vec, Vector.mmap_cons, Bind.bind]
      tauto
    }
    case right => {
      simp [embed_dir_vector_cons]
      unfold embed_dir
      unfold Dir.toZMod
      simp
      simp [mcreate_dir_vec, Vector.mmap_cons, Bind.bind]
      tauto
    }
  }

def dir_vec_is_dir_reverse {depth : Nat} {ix: Vector Dir depth} :
  mcreate_dir_vec (Vector.reverse (embed_dir_vector ix)) = some (ix.reverse) := by
  rw [<-embed_dir_vector_reverse]
  simp only [dir_vec_is_dir]

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
    apply And.intro
    case left => {
      apply embed_dir_vector_is_binary
    }
    case right => {
      rw [dir_vec_is_dir_reverse]
      simp
    }

theorem signaller_is_in_tree
    (IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier NullifierHash : F)
    (Tree : MerkleTree F poseidon₂ 20)
    (Path Proof: Vector F 20)
    [Fact (perfect_hash poseidon₂)]
    :
    Semaphore.circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExtNullifier NullifierHash Tree.root →
    (∃x, mcreate_dir_vec Path.reverse = some x ∧ MerkleTree.item_at Tree x = identity_commitment IdentityNullifier IdentityTrapdoor) := by
    simp [circuit_semantics, circuit_sem]
    intros
    sorry
    -- apply MerkleTree.proof_ceritfies_item
    -- assumption

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