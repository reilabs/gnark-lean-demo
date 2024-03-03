import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import LeanCircuit
import LeanCircuit.SemanticEquivalence

open Semaphore (F Order)

variable [Fact (Nat.Prime Order)]

theorem always_possible_to_signal
  [Fact (CollisionResistant poseidon₂)]
  (IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier : F)
  (Tree : MerkleTree F poseidon₂ 20)
  (Path : Vector Bool 20)
  (commitment_in_tree : Tree.itemAt Path = identity_commitment IdentityNullifier IdentityTrapdoor)
  :
  Semaphore.circuit
    IdentityNullifier
    IdentityTrapdoor
    (Vector.map Bool.toZMod Path.reverse)
    (Tree.proof Path).reverse
    SignalHash
    ExtNullifier
    (nullifier_hash ExtNullifier IdentityNullifier)
    Tree.root
  := by
    simp [circuit_semantics_bool, circuit_sem]
    rw [←commitment_in_tree]

theorem signaller_is_in_tree
    [Fact (CollisionResistant poseidon₂)]
    (IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier NullifierHash : F)
    (Tree : MerkleTree F poseidon₂ 20)
    (Path Proof: Vector F 20)
    :
    (is_vector_binary Path ∧ ∃x : Vector Bool D, Path = x.map Bool.toZMod) →
    Semaphore.circuit IdentityNullifier IdentityTrapdoor (Vector.map Bool.toZMod x) Proof SignalHash ExtNullifier NullifierHash Tree.root →
    Tree.itemAt (Vector.reverse x) = identity_commitment IdentityNullifier IdentityTrapdoor := by
    intro hbin
    simp [circuit_semantics_bool]
    intros h
    simp [circuit_sem] at h
    casesm* (_ ∧ _)
    rename_i h
    simp [h]

theorem no_double_signal_with_same_commitment
    [Fact (CollisionResistant poseidon₁)]
    [Fact (CollisionResistant poseidon₂)]
    (IdentityNullifier₁ IdentityNullifier₂ IdentityTrapdoor₁ IdentityTrapdoor₂ SignalHash₁ SignalHash₂ ExtNullifier₁ ExtNullifier₂ NullifierHash₁ NullifierHash₂ Root₁ Root₂ : F)
    (Path₁ Proof₁ Path₂ Proof₂: Vector F 20)
    :
    (is_vector_binary Path₁ ∧ ∃x₁ : Vector Bool D, Path₁ = x₁.map Bool.toZMod) →
    (is_vector_binary Path₂ ∧ ∃x₂ : Vector Bool D, Path₂ = x₂.map Bool.toZMod) →
    Semaphore.circuit IdentityNullifier₁ IdentityTrapdoor₁ (Vector.map Bool.toZMod x₁) Proof₁ SignalHash₁ ExtNullifier₁ NullifierHash₁ Root₁ →
    Semaphore.circuit IdentityNullifier₂ IdentityTrapdoor₂ (Vector.map Bool.toZMod x₂) Proof₂ SignalHash₂ ExtNullifier₂ NullifierHash₂ Root₂ →
    ExtNullifier₁ = ExtNullifier₂ →
    identity_commitment IdentityNullifier₁ IdentityTrapdoor₁ = identity_commitment IdentityNullifier₂ IdentityTrapdoor₂ →
    NullifierHash₁ = NullifierHash₂ := by
    simp [circuit_semantics_bool, circuit_sem, secret, Vector.eq_cons_iff]
    intros
    subst_vars
    rfl

def main : IO Unit := pure ()
