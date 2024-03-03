import LeanCircuit
import LeanCircuit.Common
import Mathlib
import ProvenZk

open Semaphore (F Order)

instance : Fact (Nat.Prime Semaphore.Order) := Fact.mk (by apply bn256_Fr_prime)

def sbox_uniqueAssignment (Inp : F): UniqueAssignment (Semaphore.sbox Inp) id := UniqueAssignment.mk _ $ by
  simp [Semaphore.sbox]; tauto

/-
  Poseidon Hash with 2 arguments
-/

def mds_3_uniqueAssignment (S : Vector F 3): UniqueAssignment (Semaphore.mds_3 S) id := UniqueAssignment.mk _ $ by
  simp [Semaphore.mds_3]; tauto

def fullRound_3_3_uniqueAssignment (S C : Vector F 3): UniqueAssignment (Semaphore.fullRound_3_3 S C) id := UniqueAssignment.mk _ $ by
  simp [Semaphore.fullRound_3_3, (sbox_uniqueAssignment _).equiv, (mds_3_uniqueAssignment _).equiv]; tauto

def halfRound_3_3_uniqueAssignment (S C : Vector F 3): UniqueAssignment (Semaphore.halfRound_3_3 S C) id := UniqueAssignment.mk _ $ by
  simp [Semaphore.halfRound_3_3, (sbox_uniqueAssignment _).equiv, (mds_3_uniqueAssignment _).equiv]; tauto

def poseidon_3_uniqueAssignment (inp : Vector F 3): UniqueAssignment (Semaphore.poseidon_3 inp) id := by
  unfold Semaphore.poseidon_3
  repeat (
    apply UniqueAssignment.compose
    . (first | apply fullRound_3_3_uniqueAssignment | apply halfRound_3_3_uniqueAssignment)
    intro _
  )
  apply UniqueAssignment.constant

theorem poseidon_3_testVector : (poseidon_3_uniqueAssignment (vec![0,1,2])).val = vec![0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a, 0x0fca49b798923ab0239de1c9e7a4a9a2210312b6a2f616d18b5a87f9b628ae29, 0x0e7ae82e40091e63cbd4f16a6d16310b3729d4b6e138fcf54110e2867045a30c] :=
  by native_decide

def poseidon₂ : Hash F 2 := fun a => (poseidon_3_uniqueAssignment vec![0, a.get 0, a.get 1]).val.get 0

lemma Poseidon2_uncps (a b : F) (k : F -> Prop) : Semaphore.Poseidon2 a b k ↔ k (poseidon₂ vec![a, b]) := by
    unfold Semaphore.Poseidon2 poseidon₂
    apply Iff.of_eq
    rw [(poseidon_3_uniqueAssignment _).equiv]
    congr

/-
  Poseidon Hash with 1 argument
-/

def mds_2_uniqueAssignment (S : Vector F 2): UniqueAssignment (Semaphore.mds_2 S) id := UniqueAssignment.mk _ $ by
  simp [Semaphore.mds_2]; tauto

def fullRound_2_2_uniqueAssignment (S C : Vector F 2): UniqueAssignment (Semaphore.fullRound_2_2 S C) id := UniqueAssignment.mk _ $ by
  simp [Semaphore.fullRound_2_2, (sbox_uniqueAssignment _).equiv, (mds_2_uniqueAssignment _).equiv]; tauto

def halfRound_2_2_uniqueAssignment (S C : Vector F 2): UniqueAssignment (Semaphore.halfRound_2_2 S C) id := UniqueAssignment.mk _ $ by
  simp [Semaphore.halfRound_2_2, (sbox_uniqueAssignment _).equiv, (mds_2_uniqueAssignment _).equiv]; tauto

def poseidon_2_uniqueAssignment (inp : Vector F 2): UniqueAssignment (Semaphore.poseidon_2 inp) id := by
  unfold Semaphore.poseidon_2
  repeat (
    apply UniqueAssignment.compose
    . (first | apply fullRound_2_2_uniqueAssignment | apply halfRound_2_2_uniqueAssignment)
    intro _
  )
  apply UniqueAssignment.constant

def poseidon₁ : Hash F 1 := fun a => (poseidon_2_uniqueAssignment vec![0, a.get 0]).val.get 0

lemma Poseidon1_uncps (a : F) (k : F -> Prop) : Semaphore.Poseidon1 a k ↔ k (poseidon₁ vec![a]) := by
    unfold Semaphore.Poseidon1 poseidon₁
    apply Iff.of_eq
    rw [(poseidon_2_uniqueAssignment _).equiv]
    congr
