import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import LeanCircuit
import LeanCircuit.Poseidon.Spec
import LeanCircuit.Poseidon.Correctness

open Semaphore (F Order)

variable [Fact (Nat.Prime Order)]

def nat_to_dir : Nat -> Dir
  | 0 => Dir.left
  | 1 => Dir.right
  | Nat.succ (Nat.succ _) => panic "Dir can be 0 or 1"

def create_dir_vec {depth} (ix: Vector F depth) : Vector Dir depth :=
  Vector.map nat_to_dir (Vector.map ZMod.val ix)

def embed_dir : Dir -> F
  | Dir.left => 0
  | Dir.right => 1

def embed_dir_vector {depth} (ix: Vector Dir depth) : Vector F depth :=
  Vector.map embed_dir ix

lemma dir_embed_recover {d : Dir} : nat_to_dir (embed_dir d).val = d := by
  cases d <;> rfl

@[simp]
lemma dir_embed_recover_vector {depth} (ix: Vector Dir depth) :
  create_dir_vec (embed_dir_vector ix) = ix := by
  simp [create_dir_vec, embed_dir_vector, dir_embed_recover]
  apply Vector.eq
  simp

@[simp]
lemma embed_dir_vector_reverse {depth} (ix : Vector Dir depth) :
  embed_dir_vector ix.reverse = (embed_dir_vector ix).reverse := by
  simp [embed_dir_vector]
  apply Vector.eq
  simp [Vector.toList_reverse, List.map_reverse]

@[simp]
lemma create_dir_vec_reverse {depth} (ix : Vector F depth) :
  create_dir_vec ix.reverse = (create_dir_vec ix).reverse := by
  simp [create_dir_vec]
  apply Vector.eq
  simp [Vector.toList_reverse, List.map_reverse]

lemma foldr_snoc_cons {α β} {f : α -> β -> β} {b : β} {x : α} {xs : List α}
  {f_comm_assoc : ∀ x y z, f x (f y z) = f y (f x z)} :
  List.foldr f b (xs ++ [x]) = List.foldr f b (x :: xs) := by
  induction xs generalizing x with
  | nil => rfl
  | cons x' xs ih =>
    conv =>
      lhs
      simp only [List.foldr]
      tactic => have : (xs ++ [x]) = xs.append [x] := by simp
      rw [←this, ih]
    simp [List.foldr, f_comm_assoc]

lemma foldr_reverse {α β} {f : α -> β -> β} {b : β} {xs : List α}
  { f_comm_assoc : ∀ x y z, f x (f y z) = f y (f x z) } :
  List.foldr f b xs = List.foldr f b xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, foldr_snoc_cons]
    simp only [List.foldr, ih]
    assumption

@[simp]
lemma is_vector_binary_reverse {depth} (ix : Vector F depth):
  is_vector_binary ix.reverse ↔ is_vector_binary ix := by
  simp only [is_vector_binary, Vector.toList_reverse]
  rw [foldr_reverse]
  { simp }
  { intros; simp; tauto }

lemma embed_dir_vector_is_binary {depth} (ix : Vector Dir depth) :
  is_vector_binary (embed_dir_vector ix) := by
  simp [is_vector_binary, embed_dir_vector]
  induction ix using Vector.inductionOn with
  | h_nil => simp [is_vector_binary]
  | @h_cons n d ds ih =>
    simp [is_vector_binary_cons]
    apply And.intro
    { simp [embed_dir, is_bit]; cases d <;> simp }
    { assumption }

def poseidon₁ : Hash F 1 := fun a => (Poseidon.perm Constants.x5_254_2 vec![0, a.get 0]).get 0

lemma Poseidon1_uncps (a : F) (k : F -> Prop) : Semaphore.Poseidon1 a k ↔ k (poseidon₁ vec![a]) := by
    simp [Semaphore.Poseidon1, poseidon₁, poseidon_2_correct, getElem]

def poseidon₂ : Hash F 2 := fun a => (Poseidon.perm Constants.x5_254_3 vec![0, a.get 0, a.get 1]).get 0

lemma Poseidon2_uncps (a b : F) (k : F -> Prop) : Semaphore.Poseidon2 a b k ↔ k (poseidon₂ vec![a, b]) := by
    simp [Semaphore.Poseidon2, poseidon₂, poseidon_3_correct, getElem]
    rfl

@[simp]
lemma create_dir_vec_cons {ix : F} {ixes: Vector F d} :
  create_dir_vec (ix ::ᵥ ixes) = nat_to_dir ix.val ::ᵥ create_dir_vec ixes := by
  simp [create_dir_vec]

lemma MerkleTreeRecoverRound_uncps {dir hash sibling : F} {k : F -> Prop}:
    Semaphore.MerkleTreeRecoverRound dir hash sibling k ↔
    is_bit dir ∧ k (match nat_to_dir dir.val with
    | Dir.left => poseidon₂ vec![hash, sibling]
    | Dir.right => poseidon₂ vec![sibling, hash]) := by
    simp [Semaphore.MerkleTreeRecoverRound, Gates.is_bool]
    intro hb
    rw [Poseidon2_uncps, Poseidon2_uncps]
    cases hb <;> {
        simp [*, Gates.select, Gates.is_bool, nat_to_dir]
        try rfl
    }

def merkle_tree_recover_rounds (Leaf : F) (PathIndices Siblings : Vector F n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k Leaf
  | Nat.succ _ => Semaphore.MerkleTreeRecoverRound PathIndices.head Leaf Siblings.head fun next =>
    merkle_tree_recover_rounds next PathIndices.tail Siblings.tail k

lemma merkle_tree_recover_rounds_uncps
  {Leaf : F}
  {PathIndices Siblings : Vector F n}
  {k : F -> Prop}:
  merkle_tree_recover_rounds Leaf PathIndices Siblings k ↔
  is_vector_binary PathIndices ∧ k (MerkleTree.recover_tail poseidon₂ (create_dir_vec PathIndices) Siblings Leaf) := by
  induction PathIndices, Siblings using Vector.inductionOn₂ generalizing Leaf with
  | nil =>
    simp [is_vector_binary]
    rfl
  | @cons n ix sib ixes sibs ih =>
    simp [MerkleTree.recover_tail_reverse_equals_recover, MerkleTree.recover_tail, merkle_tree_recover_rounds]
    simp [MerkleTreeRecoverRound_uncps, is_vector_binary_cons, and_assoc, ih]
    intros
    rfl

lemma MerkleTreeInclusionProof_looped (Leaf: F) (PathIndices: Vector F 3) (Siblings: Vector F 3) (k: F -> Prop):
    Semaphore.MerkleTreeInclusionProof_3_3 Leaf PathIndices Siblings k =
      merkle_tree_recover_rounds Leaf PathIndices Siblings k := by
    unfold Semaphore.MerkleTreeInclusionProof_3_3
    simp [merkle_tree_recover_rounds]
    simp [merkle_tree_recover_rounds]
    rw [←Vector.ofFn_get (v := PathIndices)]
    rw [←Vector.ofFn_get (v := Siblings)]
    rfl

lemma MerkleTreeInclusionProof_3_3_uncps {Leaf : F} {PathIndices Siblings : Vector F 3} {k : F -> Prop}:
    Semaphore.MerkleTreeInclusionProof_3_3 Leaf PathIndices Siblings k ↔
    is_vector_binary PathIndices ∧ k (MerkleTree.recover_tail poseidon₂ (create_dir_vec PathIndices) Siblings Leaf) := by
    simp [MerkleTreeInclusionProof_looped, merkle_tree_recover_rounds_uncps]

abbrev secret (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
  poseidon₂ vec![IdentityNullifier, IdentityTrapdoor]

abbrev identity_commitment (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
  poseidon₁ vec![(secret IdentityNullifier IdentityTrapdoor)]

abbrev nullifier_hash (ExternalNullifier: F) (IdentityNullifier: F) : F :=
  poseidon₂ vec![ExternalNullifier, IdentityNullifier]

def circuit_sem (IdentityNullifier IdentityTrapdoor ExternalNullifier NullifierHash Root: F) (Path Proof: Vector F 3): Prop :=
    NullifierHash = nullifier_hash ExternalNullifier IdentityNullifier ∧
    is_vector_binary Path ∧
    MerkleTree.recover poseidon₂ (create_dir_vec Path).reverse Proof.reverse (identity_commitment IdentityNullifier IdentityTrapdoor) = Root

theorem circuit_semantics {IdentityNullifier IdentityTrapdoor SignalHash ExternalNullifier NullifierHash Root: F} {Path Proof: Vector F 3}:
    Semaphore.circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExternalNullifier NullifierHash Root ↔
    circuit_sem IdentityNullifier IdentityTrapdoor ExternalNullifier NullifierHash Root Path Proof := by
    simp [
      circuit_sem,
      Semaphore.circuit,
      Poseidon2_uncps,
      Poseidon1_uncps,
      MerkleTreeInclusionProof_3_3_uncps,
      Gates.eq,
      nullifier_hash,
      create_dir_vec
    ]
    apply Iff.intro <;> {
      intro h
      cases h; rename_i _ r
      cases r
      subst_vars
      rw [←Vector.ofFn_get (v := Path)] at *
      rw [←Vector.ofFn_get (v := Proof)]
      tauto
    }