import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import LeanCircuit
import LeanCircuit.Poseidon
-- import LeanCircuit.Poseidon.Spec
-- import LeanCircuit.Poseidon.Correctness

open Semaphore (F Order)

variable [Fact (Nat.Prime Order)]

-- abbrev D := 20

-- def embed_dir : Dir -> F
--   | x => Dir.toZMod x

-- def embed_dir_vector {depth} (ix: Vector Dir depth) : Vector F depth :=
--   Vector.map embed_dir ix

-- lemma dir_embed_recover {d : Dir} : Dir.nat_to_dir (embed_dir d).val = d := by
--   cases d <;> rfl

-- @[simp]
-- lemma dir_embed_recover_vector {depth} (ix: Vector Dir depth) :
--   Dir.create_dir_vec (embed_dir_vector ix) = ix := by
--   simp [Dir.create_dir_vec, embed_dir_vector, dir_embed_recover]
--   apply Vector.eq
--   simp

-- @[simp]
-- lemma embed_dir_vector_reverse {depth} (ix : Vector Dir depth) :
--   embed_dir_vector ix.reverse = (embed_dir_vector ix).reverse := by
--   simp [embed_dir_vector]
--   apply Vector.eq
--   simp [Vector.toList_reverse, List.map_reverse]

-- lemma embed_dir_vector_is_binary {depth} (ix : Vector Dir depth) :
--   is_vector_binary (embed_dir_vector ix) := by
--   simp [is_vector_binary, embed_dir_vector]
--   induction ix using Vector.inductionOn with
--   | h_nil => simp [is_vector_binary]
--   | @h_cons n d ds ih =>
--     simp [is_vector_binary_cons]
--     apply And.intro
--     { simp [embed_dir, is_bit]; cases d <;> simp }
--     { assumption }

-- def poseidon₁ : Hash F 1 := fun a => (Poseidon.perm Constants.x5_254_2 vec![0, a.get 0]).get 0

-- lemma Poseidon1_uncps (a : F) (k : F -> Prop) : Semaphore.Poseidon1 a k ↔ k (poseidon₁ vec![a]) := by
--     simp [Semaphore.Poseidon1, poseidon₁, poseidon_2_correct, getElem]

-- def poseidon₂ : Hash F 2 := fun a => (Poseidon.perm Constants.x5_254_3 vec![0, a.get 0, a.get 1]).get 0

-- lemma Poseidon2_uncps (a b : F) (k : F -> Prop) : Semaphore.Poseidon2 a b k ↔ k (poseidon₂ vec![a, b]) := by
--     simp [Semaphore.Poseidon2, poseidon₂, poseidon_3_correct, getElem]
--     rfl

def hashLevel (d : Bool) (h s : F): F := match d with
  | false => poseidon₂ (vec![h, s])
  | true => poseidon₂ (vec![s, h])

lemma MerkleTreeRecoverRound_uncps {dir: Bool} {hash sibling : F} {k : F -> Prop}:
    Semaphore.MerkleTreeRecoverRound dir.toZMod hash sibling k ↔
    k (hashLevel dir hash sibling) := by
    cases dir <;>
      simp [Semaphore.MerkleTreeRecoverRound, Gates.is_bool, hashLevel, Poseidon2_uncps, Poseidon2_uncps]

lemma MerkleTreeRecoverRound_bool {dir: F} {hash sibling : F} {k : F -> Prop}:
    Semaphore.MerkleTreeRecoverRound dir hash sibling k → is_bit dir := by
      simp [Semaphore.MerkleTreeRecoverRound]
      intros; assumption

def merkle_tree_recover_rounds (Leaf : F) (PathIndices Siblings : Vector F n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k Leaf
  | Nat.succ _ => Semaphore.MerkleTreeRecoverRound PathIndices.head Leaf Siblings.head fun next =>
    merkle_tree_recover_rounds next PathIndices.tail Siblings.tail k

lemma merkle_tree_recover_rounds_uncps
  {Leaf : F}
  {PathIndices : Vector Bool n}
  {Siblings : Vector F n}
  {k : F -> Prop}:
  merkle_tree_recover_rounds Leaf (Vector.map Bool.toZMod PathIndices) Siblings k ↔
  k (MerkleTree.recover poseidon₂ PathIndices.reverse Siblings.reverse Leaf) := by
  induction PathIndices, Siblings using Vector.inductionOn₂ generalizing Leaf with
  | nil =>
    simp [is_vector_binary]
    rfl
  | @cons n ix sib ixes sibs ih =>
    simp [merkle_tree_recover_rounds]
    simp [MerkleTreeRecoverRound_uncps, is_vector_binary_cons, and_assoc, ih]
    cases ix <;> simp [MerkleTree.recover_snoc, hashLevel]

lemma MerkleTreeInclusionProof_looped (Leaf: F) (PathIndices: Vector F D) (Siblings: Vector F D) (k: F -> Prop):
    Semaphore.MerkleTreeInclusionProof_20_20 Leaf PathIndices Siblings k =
      merkle_tree_recover_rounds Leaf PathIndices Siblings k := by
    unfold Semaphore.MerkleTreeInclusionProof_20_20
    simp [merkle_tree_recover_rounds]
    rw [←Vector.ofFn_get (v := PathIndices)]
    rw [←Vector.ofFn_get (v := Siblings)]
    rfl

lemma MerkleTreeInclusionProof_20_20_uncps
  {Leaf : F}
  {PathIndices : Vector Bool D}
  {Siblings : Vector F D}
  {k : F -> Prop} :
    Semaphore.MerkleTreeInclusionProof_20_20 Leaf (Vector.map Bool.toZMod PathIndices) Siblings k ↔
    k (MerkleTree.recover poseidon₂ PathIndices.reverse Siblings.reverse Leaf) := by
    simp [MerkleTreeInclusionProof_looped, merkle_tree_recover_rounds_uncps]

abbrev secret (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
  poseidon₂ vec![IdentityNullifier, IdentityTrapdoor]

abbrev identity_commitment (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
  poseidon₁ vec![(secret IdentityNullifier IdentityTrapdoor)]

abbrev nullifier_hash (ExternalNullifier: F) (IdentityNullifier: F) : F :=
  poseidon₂ vec![ExternalNullifier, IdentityNullifier]

def circuit_sem (IdentityNullifier IdentityTrapdoor ExternalNullifier NullifierHash Root: F) (Path: Vector Bool D) (Proof: Vector F D): Prop :=
    NullifierHash = nullifier_hash ExternalNullifier IdentityNullifier ∧
    MerkleTree.recover poseidon₂ Path.reverse Proof.reverse (identity_commitment IdentityNullifier IdentityTrapdoor) = Root

theorem circuit_semantics_bool {IdentityNullifier IdentityTrapdoor SignalHash ExternalNullifier NullifierHash Root: F} {Path: Vector Bool D} {Proof: Vector F D}:
    Semaphore.circuit IdentityNullifier IdentityTrapdoor (Vector.map Bool.toZMod Path) Proof SignalHash ExternalNullifier NullifierHash Root ↔
    circuit_sem IdentityNullifier IdentityTrapdoor ExternalNullifier NullifierHash Root Path Proof := by
    simp [
      circuit_sem,
      Semaphore.circuit,
      Poseidon2_uncps,
      Poseidon1_uncps,
      MerkleTreeInclusionProof_20_20_uncps,
      Gates.eq,
      nullifier_hash
    ]
    intro
    apply Iff.intro
    repeat (
      intro h; simp [h]
    )

theorem circuit_semantics {IdentityNullifier IdentityTrapdoor SignalHash ExternalNullifier NullifierHash Root: F} {Path Proof: Vector F D}:
    (is_vector_binary Path ∧ ∃x : Vector Bool D, Path = x.map Bool.toZMod) →
    (Semaphore.circuit IdentityNullifier IdentityTrapdoor (Vector.map Bool.toZMod x) Proof SignalHash ExternalNullifier NullifierHash Root ↔
    circuit_sem IdentityNullifier IdentityTrapdoor ExternalNullifier NullifierHash Root x Proof) := by
      intro
      apply circuit_semantics_bool
