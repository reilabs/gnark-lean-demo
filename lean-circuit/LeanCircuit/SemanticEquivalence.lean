import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle

import LeanCircuit
import LeanCircuit.Poseidon.Spec
import LeanCircuit.Poseidon.Correctness

open Semaphore (F Order)

variable [Fact (Nat.Prime Order)]

/-- Number of levels in Merkle Tree -/
abbrev D := 20

-- Start of misc lemmas

/-!
These lemmas are used in simp commands to convert between `Vector Dir depth` and
`Vector F depth`. These lemmas rely on the Order of F (i.e. ZMod) being hardcoded
which is why they are not kept in the library reilabs/proven-zk.
-/

/-!
embed_dir converts from `Dir` to `F`. Can't call `Dir.toZMod` directly because
dir_embed_recover relies on knowing the value of the Order
-/
def embed_dir : Dir -> F
  | x => Dir.toZMod x

/-!
embed_dir_vector converts from `Vector Dir depth` to `Vector F depth`
-/
def embed_dir_vector {depth} (ix: Vector Dir depth) : Vector F depth :=
  Vector.map embed_dir ix

/-!
dir_embed_recover proves that converting from `Dir` to `ZMod` and back to `Dir`,
returns a value equal to the argument d
-/
lemma dir_embed_recover {d : Dir} : Dir.nat_to_dir (embed_dir d).val = d := by
  cases d <;> rfl

/-!
dir_embed_recover_vector applies the lemma `dir_embed_recover` to a whole vector
of length depth
-/
@[simp]
lemma dir_embed_recover_vector {depth} (ix: Vector Dir depth) :
  Dir.create_dir_vec (embed_dir_vector ix) = ix := by
  simp [Dir.create_dir_vec, embed_dir_vector, dir_embed_recover]
  apply Vector.eq
  simp

/-!
embed_dir_vector_reverse proves that `embed_dir_vector` and `Vector.reverse`
are associative i.e. if they are applied to a `Vector Dir`, the order
of the operations doesn't matter, the result is the same.
-/
@[simp]
lemma embed_dir_vector_reverse {depth} (ix : Vector Dir depth) :
  embed_dir_vector (Vector.reverse ix) = Vector.reverse (embed_dir_vector ix) := by
  simp [embed_dir_vector]
  apply Vector.eq
  simp [Vector.toList_reverse, List.map_reverse]

/-!
embed_dir_vector_is_binary proves that Vector Dir are binary vectors when converted from
`Vector Dir depth` to `Vector F depth` because `Dir` can only be 0 | 1.
-/
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

-- End of misc lemmas

/-!
The following proofs are needed to verify that Semaphore.circuit is equal to circuit_sem as shown
in the theorem circuit_semantics.
First, we prove that the hash circuit (Poseidon) is correct in lemmas Poseidon1_uncps and Poseidon2_uncps
Second, we prove that the parent hash of the Merkle tree is computed correctly in MerkleTreeRecoverRound_uncps.
Third, by repeatedly applying Semaphore.MerkleTreeRecoverRound, we prove that the computed root is correct
in lemma MerkleTreeInclusionProof_20_20_uncps
Finally, combining all the proofs, we show that Semaphore.circuit is a correct implementation of the Semaphore
circuit as per [specification](https://github.com/semaphore-protocol/semaphore/tree/main/packages/circuits).
Link to protocol [glossary](https://semaphore.appliedzkp.org/docs/glossary).
-/
def poseidon₁ : Hash F 1 := fun a => (Poseidon.perm Constants.x5_254_2 vec![0, a.get 0]).get 0

lemma Poseidon1_uncps (a : F) (k : F -> Prop) : Semaphore.Poseidon1 a k ↔ k (poseidon₁ vec![a]) := by
    simp [Semaphore.Poseidon1, poseidon₁, poseidon_2_correct, getElem]

def poseidon₂ : Hash F 2 := fun a => (Poseidon.perm Constants.x5_254_3 vec![0, a.get 0, a.get 1]).get 0

lemma Poseidon2_uncps (a b : F) (k : F -> Prop) : Semaphore.Poseidon2 a b k ↔ k (poseidon₂ vec![a, b]) := by
    simp [Semaphore.Poseidon2, poseidon₂, poseidon_3_correct, getElem]
    rfl

lemma MerkleTreeRecoverRound_uncps {dir hash sibling : F} {k : F -> Prop}:
    Semaphore.MerkleTreeRecoverRound dir hash sibling k ↔
    is_bit dir ∧ k (match Dir.nat_to_dir dir.val with
    | Dir.left => poseidon₂ vec![hash, sibling]
    | Dir.right => poseidon₂ vec![sibling, hash]) := by
    simp [Semaphore.MerkleTreeRecoverRound, Gates.is_bool]
    intro hb
    rw [Poseidon2_uncps, Poseidon2_uncps]
    cases hb <;> {
        simp [*, Gates.select, Gates.is_bool, Dir.nat_to_dir]
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
  is_vector_binary PathIndices ∧ k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec PathIndices) Siblings Leaf) := by
  induction PathIndices, Siblings using Vector.inductionOn₂ generalizing Leaf with
  | nil =>
    simp [is_vector_binary]
    rfl
  | @cons n ix sib ixes sibs ih =>
    simp [MerkleTree.recover_tail_reverse_equals_recover, MerkleTree.recover_tail, merkle_tree_recover_rounds]
    simp [MerkleTreeRecoverRound_uncps, is_vector_binary_cons, and_assoc, ih]
    intros
    rfl

lemma MerkleTreeInclusionProof_looped (Leaf: F) (PathIndices: Vector F D) (Siblings: Vector F D) (k: F -> Prop):
    Semaphore.MerkleTreeInclusionProof_20_20 Leaf PathIndices Siblings k =
      merkle_tree_recover_rounds Leaf PathIndices Siblings k := by
    unfold Semaphore.MerkleTreeInclusionProof_20_20
    simp [merkle_tree_recover_rounds]
    simp [merkle_tree_recover_rounds]
    rw [←Vector.ofFn_get (v := PathIndices)]
    rw [←Vector.ofFn_get (v := Siblings)]
    rfl

lemma MerkleTreeInclusionProof_20_20_uncps {Leaf : F} {PathIndices Siblings : Vector F D} {k : F -> Prop}:
    Semaphore.MerkleTreeInclusionProof_20_20 Leaf PathIndices Siblings k ↔
    is_vector_binary PathIndices ∧ k (MerkleTree.recover_tail poseidon₂ (Dir.create_dir_vec PathIndices) Siblings Leaf) := by
    simp [MerkleTreeInclusionProof_looped, merkle_tree_recover_rounds_uncps]

/-!
secret is the Poseidon hash of `IdentityNullifier` and `IdentityTrapdoor`
as per [spec](https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom#L6)
-/
abbrev secret (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
  poseidon₂ vec![IdentityNullifier, IdentityTrapdoor]

/-!
identity_commitment is the Poseidon hash of `secret`
as per [spec](https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom#L20)
-/
abbrev identity_commitment (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
  poseidon₁ vec![(secret IdentityNullifier IdentityTrapdoor)]

/-!
nullifier_hash is the Poseidon hash of `ExternalNullifier` and `IdentityNullifier`
as per [spec](https://github.com/semaphore-protocol/semaphore/blob/main/packages/circuits/semaphore.circom#L32)
-/
abbrev nullifier_hash (ExternalNullifier: F) (IdentityNullifier: F) : F :=
  poseidon₂ vec![ExternalNullifier, IdentityNullifier]

/-- circuit_sem is an implementation of the Semaphore protocol -/
def circuit_sem (IdentityNullifier IdentityTrapdoor ExternalNullifier NullifierHash Root: F) (Path Proof: Vector F D): Prop :=
    NullifierHash = nullifier_hash ExternalNullifier IdentityNullifier ∧
    is_vector_binary Path ∧
    MerkleTree.recover poseidon₂ (Dir.create_dir_vec Path).reverse Proof.reverse (identity_commitment IdentityNullifier IdentityTrapdoor) = Root

/-- circuit_semantics proves that the Semaphore circuit exported from gnark-lean-extractor is equivalent to circuit_sem -/
theorem circuit_semantics {IdentityNullifier IdentityTrapdoor SignalHash ExternalNullifier NullifierHash Root: F} {Path Proof: Vector F D}:
    Semaphore.circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExternalNullifier NullifierHash Root ↔
    circuit_sem IdentityNullifier IdentityTrapdoor ExternalNullifier NullifierHash Root Path Proof := by
    simp [
      circuit_sem,
      Semaphore.circuit,
      Poseidon2_uncps,
      Poseidon1_uncps,
      MerkleTreeInclusionProof_20_20_uncps,
      Gates.eq,
      nullifier_hash,
      Dir.create_dir_vec,
      ←MerkleTree.recover_tail_reverse_equals_recover
    ]
    apply Iff.intro
    case mp =>
      intros
      casesm* (_ ∧ _)
      rw [←Vector.ofFn_get (v := Path)]
      rw [←Vector.ofFn_get (v := Proof)]
      subst_vars
      apply And.intro
      {rfl}
      apply And.intro
      {assumption}
      {rfl}
    case mpr =>
      intro h
      cases h; rename_i h₁ h₂
      cases h₂; rename_i h₂ h₃
      rw [←Vector.ofFn_get (v := Path)] at h₂
      rw [←Vector.ofFn_get (v := Path)] at h₃
      rw [←Vector.ofFn_get (v := Proof)] at h₃
      subst_vars
      apply And.intro
      {rfl}
      apply And.intro
      assumption
      {rfl}