import ProvenZk.Binary
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.Ext.Vector

import LeanCircuit
import LeanCircuit.Poseidon.Spec
import LeanCircuit.Poseidon.Correctness

open Semaphore (F Order)

variable [Fact (Nat.Prime Order)]

abbrev D := 20

def mcreate_dir_vec {n} {depth} (ix: Vector (ZMod n) depth) : Option (Vector Dir depth) :=
  Vector.mmap (fun x => Dir.nat_to_dir x.val) ix

def mcreate_dir_vec_cons{n} {depth} {ix: (ZMod n)} {ixes: Vector (ZMod n) depth} :
  (∃x, mcreate_dir_vec (ix ::ᵥ ixes) = some x) ↔ (∃x, (Dir.nat_to_dir ix.val) = some x ∧ ∃y, mcreate_dir_vec ixes = some y) := by
  unfold mcreate_dir_vec
  apply Iff.intro
  case mp => {
    intro
    rename_i h
    simp [Vector.mmap_cons] at *
    simp
    simp at h
    apply And.intro
    case left => {
      cases h
      rename_i h
      -- How do I get out of the do-notation?
      sorry
    }
    case right => {
      sorry
    }
  }
  case mpr => {
    sorry
  }

-- def is_vector_binary' {d n} (x : Vector (ZMod n) d) : Prop :=
--   Vector.foldr (fun a r => is_bit a ∧ r) True x

-- theorem dir_left {n : Nat} {a : ZMod n} : Dir.nat_to_dir (ZMod.val a) = some Dir.left ↔ (ZMod.val a) = 0 := by sorry
-- theorem dir_right {n : Nat} {a : ZMod n} : Dir.nat_to_dir (ZMod.val a) = some Dir.right ↔ (ZMod.val a) = 1 := by sorry

def dir_some_is_bit {n : Nat} {a : ZMod n} :
  (∃x, Dir.nat_to_dir (ZMod.val a) = some x) ↔ is_bit a := by
  apply Iff.intro
  case mp => {
    sorry
  }
  case mpr => {
    sorry
  }

def embed_dir : Dir -> F
  | x => Dir.toZMod x

def embed_dir_vector {depth} (ix: Vector Dir depth) : Vector F depth :=
  Vector.map embed_dir ix

lemma dir_embed_recover {d : Dir} : Dir.nat_to_dir (embed_dir d).val = d := by
  cases d <;> rfl

def vec_dir_to_option {depth} (ix: Vector Dir depth) : Vector (Option Dir) depth := Vector.map (fun x => some x) ix

@[simp]
lemma dir_embed_recover_vector {depth} (ix: Vector Dir depth) :
  Dir.create_dir_vec (embed_dir_vector ix) = vec_dir_to_option ix := by
  unfold vec_dir_to_option
  simp [Dir.create_dir_vec, embed_dir_vector, dir_embed_recover]

@[simp]
lemma embed_dir_vector_reverse {depth} (ix : Vector Dir depth) :
  embed_dir_vector ix.reverse = (embed_dir_vector ix).reverse := by
  simp [embed_dir_vector]
  apply Vector.eq
  simp [Vector.toList_reverse, List.map_reverse]

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

def MerkleTreeRecoverHash (dir hash sibling: F) : Option F :=
  match p: Dir.nat_to_dir dir.val with
    | Dir.left => some (poseidon₂ vec![hash, sibling])
    | Dir.right => some (poseidon₂ vec![sibling, hash])
    | none => none

lemma MerkleTreeRecoverHash_0 (hash sibling: F) :
  MerkleTreeRecoverHash 0 hash sibling = some (poseidon₂ vec![hash, sibling]) := by rfl

lemma MerkleTreeRecoverHash_1 (hash sibling: F) :
  MerkleTreeRecoverHash 1 hash sibling = some (poseidon₂ vec![sibling, hash]) := by rfl

@[simp]
def MerkleTreeRecoverHash_is_some {dir hash sibling: F} :
  (is_bit dir) → (∃y, (MerkleTreeRecoverHash dir hash sibling) = some y) := by
    intros
    rename_i h
    unfold is_bit at h
    cases h
    case _ => {
      subst_vars
      simp [MerkleTreeRecoverHash_0]
    }
    case _ => {
      subst_vars
      simp [MerkleTreeRecoverHash_1]
    }

lemma MerkleTreeRecoverRound_uncps {dir hash sibling : F} {k : F -> Prop}:
    Semaphore.MerkleTreeRecoverRound dir hash sibling k ↔
    is_bit dir ∧ (∃y, (MerkleTreeRecoverHash dir hash sibling) = some y ∧ k y) := by
    simp [Semaphore.MerkleTreeRecoverRound, Gates.is_bool]
    intro hb
    rw [Poseidon2_uncps, Poseidon2_uncps]
    cases hb <;> {
        unfold MerkleTreeRecoverHash
        simp [*, Gates.select, Gates.is_bool, Dir.nat_to_dir]
        rename_i h
        subst_vars
        unfold ZMod.val
        unfold Order
        simp
    }

def merkle_tree_recover_rounds (Leaf : F) (PathIndices Siblings : Vector F n) (k : F -> Prop) : Prop :=
  match n with
  | Nat.zero => k Leaf
  | Nat.succ _ => Semaphore.MerkleTreeRecoverRound PathIndices.head Leaf Siblings.head fun next =>
    merkle_tree_recover_rounds next PathIndices.tail Siblings.tail k

@[simp]
def merkle_tree_recover_rounds_uncps_is_some
  {Leaf : F}
  {PathIndices : Vector F n}:
  is_vector_binary PathIndices ↔ (∃x, mcreate_dir_vec PathIndices = some x) := by
  intros
  induction PathIndices using Vector.inductionOn
  case h_nil => {
    unfold mcreate_dir_vec
    simp
    tauto
  }
  case h_cons ih => {
    simp [mcreate_dir_vec_cons]
    apply Iff.intro
    case mp => {
      intro
      apply And.intro
      case left => {
        rename_i h
        simp [is_vector_binary_cons] at h
        unfold is_bit at h
        cases h
        rename_i h₁ h₂
        cases h₁
        case inl => {
          subst_vars
          simp
          unfold Dir.nat_to_dir
          simp
        }
        case inr => {
          subst_vars
          unfold ZMod.val
          unfold Dir.nat_to_dir
          unfold Order
          simp
        }
      }
      case right => {
        simp [is_vector_binary_cons, and_assoc, ih] at *
        rename_i h
        cases h
        assumption
      }
    }
    case mpr => {
      intro
      simp [is_vector_binary_cons, and_assoc, ih]
      apply And.intro
      case left => {
        rename_i h
        cases h
        rename_i h₁ h₂
        simp [dir_some_is_bit] at h₁
        assumption
      }
      case right => {
        simp [is_vector_binary_cons, and_assoc, ih] at *
        rename_i h
        cases h
        assumption
      }
    }
  }

lemma merkle_tree_recover_rounds_uncps
  {Leaf : F}
  {PathIndices Siblings : Vector F n}
  {k : F -> Prop}:
  merkle_tree_recover_rounds Leaf PathIndices Siblings k ↔ is_vector_binary PathIndices ∧
  (∃x, mcreate_dir_vec PathIndices = some x ∧ k (MerkleTree.recover_tail poseidon₂ x Siblings Leaf)) := by
  induction PathIndices, Siblings using Vector.inductionOn₂ generalizing Leaf with
  | nil =>
    unfold merkle_tree_recover_rounds
    simp [is_vector_binary]
    unfold mcreate_dir_vec
    simp
    unfold MerkleTree.recover_tail
    tauto
  | @cons n ix sib ixes sibs ih =>
    simp [MerkleTree.recover_tail_reverse_equals_recover, MerkleTree.recover_tail, merkle_tree_recover_rounds]
    simp [MerkleTreeRecoverRound_uncps, is_vector_binary_cons, and_assoc, ih]
    intros
    apply Iff.intro
    case mp => {
      intro
      rename_i h
      cases h
      rename_i h
      cases h
      rename_i h
      cases h
      rename_i h
      cases h
      rename_i h
      cases h
      apply And.intro
      case left => {
        assumption
      }
      case right => {
        sorry
      }
    }
    case mpr => {
      sorry
    }

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
    Semaphore.MerkleTreeInclusionProof_20_20 Leaf PathIndices Siblings k ↔ is_vector_binary PathIndices ∧
    (∃x, mcreate_dir_vec PathIndices = some x ∧ k (MerkleTree.recover_tail poseidon₂ x Siblings Leaf)) := by
    simp [MerkleTreeInclusionProof_looped]
    simp [merkle_tree_recover_rounds_uncps]

abbrev secret (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
  poseidon₂ vec![IdentityNullifier, IdentityTrapdoor]

abbrev identity_commitment (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
  poseidon₁ vec![(secret IdentityNullifier IdentityTrapdoor)]

abbrev nullifier_hash (ExternalNullifier: F) (IdentityNullifier: F) : F :=
  poseidon₂ vec![ExternalNullifier, IdentityNullifier]

def circuit_sem (IdentityNullifier IdentityTrapdoor ExternalNullifier NullifierHash Root: F) (Path Proof: Vector F D) : Prop :=
    NullifierHash = nullifier_hash ExternalNullifier IdentityNullifier ∧
    is_vector_binary Path ∧
    (∃x, mcreate_dir_vec Path = some x ∧ MerkleTree.recover poseidon₂ x.reverse Proof.reverse (identity_commitment IdentityNullifier IdentityTrapdoor) = Root)

set_option maxHeartbeats 0
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
      {
        rename_i h₁ h₂
        cases h₂
        case intro => {
          apply Exists.intro
          case h => {
            assumption
          }
        }
      }
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
      {
        cases h₃
        case intro => {
          apply Exists.intro
          case h => {
            assumption
          }
        }
      }