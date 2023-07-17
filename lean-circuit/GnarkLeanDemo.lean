import Mathlib

import ProvenZk.Binary
import ProvenZk.Gates
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.VectorExtensions

def Order : Γäò := 21888242871839275222246405745257275088548364400416034343698204186575808495617
variable [Fact (Nat.Prime Order)]
abbrev F := ZMod Order

set_option maxHeartbeats 0
	
def DummyPoseidon1 (In: F) (k: F -> Prop): Prop :=
    Γêâgate_0, gate_0 = Gates.mul In In Γêº
    k gate_0

def DummyPoseidon2 (In_1: F) (In_2: F) (k: F -> Prop): Prop :=
    Γêâgate_0, gate_0 = Gates.mul In_1 In_2 Γêº
    k gate_0

def MerkleTreeInclusionProof_3_3 (Leaf: F) (PathIndices: Vector F 3) (Siblings: Vector F 3) (k: F -> Prop): Prop :=
    Gates.is_bool PathIndices[0] Γêº
    DummyPoseidon2 Leaf Siblings[0] fun gate_1 =>
    DummyPoseidon2 Siblings[0] Leaf fun gate_2 =>
    Γêâgate_3, Gates.select PathIndices[0] gate_2 gate_1 gate_3 Γêº
    Gates.is_bool PathIndices[1] Γêº
    DummyPoseidon2 gate_3 Siblings[1] fun gate_5 =>
    DummyPoseidon2 Siblings[1] gate_3 fun gate_6 =>
    Γêâgate_7, Gates.select PathIndices[1] gate_6 gate_5 gate_7 Γêº
    Gates.is_bool PathIndices[2] Γêº
    DummyPoseidon2 gate_7 Siblings[2] fun gate_9 =>
    DummyPoseidon2 Siblings[2] gate_7 fun gate_10 =>
    Γêâgate_11, Gates.select PathIndices[2] gate_10 gate_9 gate_11 Γêº
    k gate_11

def circuit (IdentityNullifier: F) (IdentityTrapdoor: F) (TreePathIndices: Vector F 3) (TreeSiblings: Vector F 3) (SignalHash: F) (ExternalNullifier: F) (NullifierHash: F) (MTRoot: F): Prop :=
    DummyPoseidon2 IdentityNullifier IdentityTrapdoor fun gate_0 =>
    DummyPoseidon1 gate_0 fun gate_1 =>
    DummyPoseidon2 ExternalNullifier IdentityNullifier fun gate_2 =>
    Gates.eq gate_2 NullifierHash Γêº
    MerkleTreeInclusionProof_3_3 gate_1 vec![TreePathIndices[0], TreePathIndices[1], TreePathIndices[2]] vec![TreeSiblings[0], TreeSiblings[1], TreeSiblings[2]] fun gate_4 =>
    Gates.eq gate_4 MTRoot Γêº
    Γêâ_ignored_, _ignored_ = Gates.mul SignalHash SignalHash Γêº
    True
