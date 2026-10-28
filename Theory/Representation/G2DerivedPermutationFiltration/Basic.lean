module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.Representation.FactorDegreeFiltration
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# The binary derived G₂ action on unipotent cosets

The carrier consists of the 189 left cosets of the full six-root unipotent
subgroup of the split-octonion group G₂(2). The acting group is literally its
commutator subgroup. The hexagon sign character expresses every ambient
element as a derived-group element times a unipotent element, so this
restricted action is transitive. Its point stabilizer is the intersection
with the unipotent subgroup, a two-group of order 32.

These are the action and stabilizer inputs for the permutation-filtration
argument in Aschbacher–Smith G.7.2(3), printed p.348 (PDF p.359). No claim
about composition factors is made here. The concrete group and sign facts
come from the attributed ATLAS ports imported above; no ATLAS code is copied.
-/

@[expose] public section

open Atlas.G2
namespace G2DerivedPermutationFiltration
abbrev FullGroup := Atlas.G2.Model (ZMod 2)
abbrev Group := commutator FullGroup
abbrev Flag := FullGroup ⧸ (unipotent (K := ZMod 2))
noncomputable instance : Fintype Flag := Fintype.ofFinite Flag

def flagPerm : Group →* Equiv.Perm Flag :=
  (MulAction.toPermHom FullGroup Flag).comp Group.subtype

def baseFlag : Flag := QuotientGroup.mk (1 : FullGroup)
def flagStabilizer : Subgroup Group := (unipotent (K := ZMod 2)).comap Group.subtype

theorem flagStabilizer_isPGroup : IsPGroup 2 flagStabilizer :=
  (IsPGroup.of_card (show Nat.card (unipotent (K := ZMod 2)) = 2^6 from
    BinaryParabolicPair.card_unipotent_binary)).comap_subtype

theorem mem_flagStabilizer_iff (g : Group) : g ∈ flagStabilizer ↔ flagPerm g baseFlag = baseFlag := by
  change g.val ∈ unipotent ↔
    QuotientGroup.mk (g.val * 1) = (QuotientGroup.mk 1 : Flag)
  rw [mul_one, QuotientGroup.eq]
  simp

theorem unipotent_supplement (g : FullGroup) :
    ∃ (h : Group) (b : unipotent (K := ZMod 2)), g = h.val * b.val := by
  have hmem (x : FullGroup) (hx : Binary.lineSign x = 1) : x ∈ Group := by
    rw [show Group = BinaryException.H from BinaryParabolicPair.commutator_eq_longRootClosure,
      ← BinaryException.lineSign_kernel]
    exact hx
  rcases Int.units_eq_one_or (Binary.lineSign g) with h | h
  · exact ⟨⟨g, hmem g h⟩, 1, (mul_one g).symm⟩
  · have hb : rootF (1 : ZMod 2) ∈ unipotent :=
      BinaryParabolicPair.shortRoot_mem_unipotent
    refine ⟨⟨g * (rootF 1)⁻¹, hmem _ ?_⟩, ⟨rootF 1, hb⟩, ?_⟩
    · rw [map_mul, map_inv, h, Binary.lineSign_rootF_one]
      exact mul_inv_cancel _
    · exact (inv_mul_cancel_right g (rootF 1)).symm

theorem flagTransitive (x : Flag) : ∃ g : Group, flagPerm g baseFlag = x := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨h, b, rfl⟩ := unipotent_supplement g
    refine ⟨h, ?_⟩
    change QuotientGroup.mk (h.val * 1) = (QuotientGroup.mk (h.val * b.val) : Flag)
    rw [mul_one, QuotientGroup.eq]
    simp [b.property]

theorem card_flags : Fintype.card Flag = 189 := by
  rw [← Nat.card_eq_fintype_card]
  exact BinaryParabolicPair.index_unipotent_binary

instance : MulAction.IsPretransitive Group Flag :=
  (MulAction.isPretransitive_iff_base baseFlag).mpr flagTransitive

theorem action_flagStabilizer : MulAction.stabilizer Group baseFlag = flagStabilizer := by
  ext g
  exact (mem_flagStabilizer_iff g).symm

theorem card_flagStabilizer : Nat.card flagStabilizer = 32 := by
  classical
  let := Fintype.ofFinite Group
  let := Fintype.ofFinite (MulAction.orbit Group baseFlag)
  let := Fintype.ofFinite (MulAction.stabilizer Group baseFlag)
  have hc := MulAction.card_orbit_mul_card_stabilizer_eq_card_group Group baseFlag
  simp only [← Nat.card_eq_fintype_card, action_flagStabilizer,
    MulAction.orbit_eq_univ, Nat.card_univ] at hc
  have hg : Nat.card Group = 6048 := by
    rw [show Group = BinaryException.H from BinaryParabolicPair.commutator_eq_longRootClosure]
    exact BinaryException.card_H
  rw [hg, Nat.card_eq_fintype_card (α := Flag), card_flags] at hc
  omega

/-- The actual binary flag permutation representation. -/
def flagRepresentation : Representation (ZMod 2) Group (BinaryPermutation.Full Flag) :=
  (BinaryPermutation.representation Flag).comp flagPerm

/-- Degrees sufficient for excluding faithful irreducibles of degree seven or eight. -/
def allowedDegrees : Set ℕ := {d | d = 1 ∨ d = 6 ∨ 8 < d}

end G2DerivedPermutationFiltration
