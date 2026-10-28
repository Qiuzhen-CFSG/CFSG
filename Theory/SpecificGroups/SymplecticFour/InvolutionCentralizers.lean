module

public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.Geometry
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Relative centralizers of symplectic involutions

The moved-space stabilizer constructs a genuine proper parabolic containing
an involution centralizer. Restricting that centralizer to this parabolic
preserves both its ambient image and its embedded two-residual. For the
derived group, the fixed subgroup of actual ambient conjugation is its
intersection with the ambient centralizer. The parabolic is intersected
with the derived group as well; that intersection remains proper, even
in the binary case.

These are the geometric and residual identifications for Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 16.1.4(1), printed p.1171.
The separate c₂ centralizer calculation needed for clause (2), and the
root-type conjugacy equivalence in Definition E.2.6, remain additional
matrix calculations. The results below do not assume either calculation.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
open InvolutionTypes
variable {F : Type*} [Field F]

private theorem relative_residual_map {G : Type*} [Group G]
    (p : ℕ) (C P : Subgroup G) (h : C ≤ P) :
    ((pResidual p (C.subgroupOf P)).map (C.subgroupOf P).subtype).map P.subtype =
      (pResidual p C).map C.subtype := by
  let e := subgroupOfEquivOfLe h
  calc
    _ = ((pResidual p (C.subgroupOf P)).map e.toMonoidHom).map C.subtype := by
      rw [map_map, map_map]
      rfl
    _ = _ := by rw [map_pResidual]

/-- Actual conjugation on the derived carrier has the relative ambient
centralizer as its fixed subgroup. No replacement by full Sp₄ is made. -/
theorem derived_fixed_eq (g : Sp F) :
    (MulAut.conjNormal (H := commutator (Sp F)) g).fixedSubgroup =
      (centralizer ({g} : Set (Sp F))).subgroupOf (commutator (Sp F)) := by
  ext x
  rw [MulAut.mem_fixedSubgroup, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
  rw [← Subtype.coe_inj, MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
  exact eq_comm

/-- Passing to an overgroup of the centralizer does not change its ambient image. -/
theorem centralizer_relative_map (g : Sp F) (P : Subgroup (Sp F))
    (hP : centralizer ({g} : Set (Sp F)) ≤ P) :
    ((centralizer ({g} : Set (Sp F))).subgroupOf P).map P.subtype =
      centralizer ({g} : Set (Sp F)) := map_subgroupOf_eq_of_le hP

/-- The two-residual comparison is made in the common ambient group. -/
theorem centralizer_twoResidual_relative (g : Sp F) (P : Subgroup (Sp F))
    (hP : centralizer ({g} : Set (Sp F)) ≤ P) :
    ((pResidual 2 ((centralizer ({g} : Set (Sp F))).subgroupOf P)).map
      ((centralizer ({g} : Set (Sp F))).subgroupOf P).subtype).map P.subtype =
    (pResidual 2 (centralizer ({g} : Set (Sp F)))).map
      (centralizer ({g} : Set (Sp F))).subtype :=
  relative_residual_map 2 _ P hP

/-- The fixed group in Sp₄′ is exactly the centralizer in the intersection
of Sp₄′ with a containing ambient parabolic. -/
theorem derived_fixed_map_eq_inter_parabolic (g : Sp F) (P : Subgroup (Sp F))
    (hP : centralizer ({g} : Set (Sp F)) ≤ P) :
    (MulAut.conjNormal (H := commutator (Sp F)) g).fixedSubgroup.map
      (commutator (Sp F)).subtype =
      (P ⊓ commutator (Sp F)) ⊓ centralizer ({g} : Set (Sp F)) := by
  rw [derived_fixed_eq, subgroupOf_map_subtype]
  apply le_antisymm
  · rintro x ⟨hxC, hxD⟩
    exact ⟨⟨hP hxC, hxD⟩, hxC⟩
  · rintro x ⟨⟨_, hxD⟩, hxC⟩
    exact ⟨hxC, hxD⟩

/-- The derived fixed group and its restriction to the actual parabolic
intersection have the same embedded two-residual in Sp₄′. -/
theorem derived_fixed_twoResidual_relative (g : Sp F) (P : Subgroup (Sp F))
    (hP : centralizer ({g} : Set (Sp F)) ≤ P) :
    let D := commutator (Sp F)
    let C := (MulAut.conjNormal (H := D) g).fixedSubgroup
    let Q := P.subgroupOf D
    ((pResidual 2 (C.subgroupOf Q)).map (C.subgroupOf Q).subtype).map Q.subtype =
      (pResidual 2 C).map C.subtype := by
  apply relative_residual_map
  rw [derived_fixed_eq]
  exact fun _ hx => hP hx

private theorem residual_eq_bot_of_pGroup {G : Type*} [Group G]
    (p : ℕ) (h : IsPGroup p G) : pResidual p G = ⊥ :=
  le_antisymm (sInf_le ⟨inferInstance, h.to_quotient ⊥⟩) bot_le

/-- The residual conclusion follows once the actual centralizer is a two-group.
The c₂ matrix calculation must supply this hypothesis. -/
theorem centralizer_twoResidual_eq_bot_of_isPGroup (g : Sp F)
    (h : IsPGroup 2 (centralizer ({g} : Set (Sp F)))) :
    pResidual 2 (centralizer ({g} : Set (Sp F))) = ⊥ :=
  residual_eq_bot_of_pGroup 2 h

/-- Restriction to the genuine derived carrier preserves the two-group property. -/
theorem derived_fixed_isPGroup_of_centralizer (g : Sp F)
    (h : IsPGroup 2 (centralizer ({g} : Set (Sp F)))) :
    IsPGroup 2 (MulAut.conjNormal (H := commutator (Sp F)) g).fixedSubgroup := by
  rw [derived_fixed_eq]
  exact h.comap_subtype

/-- The c₂ residual conclusion also transfers to the actual derived action,
conditional on the ambient centralizer calculation. -/
theorem derived_fixed_twoResidual_eq_bot_of_centralizer (g : Sp F)
    (h : IsPGroup 2 (centralizer ({g} : Set (Sp F)))) :
    pResidual 2 (MulAut.conjNormal (H := commutator (Sp F)) g).fixedSubgroup = ⊥ :=
  residual_eq_bot_of_pGroup 2 (derived_fixed_isPGroup_of_centralizer g h)

variable [CharP F 2]

/-- Every nonidentity involution centralizer lies in a genuine proper
parabolic containing the involution itself. -/
theorem involution_centralizer_parabolic (g : Sp F) (hg : orderOf g = 2) :
    ∃ P : Subgroup (Sp F), IsParabolic P ∧ P ≠ ⊤ ∧ g ∈ P ∧
      centralizer ({g} : Set (Sp F)) ≤ P := by
  let P := stabilizer (movedSpace g)
  have hp := movedSpace_stabilizer_parabolic g hg
  have hc := centralizer_le_movedSpace_stabilizer g
  exact ⟨P, hp, parabolic_ne_top P hp,
    hc (mem_centralizer_singleton_iff.mpr rfl), hc⟩

/-- The parabolic and both centralizer/residual equalities for an actual root
matrix conjugate. No Suzuki-type hypothesis replaces the root element. -/
theorem root_centralizer_parabolic (g : Sp F) (hg : IsRootElement g) :
    ∃ P : Subgroup (Sp F), IsParabolic P ∧ P ≠ ⊤ ∧ g ∈ P ∧
      centralizer ({g} : Set (Sp F)) ≤ P ∧
      ((centralizer ({g} : Set (Sp F))).subgroupOf P).map P.subtype =
        centralizer ({g} : Set (Sp F)) ∧
      ((pResidual 2 ((centralizer ({g} : Set (Sp F))).subgroupOf P)).map
        ((centralizer ({g} : Set (Sp F))).subgroupOf P).subtype).map P.subtype =
      (pResidual 2 (centralizer ({g} : Set (Sp F)))).map
        (centralizer ({g} : Set (Sp F))).subtype := by
  obtain ⟨P, hp, hne, hgP, hc⟩ := involution_centralizer_parabolic g (root_orderOf g hg)
  exact ⟨P, hp, hne, hgP, hc, centralizer_relative_map g P hc,
    centralizer_twoResidual_relative g P hc⟩

/-- The derived fixed group is contained in a proper intersection with an
actual ambient parabolic, including when the field has order two. -/
theorem involution_derived_parabolic (g : Sp F) (hg : orderOf g = 2) :
    ∃ P : Subgroup (Sp F), IsParabolic P ∧ P ≠ ⊤ ∧ g ∈ P ∧
      centralizer ({g} : Set (Sp F)) ≤ P ∧
      P.subgroupOf (commutator (Sp F)) ≠ ⊤ ∧
      (MulAut.conjNormal (H := commutator (Sp F)) g).fixedSubgroup ≤
        P.subgroupOf (commutator (Sp F)) := by
  obtain ⟨P, hp, hne, hgP, hc⟩ := involution_centralizer_parabolic g hg
  refine ⟨P, hp, hne, hgP, hc, derived_parabolic_ne_top P hp, ?_⟩
  rw [derived_fixed_eq]
  exact fun _ hx => hc hx

/-- The root case of the genuine derived-action statement. The preceding
relative residual theorem applies to this same ambient parabolic. -/
theorem root_derived_parabolic (g : Sp F) (hg : IsRootElement g) :
    ∃ P : Subgroup (Sp F), IsParabolic P ∧ P ≠ ⊤ ∧ g ∈ P ∧
      centralizer ({g} : Set (Sp F)) ≤ P ∧
      P.subgroupOf (commutator (Sp F)) ≠ ⊤ ∧
      (MulAut.conjNormal (H := commutator (Sp F)) g).fixedSubgroup ≤
        P.subgroupOf (commutator (Sp F)) :=
  involution_derived_parabolic g (root_orderOf g hg)

end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
