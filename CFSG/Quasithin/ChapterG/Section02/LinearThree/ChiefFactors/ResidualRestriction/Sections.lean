module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.Coordinates
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.LocalNormalizerUniqueness
/-!
# Restricting the literal G.2.5 sections to L₁

The core centralizes V and normalizes L, and therefore normalizes the
characteristic two-residual of N_L(V₁). Commutators with L₁ then show that
any part of a core layer lost on intersection with L₁ is central.
The intersection projections retain the actual denominators and give
isomorphisms onto their images in S₃/S₂ and S/S₃. All normality assertions
are relative to their stated carriers.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
G.2.5(4–8), printed pp.335–336.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  (d : Hypothesis D F n g h)

omit [Finite G] in
private theorem residual_le : D.L₁ ≤ D.L ⊓ D.G₁ := map_subtype_le _

include d in
theorem core_normalizes_residual (hUT : D.U ≤ D.T) (hILU : I D g h = D.L ⊔ D.U) :
    S D g h ≤ normalizer (D.L₁ : Set G) := by
  have hLI : D.L ≤ I D g h := hILU ▸ le_sup_left
  have hc : S D g h ≤ centralizer (D.V : Set G) :=
    le_centralizer_iff.mp ((d.central_first hUT hLI).trans inf_le_right)
  have hp : S D g h ≤ normalizer (D.V₁ : Set G) :=
    (hc.trans (centralizer_le d.setup.point_le)).trans (centralizer_le_normalizer _)
  have hL : I D g h ≤ normalizer (D.L : Set G) := by
    rw [hILU]
    exact sup_le D.L.le_normalizer (hUT.trans d.setup.T_normalizes_L)
  have hN : S D g h ≤ normalizer ((D.L ⊓ D.G₁ : Subgroup G) : Set G) :=
    (le_inf ((pCoreIn_le 2 _).trans hL) (hp.trans D.G₁.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact hN.trans (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

omit [Finite G] in
theorem core_intersection_normal (hILU : I D g h = D.L ⊔ D.U) :
    ((D.L₁ ⊓ S D g h).subgroupOf D.L₁).Normal := by
  have hLI : D.L ≤ I D g h := hILU ▸ le_sup_left
  apply normal_subgroupOf_of_le_normalizer
  apply (le_inf D.L₁.le_normalizer ?_).trans inf_normalizer_le_normalizer_inf
  exact ((residual_le (D := D)).trans inf_le_left).trans
    (hLI.trans (I_normalizes_core D g h))

omit [Finite G] in
theorem layer_intersection_normal (A : Subgroup G)
    (hA : D.L₁ ≤ normalizer (A : Set G)) :
    ((D.L₁ ⊓ A).subgroupOf D.L₁).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((le_inf D.L₁.le_normalizer hA).trans inf_normalizer_le_normalizer_inf)

include d in
/-- A section omitted by intersection is central for the actual local actor. -/
theorem lost_section_commutator (hUT : D.U ≤ D.T) (hILU : I D g h = D.L ⊔ D.U)
    (A B : Subgroup G) (hAS : A ≤ S D g h)
    (hA : D.L₁ ≤ normalizer (A : Set G)) :
    ⁅D.L₁, A⁆ ≤ B ⊔ (D.L₁ ⊓ A) := by
  apply le_trans _ le_sup_right
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp
      (hAS.trans (core_normalizes_residual d hUT hILU)))
    (le_normalizer_iff_commutator_le_right.mp hA)

section Quotients
variable (J A B : Subgroup G) [(B.subgroupOf A).Normal]

/-- The literal quotient map on J∩A; no denominator containment is invented. -/
def intersectionProjection : (J ⊓ A : Subgroup G) →* (A ⧸ B.subgroupOf A) :=
  (QuotientGroup.mk' (B.subgroupOf A)).comp (inclusion inf_le_right)

omit [Finite G] in
theorem intersectionProjection_kernel :
    (intersectionProjection J A B).ker = B.subgroupOf (J ⊓ A) := by
  ext x
  exact QuotientGroup.eq_one_iff (inclusion inf_le_right x)

instance intersectionDenominator_normal : (B.subgroupOf (J ⊓ A)).Normal := by
  rw [← intersectionProjection_kernel J A B]
  infer_instance

/-- The genuine image section, with its original quotient map. -/
noncomputable def intersectionSectionEquiv :
    ((J ⊓ A : Subgroup G) ⧸ B.subgroupOf (J ⊓ A)) ≃*
      (intersectionProjection J A B).range :=
  (QuotientGroup.quotientMulEquivOfEq (intersectionProjection_kernel J A B).symm).trans
    (QuotientGroup.quotientKerEquivRange (intersectionProjection J A B))

end Quotients

variable [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal]

/-- The section of the dual layer which belongs to L₁. -/
noncomputable def lowerIntersectionEquiv :
    ((D.L₁ ⊓ S₃ D g h : Subgroup G) ⧸ (S₂ D g h).subgroupOf (D.L₁ ⊓ S₃ D g h)) ≃*
      (intersectionProjection D.L₁ (S₃ D g h) (S₂ D g h)).range :=
  intersectionSectionEquiv D.L₁ _ _

/-- The section of the natural upper layer which belongs to L₁. -/
noncomputable def upperIntersectionEquiv :
    ((D.L₁ ⊓ S D g h : Subgroup G) ⧸ (S₃ D g h).subgroupOf (D.L₁ ⊓ S D g h)) ≃*
      (intersectionProjection D.L₁ (S D g h) (S₃ D g h)).range :=
  intersectionSectionEquiv D.L₁ _ _

/-- Relative normality of each of the three proper source layers after
intersecting with the actual local residual. -/
theorem marked_intersections_normal (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    {hLI : D.L ≤ I D g h} {r s : ℕ} (c : MarkedLayers d hLI r s) :
    ((D.L₁ ⊓ D.V).subgroupOf D.L₁).Normal ∧
    ((D.L₁ ⊓ S₂ D g h).subgroupOf D.L₁).Normal ∧
    ((D.L₁ ⊓ S₃ D g h).subgroupOf D.L₁).Normal := by
  have hlocal : D.L₁ ≤ D.L := (residual_le (D := D)).trans inf_le_left
  have hEI : S₂ D g h ≤ I D g h :=
    inf_le_left.trans (inf_le_left.trans (le_sup_left.trans le_sup_left))
  have hEN : I D g h ≤ normalizer (S₂ D g h : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hEI).mp (d.intersection hUT hf).2.2.1
  exact ⟨layer_intersection_normal _ (hlocal.trans (normalizes_of_span D d.span_eq)),
    layer_intersection_normal _ (hlocal.trans (hLI.trans hEN)),
    layer_intersection_normal _ (hlocal.trans c.lower_normalizes)⟩

/-- The quotients of the lower and upper source sections omitted by
intersection carry trivial local action. -/
theorem lost_lower_upper_central (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) {hLI : D.L ≤ I D g h} {r s : ℕ}
    (c : MarkedLayers d hLI r s) (hS₃ : S₃ D g h ≤ S D g h) :
    ⁅D.L₁, S₃ D g h⁆ ≤ S₂ D g h ⊔ (D.L₁ ⊓ S₃ D g h) ∧
    ⁅D.L₁, S D g h⁆ ≤ S₃ D g h ⊔ (D.L₁ ⊓ S D g h) := by
  have hlocal : D.L₁ ≤ D.L := (residual_le (D := D)).trans inf_le_left
  exact ⟨lost_section_commutator d hUT hILU _ _ hS₃ (hlocal.trans c.lower_normalizes),
    lost_section_commutator d hUT hILU _ _ le_rfl
      (hlocal.trans (hLI.trans (I_normalizes_core D g h)))⟩
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
