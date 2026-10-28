module
public import CFSG.Quasithin.Chapter3.Section01.SourceSQTKEquality
public import CFSG.Quasithin.ChapterB.Section02.Thompson.MinimalActor
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding
public import Theory.GroupAction.NormalPChiefSeries.FixedCodimension

/-!
# The original Thompson centralization in 15.1.12(4)

A literal selected subgroup `X` has symmetric-three quotient, an index-two
actor image, and its two-residual together with the Sylow subgroup generates
the ambient local group. The balanced chief-series ranks feed the Thompson
replacement theorem. Normality of `O₂(X)` supplies the required normalizer
condition, and injective transport restores the original ambient Sylow group.

The qrc consumer uses the same minimal actor and the exact module
`(conjugateSpan H V).subgroupOf H` from `SourceSQTKEquality`. Its only new
source premise is selection of `X` from the chief-action classification;
maximum order, rank balance, kernel containment and centralization are not
additional assumptions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 3.1.9 and
15.1.12(4), printed pp.576–577 and1090. The conclusion concerns `O²(H)`,
the two-residual, rather than the two-core.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The literal subgroup selected from the chief-action classification in
15.1.12(3). No Thompson centralization is part of these data. -/
structure SourceThompsonSelection (S A : Subgroup G) where
  X : Subgroup G
  actor_le : A ≤ X
  core_le : pCore 2 G ≤ (pCore 2 X).map X.subtype
  core_le_sylow : (pCore 2 X).map X.subtype ≤ S
  actor_index : ((pCore 2 X).map X.subtype).relIndex A = 2
  quotient_symmetric : Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3))
  residual_generation : (pResidual 2 X).map X.subtype ⊔ S = ⊤
  residual_commutator : (pResidual 2 X).map X.subtype =
    ⁅(pResidual 2 X).map X.subtype, A⁆

/-- The source rank equalities and the same selected actor imply Thompson
centralization. The normal action is on the literal subgroup `U`. -/
theorem thompson_centralizes_residual_of_source_selection
    (S : Sylow 2 G) (U A : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G))
    (hmin : ∀ B ∈ elementaryAbelianMaxSubgroups (S : Subgroup G),
      ¬ B ≤ pCore 2 G → (pCore 2 G).relIndex A ≤ (pCore 2 G).relIndex B)
    (hU : U ≤ pCore 2 G) (hkernel : A ⊓ centralizer (U : Set G) ≤ pCore 2 G)
    (h1 : 2 * Nat.log 2 ((pCore 2 G).relIndex A) = fixedCodim (normalRepresentation U) A)
    (h2 : fixedCodim (normalRepresentation U) A =
      2 * Nat.log 2 ((centralizer (U : Set G)).relIndex (A ⊓ pCore 2 G)))
    (hc : U ⊓ centralizer (A : Set G) = U ⊓ centralizer (A ⊓ pCore 2 G : Set G))
    (hsel : SourceThompsonSelection (S : Subgroup G) A) :
    omegaOneCenterAmbient (ChapterB.thompsonJ (S : Subgroup G) 1) ≤
      centralizer (pResidual 2 G : Set G) := by
  let X := hsel.X
  let R := (pCore 2 X).map X.subtype
  let L := (pResidual 2 X).map X.subtype
  have hXR : X ≤ normalizer (R : Set G) := by
    intro x hx
    apply Subgroup.le_normalizer_map X.subtype
    exact ⟨⟨x,hx⟩, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩
  have hLR : L ≤ normalizer (R : Set G) :=
    (Subgroup.map_subtype_le (pResidual 2 X)).trans hXR
  apply ChapterB.omega_thompson_one_centralizes_residual_of_minimal_actor
    (S : Subgroup G) (pCore 2 G) R U A L S.isPGroup' hA hmin hU
    hsel.core_le hsel.core_le_sylow hkernel (MulAut.conjNormal : G →* MulAut U)
    (MulAut.conjNormal_ker_eq_centralizer U)
  · rw [← normalRepresentation_fixedCodim_eq_rank_difference U A]
    exact h1.symm
  · rw [← normalRepresentation_fixedCodim_eq_rank_difference U A]
    exact h2
  · exact hc
  · exact hsel.actor_index
  · exact hLR
  · exact hsel.residual_commutator
  · exact hsel.residual_generation

/-- Original 15.1.12(4) for the exact module in the qrc source. The only
additional source premise is the chief-classification selection for its
same minimal actor; every rank, kernel and maximum-order input is derived. -/
theorem QrcHypotheses.sqtk_thompson_omega_centralizes_residual_of_selection
    {T : Sylow 2 G} {M M₀ H V : Subgroup G}
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2)
    (hselect :
      let d := h.toQRCConfiguration (h.no_common_normal hu)
      let U := (conjugateSpan H V).subgroupOf H
      let S := T.subtype h.right_mem.1.1.2
      letI := d.module_elementary
      letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
      letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
        ((span_le_right_core d hV).trans (twoCore_le H))
      ∀ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H), ¬ A ≤ pCore 2 H →
        IsQuadratic (normalRepresentation U) A →
        (∀ B ∈ elementaryAbelianMaxSubgroups (S : Subgroup H),
          ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) →
        2 * Nat.log 2 ((pCore 2 H).relIndex A) = fixedCodim (normalRepresentation U) A →
        fixedCodim (normalRepresentation U) A =
          2 * Nat.log 2 ((centralizer (U : Set H)).relIndex (A ⊓ pCore 2 H)) →
        U ⊓ centralizer (A : Set H) = U ⊓ centralizer (A ⊓ pCore 2 H : Set H) →
        Nonempty (SourceThompsonSelection (S : Subgroup H) A)) :
    omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) ≤
      centralizer ((pResidual 2 H).map H.subtype : Set G) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  have hnf := source_notFF_of_ratio_two d hq
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
  obtain ⟨A,hA,hAR,hquad,hmin,hall⟩ :=
    h.sqtk_minimal_actor_equalities hG hM hu hJ hne hV hdual hq
  obtain ⟨s⟩ := NoncentralChiefRefinement.SeriesOn.exists_series U
  have hs := hall s
  obtain ⟨sel⟩ := hselect A hA hAR hquad hmin hs.2.1 hs.2.2.1 hs.2.2.2.1
  have hUN : U ≤ pCore 2 H := by
    intro u hu
    obtain ⟨x,hx,he⟩ := span_le_right_core d hV hu
    exact H.subtype_injective he ▸ hx
  have hkernel : A ⊓ centralizer (U : Set H) ≤ pCore 2 H :=
    (inf_le_inf_right _ hA.1).trans
      (source_span_centralizer_sylow_le_core d hne hV hnf S hS)
  have hi := thompson_centralizes_residual_of_source_selection S U A hA hmin hUN hkernel
    hs.2.1 hs.2.2.1 hs.2.2.2.1 sel
  have hm := Subgroup.map_mono (f := H.subtype) hi
  rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
    ← ChapterB.thompsonJ_map_injective H.subtype H.subtype_injective, hS] at hm
  exact hm.trans (by
    simpa only [Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (pResidual 2 H : Set H) H.subtype)

end CFSG.Quasithin.Chapter3
