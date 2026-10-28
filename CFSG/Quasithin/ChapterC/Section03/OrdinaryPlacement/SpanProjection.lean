module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.Preparation
public import CFSG.Quasithin.ChapterC.Section03
public import Theory.GroupTheory.CentralProductMovedProjection
public import Theory.GroupTheory.RadicalNormalizerControl

/-!
# The ordinary-component projection under genuine C.2.8

The original perfect span acts by inner automorphisms on each ordinary
component. The normalizer bound on the moved module makes its projection
nontrivial. Perfect central-product projection therefore produces a subgroup
of the same component with noncentral two-core. Component-stabilizer
saturation puts this two-core inside the original radical R.

No normalization of L by M is assumed. These are the projection and local
subgroup obstructions in C.3.2--3, printed p.149. The subsequent placement
and local subgroup classification are separate inputs to C.3.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- Schreier applies to the unchanged perfect source span. -/
theorem ordinary_span_inner (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    (conjugateSpanBy L M).subgroupOf H ≤ K ⊔ centralizer (K : Set H) := by
  have hAH := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect ((conjugateSpanBy L M).subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hAH).symm.toMonoidHom)
      (subgroupOfEquivOfLe hAH).symm.surjective
  let := h.component_outer_solvable K hK
  exact perfect_le_sup_centralizer_of_solvable_outer K _
    (hK.perfect_le_normalizer_of_odd_rank_le_two h.sqtk.stronglyQuasithin _)

/-- The original module has nontrivial action on every ordinary component. -/
theorem ordinary_module_not_centralizes
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    ¬ V.subgroupOf H ≤ centralizer (K : Set H) := by
  have hVH := h.module_le.trans
    ((conjugateSpanBy_le_self h.component_le).trans h.local_le)
  have hN : normalizer (V.subgroupOf H : Set H) ≤ M.subgroupOf H := by
    rw [←subgroupOf_normalizer_eq hVH]
    intro x hx
    exact h.module_normalizer ⟨x.property,hx⟩
  intro hc
  exact h.component_not_le K hK
    ((le_centralizer_iff.mp hc).trans ((Subgroup.centralizer_le_normalizer _).trans hN))

/-- The actual source projection retains its factor, its stabilizer and its
radical containment; its two-core is not central in the projection. -/
theorem ordinary_span_projection
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    ∃ P Q : Subgroup H, P ≤ K ∧ Q ≤ centralizer (K : Set H) ∧
      Group.IsPerfect P ∧ Group.IsPerfect Q ∧
      (conjugateSpanBy L M).subgroupOf H ≤ P ⊔ Q ∧
      P ≤ (conjugateSpanBy L M).subgroupOf H ⊔ Q ∧
      ⁅P.pCoreIn 2,P⁆ ≠ ⊥ ∧ P.pCoreIn 2 ≤ R.subgroupOf H ∧
      M.subgroupOf H ⊓ normalizer (K : Set H) ≤ normalizer (P : Set H) := by
  let A := (conjugateSpanBy L M).subgroupOf H
  let B := M.subgroupOf H
  let U := V.subgroupOf H
  have hAH := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  have hVH := h.module_le.trans hAH
  have hRH := h.radical_le.trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hAH).symm.surjective
  have hUA : U ≤ A := subgroupOf_mono H h.module_le
  have hmove : U = ⁅U,A⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hAH]
    exact h.module_commutator
  obtain ⟨P,Q,hPK,hQC,hP,hQ,hAP,hPA,hnc,hN⟩ :=
    exists_perfect_projection_with_noncentral_core K (centralizer (K : Set H)) A U
      (le_centralizer_iff.mp le_rfl) (h.ordinary_span_inner K hK) hUA
      h.module_elementary.isPGroup.comap_subtype hmove (h.ordinary_module_not_centralizes K hK)
  have hBA : B ≤ normalizer (A : Set H) := by
    intro b hb a
    exact le_normalizer_conjugateSpanBy L M hb (a : G)
  have hBP : B ⊓ normalizer (K : Set H) ≤ normalizer (P : Set H) :=
    hN _ inf_le_right (inf_le_right.trans (normalizer_le_normalizer_centralizer K))
      (inf_le_left.trans hBA)
  have hNR : normalizer (R.subgroupOf H : Set H) ≤ B := by
    rw [←subgroupOf_normalizer_eq hRH]
    intro x hx
    exact h.normalizer_le ⟨x.property,hx⟩
  have hsat : ∀ W : Subgroup H, IsPGroup 2 W → B ≤ normalizer (W : Set H) →
      W ≤ R.subgroupOf H := by
    intro W hp hBW
    exact le_of_normalizer_le_normalizer_of_pCore_normalizer_le _ W
      h.isRadical.isPGroup hp h.isRadical.2.le (hNR.trans hBW)
  have hcore : P.pCoreIn 2 ≤ R.subgroupOf H :=
    hK.stabilizer_saturation hsat _ ((pCoreIn_le 2 P).trans hPK)
      (isPGroup_pCoreIn 2 P)
      (hBP.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  exact ⟨P,Q,hPK,hQC,hP,hQ,hAP,hPA,hnc,hcore,hBP⟩

/-- The original radical meets every ordinary component noncentrally. This
gives the nontrivial local subgroup used in C.3.5 before any placement of V. -/
theorem ordinary_radical_intersection_not_centralizes
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    ¬ R.subgroupOf H ⊓ K ≤ centralizer (K : Set H) := by
  obtain ⟨P,Q,hPK,_,_,_,_,_,hnc,hcore,_⟩ := h.ordinary_span_projection K hK
  intro hc
  exact hnc (commutator_eq_bot_iff_le_centralizer.mpr
    ((le_inf hcore ((pCoreIn_le 2 P).trans hPK)).trans (hc.trans (centralizer_le hPK))))

/-- A model inspection excluding noncentral two-cores of perfect subgroups
excludes that model as an ordinary component of the original source H. -/
theorem no_ordinary_component_of_perfect_subgroup_core_central
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    (hlocal : ∀ P : Subgroup H, P ≤ K → Group.IsPerfect P → ⁅P.pCoreIn 2,P⁆ = ⊥) :
    False := by
  obtain ⟨P,Q,hPK,_,hP,_,_,_,hnc,_,_⟩ := h.ordinary_span_projection K hK
  exact hnc (hlocal P hPK hP)

end CFSG.Quasithin.ChapterC.HypothesisC28
