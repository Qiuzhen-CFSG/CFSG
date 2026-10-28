module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefImages
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors.Alignment
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors.RankOneImages
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization

/-!
# Original Delta images and internal-module replacement

The first two theorems apply the explicit B.2.9 replacement inside an actual
normal elementary subgroup. The lift retains maximum elementary order,
Delta membership, containment in the original actor/module join, and the
literal image modulo O₂(H). Inclusion-minimality then excludes every proper
weak offender on such an internal module.

The original-chief application constructs an order-two best offender in each
marked factor whenever the original Delta image has order four. Combining
this with the lift excludes order four conditionally on an actual internal
natural wreath module with two-core centralizer. This extra module has not
been constructed from the preceding source hypotheses. In particular it
cannot be chosen inside U_H: uniform fixed-centralizer equality proves the
last obstruction theorem. A chief quotient is not an internal-module witness.

The unconditional order-four exclusion and marked offender-generation
identities remain with qt-e-152-offender-plane. The preceding small-parabolic
inputs are produced by qt-e-152-small-parabolic and finally discharged by
qt-e-152-plane-geometry. This module does not add the internal-module premise
to the source theorem or to its existing plane consumer.

Source: Aschbacher--Smith B.2.8--9, 15.1.12(2), and Notation 15.2.9,
printed pp.77,1090,1110; refs/quasithin.pdf.
-/

public section
open NoncentralChiefRefinement Theory.GroupTheory
open Subgroup Stellmacher Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterD
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

/-- A weak offender on an actual internal module lifts while preserving the
maximum elementary family used in Delta. The kernel is the literal two-core. -/
theorem delta_internal_lift {H A : Subgroup G} (hA : A ∈ delta H)
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (q : H →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (W : Set H)) (hQ : q.ker = pCore 2 H)
    (hweak : ¬ IsStrongOffender (NormalElementaryQuotient.representation W q hq hk)
      ((A.subgroupOf H).map q))
    (E : Subgroup D)
    (hE : IsOffender (NormalElementaryQuotient.representation W q hq hk) E)
    (hEA : E ≤ (A.subgroupOf H).map q) :
    ∃ B ∈ delta H, B ≤ A ⊔ W.map H.subtype ∧
      (B.subgroupOf H).map q = E ∧ offenderImage H B = offenderImage H A := by
  let A₀ := A.subgroupOf H
  have hAm : A₀ ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup H) := by
    apply (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ A₀).mp
    simpa only [A₀,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hA.1.1] using hA.1
  have hAn : A₀.map q ≠ ⊥ := by
    intro hz
    have hAQ := (map_eq_bot_iff A₀).mp hz
    rw [hQ] at hAQ
    have hm := map_mono (f := H.subtype) hAQ
    rw [map_subgroupOf_eq_of_le hA.1.1] at hm
    exact hA.2.1 hm
  let B₀ := A₀ ⊓ E.comap q
  let B := B₀ ⊔ (W ⊓ centralizer (B₀ : Set H))
  obtain ⟨hB,hBE⟩ := ChapterB.lemma_B_2_9_construct W q hq hk ⊤ le_top
    A₀ ⟨hAm,hAn⟩ hweak E hE hEA
  have hBm : B.map H.subtype ∈ elementaryAbelianMaxSubgroups H := by
    have hm := (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ B).mpr hB.1
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hm
  have hBn : ¬ B.map H.subtype ≤ twoCoreIn H := by
    intro hh
    have hn : B ≤ pCore 2 H := (map_le_map_iff_of_injective H.subtype_injective).mp hh
    exact hB.2 ((map_eq_bot_iff B).mpr (hQ.symm ▸ hn))
  have hBA : B.map H.subtype ≤ A ⊔ W.map H.subtype := by
    have hm := map_mono (f := H.subtype)
      (show B ≤ A₀ ⊔ W from sup_le (inf_le_left.trans le_sup_left)
        (inf_le_left.trans le_sup_right))
    simpa only [Subgroup.map_sup,A₀,map_subgroupOf_eq_of_le hA.1.1] using hm
  have hWQ : W.map H.subtype ≤ twoCoreIn H := by
    apply map_mono
    rw [←hQ,hk]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hBAq : offenderImage H (B.map H.subtype) ≤ offenderImage H A :=
    (offenderImage_le_iff hBm.1 hA.1.1).mpr
      (hBA.trans (sup_le_sup_left hWQ A))
  have heq : offenderImage H (B.map H.subtype) = offenderImage H A :=
    le_antisymm hBAq (hA.2.2 _ hBm hBn hBAq)
  have hDel : B.map H.subtype ∈ delta H := by
    refine ⟨hBm,hBn,?_⟩
    intro C hC hCn hCB
    rw [heq] at hCB ⊢
    exact hA.2.2 C hC hCn hCB
  refine ⟨B.map H.subtype,hDel,hBA,?_,heq⟩
  have hm : (B.map H.subtype).subgroupOf H = B := by
    apply map_injective H.subtype_injective
    exact map_subgroupOf_eq_of_le hBm.1
  rw [hm]
  exact hBE

/-- Original quotient-image minimality rules out every proper weak offender
on an internal module whose centralizer is O₂(H). -/
theorem delta_internal_offender_eq {H A : Subgroup G} (hA : A ∈ delta H)
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (q : H →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (W : Set H)) (hQ : q.ker = pCore 2 H)
    (hweak : ¬ IsStrongOffender (NormalElementaryQuotient.representation W q hq hk)
      ((A.subgroupOf H).map q))
    (E : Subgroup D)
    (hE : IsOffender (NormalElementaryQuotient.representation W q hq hk) E)
    (hEA : E ≤ (A.subgroupOf H).map q) : E = (A.subgroupOf H).map q := by
  obtain ⟨B,hB,_,hBE,hBA⟩ := delta_internal_lift hA W q hq hk hQ hweak E hE hEA
  rw [←hBE]
  apply le_antisymm
  all_goals
    rw [Subgroup.map_le_map_iff,hQ]
  · have hh := (offenderImage_le_iff hB.1.1 hA.1.1).mp hBA.le
    rw [←map_le_map_iff_of_injective H.subtype_injective,Subgroup.map_sup,
      map_subgroupOf_eq_of_le hB.1.1,map_subgroupOf_eq_of_le hA.1.1]
    exact hh
  · have hh := (offenderImage_le_iff hA.1.1 hB.1.1).mp hBA.ge
    rw [←map_le_map_iff_of_injective H.subtype_injective,Subgroup.map_sup,
      map_subgroupOf_eq_of_le hB.1.1,map_subgroupOf_eq_of_le hA.1.1]
    exact hh
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
namespace CFSG.Quasithin.Chapter15.Section02
open Subgroup Stellmacher Representation Representation.BinaryOffender NoncentralChiefRefinement
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor SmallActionsSource
variable {G : Type*} [Group G] [Finite G]

/-- In the order-four branch, every original chief image contains a cyclic
best offender in each of its two literally marked natural factors. -/
theorem ChosenSmallSource.delta_four_chief_cyclic_offenders
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A∈delta H) (hfour : Nat.card (offenderImage H A)=4)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (j : Fin s.series.length) (hj : ¬ s.Central j)
    (c : ChiefWreathCoordinates (s.factorRepresentation j)) (i : ChiefWreath.C2) :
    ∃ E : Subgroup (actionImage (s.factorRepresentation j)),
      E ≤ actionSubgroup (s.factorRepresentation j) (A.subgroupOf H) ∧
      Nat.card E=2 ∧ IsBestOffender (imageRepresentation (s.factorRepresentation j)) E ∧
      E ≤ (ChiefWreath.factor i).comap c.imageEquiv.toMonoidHom := by
  let A₀ := A.subgroupOf H
  let : IsElementaryAbelian 2 A := hA.1.2.1
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hA.1.1
  have hAm : A₀ ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup H) := by
    apply (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ A₀).mp
    simpa only [A₀,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hA.1.1] using hA.1
  have hAb : A₀.map c.actor ≤ ChiefWreath.base := by
    apply map_le_iff_le_comap.mpr
    rw [←c.factor_sup_eq_base,h.chief_marked_base hunique hH he s j hj c]
    exact le_sup_of_le_left (le_sSup hAm)
  have hk : c.actor.ker=pCore 2 H :=
    c.kernel.trans (h.chief_kernel_of_residual_unique hunique hH s j hj)
  have hcard : Nat.card (A₀.map c.actor)=4 := by
    rw [←Subgroup.relIndex_ker,hk]
    change Nat.card ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))=4 at hfour
    rwa [←Subgroup.relIndex_ker,QuotientGroup.ker_mk'] at hfour
  exact c.four_image_contains_cyclic_bestOffender A₀ i hAb hcard
end CFSG.Quasithin.Chapter15.Section02
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Subgroup Stellmacher Representation Representation.BinaryOffender
open SmallActionsSource ChapterD
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normal_image_representation (U : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U] :
    NormalElementaryQuotient.representation U (Representation.BinaryOffender.actionHom
      (normalRepresentation U)) (normalRepresentation U).asGroupHom.rangeRestrict_surjective
      ((actionHom_ker_eq _).trans (MultipleFactors.normalRepresentation_ker U)) =
    Representation.BinaryOffender.imageRepresentation (normalRepresentation U) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := (normalRepresentation U).asGroupHom.rangeRestrict_surjective g
  apply Additive.toMul.injective
  apply Subtype.ext
  exact NormalElementaryQuotient.representation_apply U _ _ _ x v

/-- The original order-four image is excluded once the natural action occurs
on an actual normal elementary subgroup with two-core centralizer. The internal
module still requires construction in the source
application; a chief quotient alone is not such a witness. -/
theorem delta_image_ne_four_of_internal_wreath {H A : Subgroup G}
    (hA : A∈delta H) (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (c : ChiefWreathCoordinates (normalRepresentation W))
    (hQ : c.actor.ker=pCore 2 H)
    (hbase : (A.subgroupOf H).map c.actor ≤ ChiefWreath.base) :
    Nat.card (offenderImage H A) ≠ 4 := by
  intro hfour
  let ρ := normalRepresentation W
  let q := Representation.BinaryOffender.actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hk : q.ker=centralizer (W : Set H) :=
    (actionHom_ker_eq _).trans (MultipleFactors.normalRepresentation_ker W)
  have hqQ : q.ker=pCore 2 H := c.kernel.symm.trans hQ
  let A₀ := A.subgroupOf H
  let : IsElementaryAbelian 2 A := hA.1.2.1
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hA.1.1
  have hcard : Nat.card (A₀.map c.actor)=4 := by
    rw [←Subgroup.relIndex_ker,hQ]
    change Nat.card ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))=4 at hfour
    rwa [←Subgroup.relIndex_ker,QuotientGroup.ker_mk'] at hfour
  have hweak := c.four_image_not_strong A₀ hbase hcard
  obtain ⟨E,hEA,hEcard,hE,_⟩ := c.four_image_contains_cyclic_bestOffender A₀ 1 hbase hcard
  have hrep : NormalElementaryQuotient.representation W q hq hk=imageRepresentation ρ :=
    normal_image_representation W
  have hEq : E=A₀.map q := delta_internal_offender_eq hA W q hq hk hqQ
    (hrep.symm ▸ hweak) E (hrep.symm ▸ hE.isOffender (imageRepresentation ρ)) hEA
  have hfour' : Nat.card (A₀.map q)=4 := by
    rw [←Subgroup.relIndex_ker,hqQ]
    rwa [←Subgroup.relIndex_ker,hQ] at hcard
  rw [hEq,hfour'] at hEcard
  contradiction
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
namespace CFSG.Quasithin.Chapter15.Section02
open Subgroup Stellmacher ChosenGeometry ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- A module inside the original span that is centralized by O₂(H) cannot
have centralizer O₂(H): the uniform fixed-space equality would put the
original Delta actor in O₂(H). Thus an internal-module lift cannot simply
reinterpret one of the chief quotients as a subgroup of the span. -/
theorem ChosenSmallSource.delta_no_core_faithful_subgroup_of_span
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) (hA : A∈delta H)
    (W : Subgroup G) (hWU : W ≤ conjugateSpan H V)
    (hQW : twoCoreIn H ≤ centralizer (W : Set G)) :
    H ⊓ centralizer (W : Set G) ≠ twoCoreIn H := by
  intro hker
  have hWB : W ≤ centralizer (A ⊓ twoCoreIn H : Subgroup G) :=
    le_centralizer_iff.mp ((inf_le_right : A ⊓ twoCoreIn H ≤ twoCoreIn H).trans hQW)
  have hWF : W ≤ conjugateSpan H V ⊓ centralizer (A : Set G) := by
    rw [h.delta_fixed hH hA]
    exact le_inf hWU hWB
  have hAW : A ≤ centralizer (W : Set G) :=
    le_centralizer_iff.mp (hWF.trans inf_le_right)
  exact hA.2.1 (hker ▸ le_inf hA.1.1 hAW)
end CFSG.Quasithin.Chapter15.Section02
namespace CFSG.Quasithin.Chapter15.Section02
open Subgroup Stellmacher Representation Representation.BinaryOffender NoncentralChiefRefinement Theory.GroupTheory
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor SmallActionsSource
variable {G : Type*} [Group G] [Finite G]

/-- The order-two branch places the original offender in one marked factor
on every literal noncentral chief module, with fixed codimension one. -/
theorem ChosenSmallSource.delta_two_chief_factor
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A∈delta H) (htwo : Nat.card (offenderImage H A)=2)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (j : Fin s.series.length) (hj : ¬ s.Central j)
    (c : ChiefWreathCoordinates (s.factorRepresentation j)) :
    ∃ i : ChiefWreath.C2, A.subgroupOf H ≤ c.factor i ∧
      fixedCodim (s.factorRepresentation j) (A.subgroupOf H)=1 := by
  let A₀ := A.subgroupOf H
  have hAm : A₀ ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup H) := by
    apply (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ A₀).mp
    simpa only [A₀,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hA.1.1] using hA.1
  have hAb : A₀.map c.actor ≤ ChiefWreath.base := by
    apply map_le_iff_le_comap.mpr
    rw [←c.factor_sup_eq_base,h.chief_marked_base hunique hH he s j hj c]
    exact le_sup_of_le_left (le_sSup hAm)
  have hk : c.actor.ker=pCore 2 H :=
    c.kernel.trans (h.chief_kernel_of_residual_unique hunique hH s j hj)
  have hidx : (pCore 2 H).relIndex A₀=2 := by
    change Nat.card ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))=2 at htwo
    rwa [←Subgroup.relIndex_ker,QuotientGroup.ker_mk'] at htwo
  have hcard : Nat.card (A₀.map c.actor)=2 := by
    rw [←Subgroup.relIndex_ker,hk,hidx]
  have hc : fixedCodim (s.factorRepresentation j) A₀=1 := by
    have hh := (h.delta_chief_actions hH hA s j hj).2.1
    rw [hidx,show Nat.log 2 2=1 by decide] at hh
    exact hh.symm
  obtain ⟨i,hi⟩ := c.order_two_image_le_factor A₀ hAb hcard hc
  exact ⟨i,hi,hc⟩
end CFSG.Quasithin.Chapter15.Section02
