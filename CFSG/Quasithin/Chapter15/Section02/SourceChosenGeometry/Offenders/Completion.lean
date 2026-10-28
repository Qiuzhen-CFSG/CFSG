module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors.FourImages
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.WreathGeneration.Marked

/-!
# Original chief transvections and marked offender generators

The order-four exclusion discharges the last local premise of the existing
marked construction. Every original Delta image has order two, fixes a
hyperplane on each actual chief four-space, and lies in one distinguished
factor. Its whole-span fixed codimension is two. For each outside offender,
the literal family span X and marked residual K_i satisfy the source
normal-closure, commutator and generation identities.

The Offenders consumer uses these witnesses to prove the uniform central
plane conclusion. The preceding small-action, residual-overgroup uniqueness
and wreath hypotheses remain with qt-e-152-small-parabolic and are discharged
by the final owner qt-e-152-plane-geometry; no local offender premise remains.

Source: Aschbacher--Smith 15.1.12(2), Notation 15.2.9 and 15.2.11,
printed pp.1090,1110--1111; refs/quasithin.pdf.
-/

public section
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section02
open Subgroup Stellmacher Representation Representation.BinaryOffender
open NoncentralChiefRefinement Theory.GroupTheory SmallActionsSource
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Every original Delta image is a transvection in one of the literal marked
factors on each original noncentral chief interval. -/
theorem ChosenSmallSource.delta_chief_factor
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A∈delta H)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (j : Fin s.series.length) (hj : ¬ s.Central j)
    (c : ChiefWreathCoordinates (s.factorRepresentation j)) :
    ∃ i : ChiefWreath.C2, A.subgroupOf H ≤ c.factor i ∧
      fixedCodim (s.factorRepresentation j) (A.subgroupOf H)=1 :=
  h.delta_two_chief_factor hunique hH he hA
    (h.delta_image_card_two ha hunique hH he hA) s j hj c

/-- The sharp whole-span displacement is two for every original Delta member. -/
theorem ChosenSmallSource.delta_span_fixedCodim_two
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A∈delta H) :
    fixedCodim (normalRepresentation ((conjugateSpan H V).subgroupOf H))
      (A.subgroupOf H)=2 := by
  have htwo := h.delta_image_card_two ha hunique hH he hA
  change Nat.card ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))=2 at htwo
  rw [←Subgroup.relIndex_ker,QuotientGroup.ker_mk'] at htwo
  have hh := (h.delta_span_ranks hH he hA).1
  rw [htwo,show Nat.log 2 2=1 by decide,mul_one] at hh
  exact hh.symm

/-- The source X and K_i satisfy all the marked identities, uniformly for
original outside offenders, with the order-two premise now discharged. -/
theorem ChosenSmallSource.delta_marked_generation
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A∈delta H) (hAT : ¬ A≤(T : Subgroup G))
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (j : Fin s.series.length) (hj : ¬ s.Central j)
    (c : ChiefWreathCoordinates (s.factorRepresentation j)) :
    ∃ i : ChiefWreath.C2, A.subgroupOf H≤c.factor i ∧
      let L := (c.factor i).map H.subtype
      let K := (c.residualFactor i).map H.subtype
      let X := markedOffenderSpan (T : Subgroup G) H L
      X ≤ centralizer (V : Set G) ∧
        L=twoCoreIn H ⊔ (X ⊔ A) ∧
        conjugateSpanBy X L=X ⊔ A ∧ K≤X ⊔ A ∧ K=⁅K,A⁆ ∧
        H=(X ⊔ A) ⊔ (T : Subgroup G) ∧
        ChosenGeometry.residual H=conjugateSpanBy K H :=
  h.delta_two_marked_generation hunique hH he hA
    (h.delta_image_card_two ha hunique hH he hA) hAT s j hj c

/-- The actual marked generator witnesses for the plane-normality consumer. -/
theorem ChosenSmallSource.delta_generator_witnesses
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hA : A∈delta H) (hAT : ¬ A≤(T : Subgroup G)) :
    ∃ X K : Subgroup G, X≤centralizer (V : Set G) ∧
      H=(X ⊔ A) ⊔ (T : Subgroup G) ∧ K≤X ⊔ A ∧
      ChosenGeometry.residual H=conjugateSpanBy K H :=
  h.delta_two_generator_witnesses hunique hH he hA
    (h.delta_image_card_two ha hunique hH he hA) hAT

end CFSG.Quasithin.Chapter15.Section02
