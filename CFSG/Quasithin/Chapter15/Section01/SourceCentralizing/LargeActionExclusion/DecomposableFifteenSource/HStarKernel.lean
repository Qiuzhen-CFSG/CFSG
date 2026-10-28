module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.IntersectionResidual
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedSmallChiefActions
public import Theory.Representation.BinaryOffender.IrreducibleResidual

/-!
# Actual H-star chief kernels in the full quintic row

The original quintic intersection residual has unique maximal overgroup M.
Its normalizer control identifies every noncentral chief-action kernel of
an actual H-star with O₂(H). Thus the prepared small chief-action theorem
classifies the literal quotient H/O₂(H), retaining the original module and
its actual H-conjugate span throughout.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

/-- Every noncentral chief factor of the original H-span has kernel O₂(H). -/
theorem PreparedChosenModule.decomposable_five_HStar_chief_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      ∀ {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M),
      let W := (conjugateSpan H V).subgroupOf H
      letI := (h.chief_data hG T hempty hM hJ H hH).1
      letI : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf
        (show conjugateSpan H V ≤ H by
          rw [UniqueFactor.conjugateSpan_eq]
          exact conjugateSpanBy_le_self ((h.inside_core H hH).trans (twoCore_le H)))
      ∀ (σ : SeriesOn W) (i : Fin σ.series.length), ¬ σ.Central i →
        (Representation.BinaryOffender.actionHom (σ.factorRepresentation i)).ker = pCore 2 H := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive H hH
  let W := (conjugateSpan H V).subgroupOf H
  let := (h.chief_data hG T hempty hM hJ H hH).1
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro σ i hi
  let := σ.factorRepresentation_irreducible i
  let ρ := σ.factorRepresentation i
  let q := Representation.BinaryOffender.actionHom ρ
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply hi
    apply (σ.central_iff_action i).mpr
    intro x v
    have hx : q x = 1 := show x ∈ q.ker from he ▸ mem_top x
    exact congrArg Additive.toMul ((actionHom_eq_one_iff ρ x).mp hx (Additive.ofMul v))
  have huni := h.decomposable_five_caseIIResidual_unique hG T hempty hM hmany hJ hu hfull
    c d hd s π hp hs hdec hq hfive
  exact Section02.source_HStar_reduced_kernel_of_residual_unique hG T hM hJ hu h huni hH q
    ρ.asGroupHom.rangeRestrict_surjective (irreducible_image_twoCore_eq_bot ρ) hn

/-- The actual H-star quotient belongs to the four prepared small actor types. -/
theorem PreparedChosenModule.decomposable_five_HStar_small_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      ∀ {H : Subgroup G}, H ∈ Chapter3.HStar (T : Subgroup G) M →
        ChapterB.ChiefSmallActor (H ⧸ pCore 2 H) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive H hH
  let W := (conjugateSpan H V).subgroupOf H
  let := (h.chief_data hG T hempty hM hJ H hH).1
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.inside_core H hH).trans (twoCore_le H)))
  obtain ⟨σ⟩ := SeriesOn.exists_series W
  have hcount := (h.chief_data hG T hempty hM hJ H hH).2 σ
  obtain ⟨i,hi⟩ : ∃ i, ¬ σ.Central i := by
    by_contra! hc
    have hz := σ.noncentralCount_eq_zero_iff.mpr hc
    omega
  have hk := h.decomposable_five_HStar_chief_kernel hG T hempty hM hmany hJ hu hfull
    c d hd s π hp hs hdec hq hfive hH σ i hi
  have ha := h.chief_small_quotient hG T hempty hM hJ hH σ i hi
  exact ha.of_equiv (QuotientGroup.quotientMulEquivOfEq hk.symm)

end CFSG.Quasithin.Chapter15.Section01
