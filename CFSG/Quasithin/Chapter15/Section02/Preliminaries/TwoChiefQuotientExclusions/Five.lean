module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.ChiefActions
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.TwoChiefQuotientExclusions.Pair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.Basic

/-!
# Two natural chief factors exclude the concrete mixed five-point Borels

Both faithful four-dimensional factors contribute to the literal elementary
H-span. That span lies in O₂(H), so the core has order at least 256 and the
original Sylow T has order at least 2048. The four existing mixed A₅/S₃
Borel models have Sylow order at most 256. Applying this bound to the
literal rank-one pair, then identifying its common Borel with H ∩ M,
excludes every such model at the actual source overlap.

This proves the model-exclusion side of the S₅ branch. Recognizing the
source pair as one of those models remains with qt-e-152-small-parabolic;
no recognition callback or single-quotient exclusion is asserted here.

Source: Aschbacher--Smith 15.1.12 and 15.2.8, printed pp.1090,1109--1110,
and the mixed alternatives in F.1.12, printed pp.262--264.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The literal orbit span lies inside the intrinsic two-core of H. -/
theorem ChosenSmallSource.HStar_span_le_core
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    (conjugateSpan H V).subgroupOf H ≤ pCore 2 H := by
  have hc : conjugateSpan H V ≤ H.pCoreIn 2 := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le (h.prepared.inside_core H hH) (twoCore_normalized H)
  intro x hx
  obtain ⟨y,hy,he⟩ := hc hx
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy

/-- Both faithful natural four-spaces contribute to the actual H-core. -/
theorem ChosenSmallSource.symmetricFive_core_card
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    256 ≤ Nat.card (pCore 2 H) := by
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  have hb := card_le_of_le (h.HStar_span_le_core hH)
  rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv] at hb
  exact (h.symmetricFive_span_card hprior hH he).trans hb

private theorem symmetricFive_sylow_core_ratio {D : Type*} [Group D] [Finite D]
    (e : (D ⧸ pCore 2 D) ≃* Equiv.Perm (Fin 5)) (P : Sylow 2 D) :
    Nat.card P = 8 * Nat.card (pCore 2 D) := by
  have hq : Nat.card (D ⧸ pCore 2 D) = 120 :=
    (Nat.card_congr e.toEquiv).trans (by
      simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
  have hc : Nat.card D = 120 * 2 ^ n := by
    rw [(pCore 2 D).card_eq_card_quotient_mul_card_subgroup,hq,hn]
  rw [P.card_eq_multiplicity,hc,hn,
    Nat.factorization_mul (by decide) (pow_ne_zero _ (by decide)),
    Nat.factorization_pow]
  have hf : (120 : ℕ).factorization 2 = 3 := by decide +kernel
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,hf,
    Nat.prime_two.factorization,Finsupp.single_eq_same,mul_one]
  rw [pow_add]
  rfl

/-- The two chief factors force the original ambient Sylow to have order
at least 2048 in the single symmetric-five branch. -/
theorem ChosenSmallSource.symmetricFive_sylow_card
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    2048 ≤ Nat.card T := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hc := symmetricFive_sylow_core_ratio he.some (T.subtype hTH)
  have hcard : Nat.card (T.subtype hTH) = Nat.card T := by
    change Nat.card ((T : Subgroup G).subgroupOf H) = Nat.card T
    exact Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv
  rw [hcard] at hc
  have hl := h.symmetricFive_core_card hprior hH he
  omega

/-- None of the concrete mixed A₅/S₃ Borels can be the original common
Borel in the single S₅ branch. Both chief factors are used in the Sylow bound.
Producing a mixed Borel model from the source pair remains a recognition step. -/
theorem SmallResidualWitness.symmetricFive_not_mixedBorelModel
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    ¬ ChapterF.Source.MixedBorelModel
      (ChapterF.Source.commonBorel
        ![Y₁ ⊔ (M ⊓ Mc).pCoreIn 2,(pResidual 2 H).map H.subtype] (T : Subgroup G)) := by
  intro hm
  have hf := (hw.symmetricFive_pair hH he).1
  have hu := hf.sylow_card_le_of_mixedBorelModel hm
  have hl := h.symmetricFive_sylow_card hprior hH he
  omega

/-- All original small actions exclude the four concrete mixed models at
their actual overlap H ∩ M. This is the consumer of the two-chief order bound;
the source recognition of that overlap is still required. -/
theorem ChosenSmallSource.symmetricFive_not_mixed_overlap
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    ¬ ChapterF.Source.MixedBorelModel (H ⊓ M : Subgroup G) := by
  obtain ⟨Y₁,hw,_⟩ := h.smallResidualWitness hprior
  obtain ⟨hF,_,hP₁,hN,_,_⟩ := hw.symmetricFive_pair hH he
  have hB := hF.commonBorel_eq_normalizer 1
  rw [hP₁] at hB
  have hB' : ChapterF.Source.commonBorel
      ![Y₁ ⊔ (M ⊓ Mc).pCoreIn 2,(pResidual 2 H).map H.subtype] (T : Subgroup G) = H ⊓ M :=
    hB.trans hN.symm
  rw [←hB']
  exact hw.symmetricFive_not_mixedBorelModel hprior hH he

end CFSG.Quasithin.Chapter15.Section02
