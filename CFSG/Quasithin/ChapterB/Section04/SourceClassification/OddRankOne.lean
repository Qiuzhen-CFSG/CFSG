module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Alternating
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.SourceFF
public import CFSG.Quasithin.ChapterK.Section01To04.OddCharacteristic.Coincidences
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Eleven
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive.SourceGeometry

/-!
# The odd rank-one parameter sieve on the genuine B.4 source domain

The original FF hypothesis supplies the cubic bound required by the proved
q≤25 argument and the five small-prime exclusions. The new actual q=25
field and diagonal actor calculations close the sixth exclusion at the FF
threshold. The only surviving prime/exponent pairs are (5,1), (7,1), (3,2),
and the actual exceptional isomorphisms transport these to the completed
alternating and binary-linear recognition theorems. The resulting action
case retains the original layer, offender subgroup and permitted ambient
extensions.

Source: Aschbacher--Smith B.4.2 and K.2, printed pp.86 and 453.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
open ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The literal B.4 source action with PSL₂(25) central quotient is not FF. -/
theorem not_ff_pslTwo_twentyFive (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 25) : ¬ IsFFModule ρ := by
  rcases h with ⟨hsq, hfit, hquasi, hfaith, hirr, _⟩
  subst L
  exact RankOneSmall.TwentyFive.source_not_ff ρ ⟨hsq, hquasi, hfaith, hirr⟩ hm

/-- The exact three remaining parameters, on the original specified layer.
Neither actor generation nor a representation classifier is an extra premise. -/
theorem odd_pslTwo_parameters (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hlo : 4 ≤ p ^ e)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ e)) :
    (p = 5 ∧ e = 1) ∨ (p = 7 ∧ e = 1) ∨ (p = 3 ∧ e = 2) := by
  rcases h with ⟨hsq, hfit, hquasi, hfaith, hirr, hratio⟩
  subst L
  let h : SourceAction ρ := ⟨hsq, hquasi, hfaith, hirr⟩
  have hhi := RankOneSize.source_field_order_le_twentyFive ρ h hp ho he hlo hm hratio
  rcases prime_power_candidates_le_twentyFive hp ho he hlo hhi with hgood | hbad
  · exact hgood
  · exfalso
    rcases hbad with hq | hq | hq | hq | hq | hq
    · rw [hq] at hm
      exact (not_lt_of_ge hratio) (RankOneSmall.Eleven.two_lt_cubicRatio ρ h hm)
    · rw [hq] at hm
      exact (not_lt_of_ge hratio)
        (RankOneSmall.source_prime_exclusion ρ h (Or.inl rfl) hm)
    · rw [hq] at hm
      have hd := RankOneSmall.source_seventeen_degree_eq_eight ρ h hm hratio
      exact (not_lt_of_ge hratio)
        (RankOneSmall.Seventeen.two_lt_cubicRatio_of_degree_le_eight ρ h hm hd.le)
    · rw [hq] at hm
      exact (not_lt_of_ge hratio)
        (RankOneSmall.source_prime_exclusion ρ h (Or.inr (Or.inl rfl)) hm)
    · rw [hq] at hm
      exact (not_lt_of_ge hratio)
        (RankOneSmall.source_prime_exclusion ρ h (Or.inr (Or.inr rfl)) hm)
    · rw [hq] at hm
      exact RankOneSmall.TwentyFive.source_not_ff ρ h hm hff

/-- Apply the parameter sieve directly to an original best offender. -/
theorem odd_pslTwo_parameters_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hlo : 4 ≤ p ^ e) (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ e)) :
    (p = 5 ∧ e = 1) ∨ (p = 7 ∧ e = 1) ∨ (p = 3 ∧ e = 2) :=
  odd_pslTwo_parameters (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA)
    ⟨A, hA.isOffender ρ⟩ hp ho he hlo hm

/-- The complete odd-PSL₂ source family has an actual B.4 action row.
The three surviving exceptional isomorphisms act on the original central
quotient; the component and ambient representation are retained. -/
theorem odd_pslTwo_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hlo : 4 ≤ p ^ e)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ e)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  rcases odd_pslTwo_parameters h hff hp ho he hlo hm with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨eQ⟩ := ChapterK.OddCharacteristic.altFive_of_psl2_five (by simpa using hm)
    exact alternating_case h hff (by decide) eQ
  · obtain ⟨eQ⟩ := ChapterK.OddCharacteristic.psl3Two_of_psl2_seven (by simpa using hm)
    have hquot : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ 1) :=
      ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ⟨eQ⟩⟩
    obtain ⟨A, hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
    exact ChapterK.Linear.SourceFF.actionCase_of_bestOffender ρ h.sqtk h.fitting.symm
      h.quasisimple h.faithful h.irreducible 1 (by decide) hquot A hA
  · obtain ⟨eQ⟩ := ChapterK.OddCharacteristic.altSix_of_psl2_nine (by simpa using hm)
    exact alternating_case h hff (by decide) eQ

/-- The full odd rank-one branch for the literal B.4 best-offender dispatcher. -/
theorem odd_pslTwo_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hlo : 4 ≤ p ^ e) (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ e)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  odd_pslTwo_case (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA)
    ⟨A, hA.isOffender ρ⟩ hp ho he hlo hm

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The literal Theorem C constructor supplies no positive exponent or lower
field-order bound. The actual field excludes exponent zero; perfection of
the source central quotient excludes PSL₂(3). -/
theorem odd_pslTwo_source_bounds (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {p e : ℕ} (_hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ e)) :
    (e = 1 ∨ e = 2) ∧ 4 ≤ p ^ e := by
  obtain ⟨F, _, _, hF, ⟨eQ⟩⟩ := hm
  have hgt : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have he0 : e ≠ 0 := by
    intro hzero
    rw [hzero, pow_zero] at hF
    omega
  have hodd : Odd (Nat.card F) := hF ▸ ho.pow
  have hthree : Nat.card F ≠ 3 := by
    intro hthree
    let := h.quasisimple
    let : Group.IsPerfect (L ⧸ center L) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center L))
    let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Group.IsPerfect.ofSurjective (f := eQ.toMonoidHom) eQ.surjective
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three hthree inferInstance
  refine ⟨by omega, ?_⟩
  obtain ⟨k, hk⟩ := hodd
  omega

/-- Original Theorem C odd rank-one constructor, with both numerical bounds
proved from its actual field model and the source quasisimple layer. -/
theorem odd_pslTwo_theoremC_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ e)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨he', hlo⟩ := odd_pslTwo_source_bounds h hp ho he hm
  exact odd_pslTwo_case h hff hp ho he' hlo hm

/-- Direct best-offender application for the literal C(2) linear-two row. -/
theorem odd_pslTwo_theoremC_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ e)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  odd_pslTwo_theoremC_case (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA)
    ⟨A, hA.isOffender ρ⟩ hp ho he hm

end CFSG.Quasithin.ChapterB.SourceClassification
