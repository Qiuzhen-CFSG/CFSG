module
public import CFSG.Quasithin.ChapterI.Section03.MathieuFixedModels
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Source
public import Theory.SpecificGroups.OddThreeSectionRank
public import Theory.Mathieu.TwoRankLower
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.Suzuki.InvolutoryTwoComponents

/-!
# Further model exclusions for a fixed Mathieu component

An involution of HS has only A₆ or A₈ components in its fixed group;
the order of M₂₂ excludes both. Every section of odd-field PSL₃ or PSU₃
has two-rank at most three. Pulling a PSL₂ section back to SL₂ gives the
same bound through odd-field GL₂. These bounds contradict the elementary
sixteen in M₂₂. For binary PSL₂, cyclic odd Sylow subgroups exclude its
cubic rank two. Suzuki involution fixed groups are two-groups.

The reduced Theorem B list therefore retains the four larger odd Lie
families, binary PSU₃, the rank-two families and McL. No equality of the
original Mathieu component with a proper overcomponent is asserted.
The literal exterior and Hall applications are in
Hall.OddNormalizer.PushingUpReducedProperModels and Hall.OddNormalizer.
Source: Aschbacher--Smith 4.2.13, printed p.612, and Theorem B, p.33;
GLS III Table 5.3m and the section and matrix calculations cited in the
imported modules. All quotient maps and model equivalences are actual maps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterI.MathieuPumpup
open Sporadic.Mathieu

private theorem mathieu_cover_card_dvd {B : Type*} [Group B]
    (e : (B ⧸ center B) ≃* M22) : 443520 ∣ Nat.card B := by
  rw [←m22_order,←Nat.card_congr e.toEquiv]
  exact card_quotient_dvd_card _

/-- An involution of HS cannot fix a component covering M₂₂. -/
theorem no_mathieu_fixed_hs [IsSimpleGroup Sporadic.LeechRelated.HS.Carrier]
    [Group.IsPerfect Sporadic.LeechRelated.HS.Carrier] :
    ¬ HasMathieuFixedComponent Sporadic.LeechRelated.HS.Carrier := by
  classical
  rintro ⟨a,ha,B,hB,⟨b⟩⟩
  let K := B.subgroupOf a.fixedSubgroup
  have hd : 443520 ∣ Nat.card K := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hB.1).toEquiv]
    exact mathieu_cover_card_dvd b
  by_cases hi : ∃ g : Sporadic.LeechRelated.HS.Carrier, a = MulAut.conj g
  · obtain ⟨e⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.inner_component_equiv
      a ha hi K hB.2
    rw [Nat.card_congr e.toEquiv] at hd
    change 443520 ∣ Nat.card (alternatingGroup (Fin 6)) at hd
    rw [nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
  · obtain ⟨e⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.outer_component_equiv
      a ha hi K hB.2
    rw [Nat.card_congr e.toEquiv] at hd
    change 443520 ∣ Nat.card (alternatingGroup (Fin 8)) at hd
    rw [nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd

variable {S : Type*} [Group S]

/-- The odd-field PSL₃ section rank excludes the literal Mathieu quotient. -/
theorem HasMathieuFixedComponent.not_odd_linear_three (h : HasMathieuFixedComponent S)
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL S 3 q) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h.of_mulEquiv e
  have hr := Theory.SpecificGroups.OddThreeSectionRank.psl3_subgroup_quotient_twoRank_le_three
    (hF.symm ▸ ho) B (center B)
  rw [primeRank_equiv 2 b] at hr
  have hl := m22_four_le_twoRank
  omega

/-- The same section argument uses the actual Hermitian projective quotient. -/
theorem HasMathieuFixedComponent.not_odd_unitary_three (h : HasMathieuFixedComponent S)
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSU S 3 q) : False := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h.of_mulEquiv e
  have hr := Theory.SpecificGroups.OddThreeSectionRank.psu3_subgroup_quotient_twoRank_le_three
    J (hF.symm ▸ ho.pow) B (center B)
  rw [primeRank_equiv 2 b] at hr
  have hl := m22_four_le_twoRank
  omega

/-- Suzuki involution fixed groups are two-groups, hence have no components. -/
theorem HasMathieuFixedComponent.not_suzuki (h : HasMathieuFixedComponent S)
    {m : ℕ} (hm : 1 ≤ m) (e : S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  obtain ⟨a,ha,B,hB,hq⟩ := h.of_mulEquiv e
  let := (BenderSuzuki.MatrixGroups.suzuki_involution_fixed_isPGroup m hm a ha).isNilpotent
  let := hB.2.2
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hB.ne_bot
  let : Nontrivial (B.subgroupOf a.fixedSubgroup) :=
    (subgroupOfEquivOfLe hB.1).surjective.nontrivial
  exact Group.IsPerfect.not_isSolvable (B.subgroupOf a.fixedSubgroup) inferInstance

/-- Odd Sylow subgroups of binary PSL₂ are cyclic, as are their quotient images. -/
theorem HasMathieuFixedComponent.not_binary_linear_two (h : HasMathieuFixedComponent S)
    {n : ℕ} (hm : ClassicalGroup.IsPSL S 2 (2^n)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h.of_mulEquiv e
  let P : Sylow 3 B := Sylow.nonempty.some
  let j := (Theory.PSL2.sl2QuotientEquiv F).symm.toMonoidHom.comp
    (B.subtype.comp (P : Subgroup B).subtype)
  let : IsCyclic P := Matrix.SL2.odd_pGroup_isCyclic_of_injective P.isPGroup' (by decide) j
    ((Theory.PSL2.sl2QuotientEquiv F).symm.injective.comp
      (B.subtype_injective.comp (P : Subgroup B).subtype_injective))
  let f := b.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hf : Function.Surjective f := b.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hf
  let : IsCyclic Q := isCyclic_of_surjective (f.subgroupMap (P : Subgroup B))
    (f.subgroupMap_surjective _)
  have hr := Q.primeRank_le_one_of_isCyclic inferInstance
  rw [m22_primeRank_three] at hr
  omega

/-- Pullback to SL₂ preserves the literal Mathieu section; every image of
an odd-field GL₂ two-subgroup has two-rank at most three. -/
theorem HasMathieuFixedComponent.not_odd_linear_two (h : HasMathieuFixedComponent S)
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL S 2 q) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  have hodd : Odd (Nat.card F) := hF.symm ▸ ho
  have hfield : GorensteinWalter.IsOddPrimePower (Nat.card F) := by
    obtain ⟨n,hp,hn⟩ := FiniteField.card F (ringChar F)
    have hc : Nat.card F = ringChar F ^ (n : ℕ) := by
      simpa only [Nat.card_eq_fintype_card] using hn
    refine ⟨ringChar F,n,hp,?_,n.pos,hc⟩
    apply hp.odd_of_ne_two
    intro he
    have heven : Even (Nat.card F) := by
      rw [hc,he]
      exact Nat.even_pow.mpr ⟨by decide,n.pos.ne'⟩
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h.of_mulEquiv e
  let π := Theory.PSL2.quotientMap F
  let U := B.comap π
  let f : U →* M22 := b.toMonoidHom.comp
    ((QuotientGroup.mk' (center B)).comp (π.subgroupComap B))
  have hf : Function.Surjective f := b.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp
      (π.subgroupComap_surjective_of_surjective B (Theory.PSL2.quotientMap_surjective F)))
  let P : Sylow 2 U := Sylow.nonempty.some
  let j := Matrix.SpecialLinearGroup.toGL.comp (U.subtype.comp (P : Subgroup U).subtype)
  have hj : Function.Injective j := Matrix.SpecialLinearGroup.toGL_injective.comp
    (U.subtype_injective.comp (P : Subgroup U).subtype_injective)
  let Q := P.mapSurjective hf
  have hr := Theory.SpecificGroups.OddThreeSectionRank.gl2_twoGroup_image_twoRank_le_three
    hfield (Field.two_ne_zero_of_odd_card F hodd) P.isPGroup' j hj
    (f.subgroupMap (P : Subgroup U)) (f.subgroupMap_surjective _)
  change primeRank 2 Q ≤ 3 at hr
  rw [←Q.primeRank_eq] at hr
  have hl := m22_four_le_twoRank
  omega

open ChapterA.Section02 ClassificationModels

/-- The four odd rows not excluded by the linear and ternary section bounds. -/
@[expose] def RemainingMathieuOddModel (S : Type*) [Group S] : Prop :=
  (∃ p, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSp S 2 p) ∨
  (∃ p, p.Prime ∧ Odd p ∧ IsG2At S p) ∨
  (∃ p, p.Prime ∧ (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) ∧ ClassicalGroup.IsPSL S 4 p) ∨
  (∃ p, p.Prime ∧ (∃ b : ℕ, p + 1 = 2 ^ b) ∧ ClassicalGroup.IsPSU S 4 p)

/-- Remove all odd linear-two and ternary rows from Theorem B. -/
theorem HasMathieuFixedComponent.odd_rows (h : HasMathieuFixedComponent S)
    (hm : IsTheoremBOddModel S) : RemainingMathieuOddModel S := by
  cases hm with
  | linear_two q hq he => exact (h.not_odd_linear_two hq he).elim
  | linear_three p e hp ho he hm => exact (h.not_odd_linear_three ho.pow hm).elim
  | unitary_three p e hp ho he hm => exact (h.not_odd_unitary_three ho.pow hm).elim
  | symplectic p hp ho he => exact Or.inl ⟨p,hp,ho,he⟩
  | g2 p hp ho he => exact Or.inr (Or.inl ⟨p,hp,ho,he⟩)
  | linear_four p hp hf he => exact Or.inr (Or.inr (Or.inl ⟨p,hp,hf,he⟩))
  | unitary_four p hp hf he => exact Or.inr (Or.inr (Or.inr ⟨p,hp,hf,he⟩))

/-- Only the unitary rank-one family remains. -/
theorem HasMathieuFixedComponent.bender_rows (h : HasMathieuFixedComponent S)
    (hm : IsBenderModel S) : ∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSU S 3 (2 ^ n) := by
  cases hm with
  | linear n hn he => exact (h.not_binary_linear_two he).elim
  | unitary n hn he => exact ⟨n,hn,he⟩
  | suzuki n hn he => exact (h.not_suzuki hn he.some).elim

/-- Remaining proper overcomponents after the HS and small Lie-family exclusions. -/
@[expose] def RemainingMathieuReducedModel (S : Type*) [Group S] : Prop :=
  RemainingMathieuOddModel S ∨
    (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSU S 3 (2 ^ n)) ∨
    (∃ n, IsRankTwoModel S n) ∨ Nonempty (S ≃* Sporadic.LeechRelated.McL.Carrier)

/-- The reduced list retains genuine model equivalences for the same fixed component. -/
theorem HasMathieuFixedComponent.reduced_rows [IsSimpleGroup S] [Group.IsPerfect S]
    (h : HasMathieuFixedComponent S) (hm : IsTheoremBModel S) :
    RemainingMathieuReducedModel S := by
  rcases h.theoremB_rows hm with ho | hb | hr | hs | hmcl
  · exact Or.inl (h.odd_rows ho)
  · exact Or.inr (Or.inl (h.bender_rows hb))
  · exact Or.inr (Or.inr (Or.inl hr))
  · obtain ⟨e⟩ := hs
    let : IsSimpleGroup Sporadic.LeechRelated.HS.Carrier := e.symm.isSimpleGroup
    let : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact (no_mathieu_fixed_hs (h.of_mulEquiv e)).elim
  · exact Or.inr (Or.inr (Or.inr hmcl))

end CFSG.Quasithin.ChapterI.MathieuPumpup
