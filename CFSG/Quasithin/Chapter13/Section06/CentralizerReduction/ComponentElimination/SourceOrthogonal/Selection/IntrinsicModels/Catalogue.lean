module

public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.IntrinsicModels.Quotients
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.FixedModels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.SmallUnitary
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Theory.Mathieu.M22.Properties.Order

/-!
# The A.3.6 catalogue above SL₄(2)

A surjection from a C-component satisfying the complete A.3.6 conclusion
onto SL₄(2) is injective. The simple branch follows from simplicity. In a
three-cover the kernel is exactly the center, so its actual central quotient
must be SL₄(2). Odd classical quotients are excluded by defining-prime cubes;
even linear quotients by Sylow-center orders (also separating PSL₃(4)); and
even unitary quotients by root orders, the source congruence and solvability
of SU₃(2). The alternating and Mathieu quotients have different orders.

In the natural and nilpotent branches the solvable Fitting subgroup is
killed by the given map. The quasisimple SL₂(p) quotient would then have
central quotient of order 20160, contradicting its order formula. This uses
no center–Frattini assertion. The final consumer applies the comparison in
the literal ambient two-core quotient and retains the original map on
representatives. Universal A.3.6 remains an explicit earlier-source input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6,
printed pp.43–45, used in 13.6.23, printed p.933/PDF p.950. Imported
ATLAS model comparisons retain their attribution and license.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open BenderSuzuki.MatrixGroups
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
universe u
namespace Catalogue

private instance four_simple : IsSimpleGroup SL(4, ZMod 2) := by
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  exact (Atlas.Order20160A8.sl4TwoEquivPSL.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).isSimpleGroup

private theorem four_center : center SL(4, ZMod 2) = ⊥ := by
  apply (Subgroup.eq_bot_iff_card _).mpr
  rw [Atlas.ExceptionalSupport.card_sl_center]
  norm_num

private theorem surjective_ker_ne_top {H : Type*} [Group H]
    (f : H →* SL(4, ZMod 2)) (hf : Function.Surjective f) : f.ker ≠ ⊤ := by
  intro h
  have htriv : ∀ y : SL(4, ZMod 2), y = 1 := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact h.ge (mem_top x)
  obtain ⟨y, hy⟩ := exists_ne (1 : SL(4, ZMod 2))
  exact hy (htriv y)

private theorem simple_injective {H : Type*} [Group H] [IsSimpleGroup H]
    (f : H →* SL(4, ZMod 2)) (hf : Function.Surjective f) : Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance).resolve_right
    (surjective_ker_ne_top f hf)

/-- Identify the kernel of the given epimorphism, rather than an arbitrary
simple section of the covering group. -/
private def centralQuotientEquiv {H : Type*} [Group H] [IsQuasisimple H]
    (f : H →* SL(4, ZMod 2)) (hf : Function.Surjective f) :
    (H ⧸ center H) ≃* SL(4, ZMod 2) := by
  have hk : f.ker = center H := by
    apply le_antisymm
    · exact (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
        (surjective_ker_ne_top f hf)
    · intro x hx
      have hz : f x ∈ center SL(4, ZMod 2) := by
        rw [mem_center_iff]
        intro y
        obtain ⟨y, rfl⟩ := hf y
        simpa only [map_mul] using congrArg f (mem_center_iff.mp hx y)
      simpa only [four_center, mem_bot, MonoidHom.mem_ker] using hz
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

private def centerQuotientCongr {H J : Type*} [Group H] [Group J] (e : H ≃* J) :
    (H ⧸ center H) ≃* (J ⧸ center J) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro y hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩)

/-- A solvable normal subgroup is killed by the literal map to the simple
perfect binary linear group. -/
private theorem solvable_le_ker {H : Type*} [Group H] [Group.IsPerfect H]
    (N : Subgroup H) [N.Normal] [Group.IsSolvable N]
    (f : H →* SL(4, ZMod 2)) (hf : Function.Surjective f) : N ≤ f.ker := by
  let : Group.IsPerfect SL(4, ZMod 2) := Group.IsPerfect.ofSurjective hf
  let : (N.map f).Normal := (inferInstance : N.Normal).map f hf
  have he : N.map f = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) inferInstance with h | h
    · exact h
    · let : Group.IsSolvable (N.map f) := Group.isSolvable_of_surjective
        (f := f.subgroupMap N) (f.subgroupMap_surjective N)
      have ht : Group.IsSolvable (⊤ : Subgroup SL(4, ZMod 2)) := h ▸ inferInstance
      let := ht
      let : Group.IsSolvable SL(4, ZMod 2) :=
        Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup SL(4, ZMod 2)) ≃*
          SL(4, ZMod 2)).toMonoidHom) topEquiv.surjective
      exact (Group.IsPerfect.not_isSolvable SL(4, ZMod 2) inferInstance).elim
  exact (Subgroup.map_eq_bot_iff _).mp he

/-- The SL₂ quotient in both radical alternatives cannot map onto SL₄(2). -/
private theorem not_sl2_surjection {H : Type*} [Group H] [IsQuasisimple H]
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p) (hm : IsSL H 2 p)
    (f : H →* SL(4, ZMod 2)) (hf : Function.Surjective f) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let d := (centerQuotientCongr e).symm.trans (centralQuotientEquiv f hf)
  have hcard : Nat.card (SL(2, F) ⧸ center SL(2, F)) = 20160 :=
    (Nat.card_congr d.toEquiv).trans Atlas.Order20160A8.sl4Two_card
  have hc := (center SL(2, F)).card_eq_card_quotient_mul_card_subgroup
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
    hcard, Atlas.ExceptionalSupport.card_sl_center, hF] at hc
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hg : Nat.gcd 2 (p - 1) = 2 :=
    Nat.gcd_eq_left_iff_dvd.mpr (by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩)
  simp only [Fintype.card_fin, hg] at hc
  by_cases h : p ≤ 34
  · have hs : p ^ 2 ≤ 34 ^ 2 := Nat.pow_le_pow_left h 2
    have hm := Nat.mul_le_mul h (Nat.sub_le_sub_right hs 1)
    norm_num at hm
    omega
  · have hl : 35 ≤ p := by omega
    have hs : 35 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hl 2
    have hm := Nat.mul_le_mul hl (Nat.sub_le_sub_right hs 1)
    norm_num at hm
    omega

/-- Both actual Fitting-quotient cases reduce to the preceding SL₂ comparison. -/
private theorem radical_alternative_impossible {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] (hcommon : A36Common H)
    (heq : generalizedFitting H = fittingSubgroup H)
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hm : IsSL (H ⧸ generalizedFitting H) 2 p)
    (f : H →* SL(4, ZMod 2)) (hf : Function.Surjective f) : False := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hm
  have hmodel : IsSL (H ⧸ fittingSubgroup H) 2 p :=
    ⟨F, hfield, hfinite, hF,
      ⟨(QuotientGroup.quotientMulEquivOfEq heq).symm.trans e⟩⟩
  let : IsQuasisimple (H ⧸ fittingSubgroup H) := hcommon.2.1
  let q := QuotientGroup.lift (fittingSubgroup H) f
    (solvable_le_ker (fittingSubgroup H) f hf)
  exact not_sl2_surjection hp hlarge hmodel q
    (QuotientGroup.lift_surjective_of_surjective _ _ hf _)


/-- The even linear cover is distinguished by the center of an actual Sylow
subgroup, including the equal-order PSL₃(4) case. -/
private theorem even_linear_impossible {H : Type*} [Group H] [IsQuasisimple H]
    {n : ℕ} (hn : 1 ≤ n) (hm : (2 ^ n) % 3 = 1)
    (hmodel : IsSL H 3 (2 ^ n))
    (f : H →* SL(4, ZMod 2)) (hf : Function.Surjective f) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let d := (centralQuotientEquiv f hf).symm.trans (centerQuotientCongr e)
  let S : Sylow 2 SL(4, ZMod 2) := Classical.choice inferInstance
  have hc := Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F
    (by omega : 0 < n) hF d S
  have hb := BinaryLinear.sl_sylow_center_card_le_two (by decide : 2 ≤ 4) S
  rw [hc] at hb
  have hpos : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  have he : 2 ^ n = 2 := by omega
  rw [he] at hm
  norm_num at hm

/-- The quadratic coefficient field and the fixed field remain distinct in
the unitary quotient comparison. -/
private theorem even_unitary_impossible {H : Type*} [Group H] [IsQuasisimple H]
    {n : ℕ} (hn : 1 ≤ n) (hm : (2 ^ n) % 3 = 2)
    (hmodel : IsSU H 3 (2 ^ n))
    (f : H →* SL(4, ZMod 2)) (hf : Function.Surjective f) : False := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hmodel
  have hz := HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hF hconj
  have hk := J.specialToProjective_ker_eq_center hz
  let d : (H ⧸ center H) ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    (centerQuotientCongr e).trans
      ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
          J.specialToProjective_surjective))
  have hcard : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 20160 :=
    (Nat.card_congr (d.symm.trans (centralQuotientEquiv f hf)).toEquiv).trans
      Atlas.Order20160A8.sl4Two_card
  have hd := HermitianForm.BinarySylowOrder.cube_dvd_card_projective J (by omega) hF hconj
  rw [hcard, ← pow_mul] at hd
  have hsmall : n ≤ 2 := by
    by_contra hnlarge
    have hdiv : 2 ^ 9 ∣ 20160 := (Nat.pow_dvd_pow 2 (by omega : 9 ≤ n * 3)).trans hd
    norm_num at hdiv
  have hcases : n = 1 ∨ n = 2 := by omega
  rcases hcases with rfl | rfl
  · exact Chapter13.Section08.Components.CoverModels.ClassicalParameters.not_su3_two
      ⟨F, inferInstance, inferInstance, J, hF, hconj, ⟨e⟩⟩
  · norm_num at hm

/-- All four genuine central-cover model alternatives are excluded. -/
private theorem threeCover_impossible {H : Type*} [Group H] [IsQuasisimple H]
    (hmodel : ThreeCoverModel H)
    (f : H →* SL(4, ZMod 2)) (hf : Function.Surjective f) : False := by
  let d := centralQuotientEquiv f hf
  cases hmodel with
  | classical unitary q hq hmodel =>
    rcases hq with ⟨n, hn, rfl, hm⟩ | ⟨hp, ho⟩
    · cases unitary with
      | false => exact even_linear_impossible hn hm hmodel f hf
      | true => exact even_unitary_impossible hn hm hmodel f hf
    · have hs := Chapter13.Section08.Components.CoverModels.ClassicalParameters.quotient_isPSLSign
        hp ho hmodel
      apply Chapter13.Section08.Components.CoverModels.ClassicalParameters.odd_projective_not_binary
        hp ho hs (Or.inl rfl : 4 = 4 ∨ 4 = 5)
      exact ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
        ⟨d.trans Atlas.Order20160A8.sl4TwoEquivPSL⟩⟩
  | alternating_six hm =>
    obtain ⟨e⟩ := hm.2.2
    have hc := Nat.card_congr (e.symm.trans d).toEquiv
    rw [Atlas.Order20160A8.sl4Two_card, Nat.card_eq_fintype_card, card_alternatingGroup] at hc
    norm_num at hc
  | alternating_seven hm =>
    obtain ⟨e⟩ := hm.2.2
    have hc := Nat.card_congr (e.symm.trans d).toEquiv
    rw [Atlas.Order20160A8.sl4Two_card, Nat.card_eq_fintype_card, card_alternatingGroup] at hc
    norm_num at hc
  | mathieu hm =>
    obtain ⟨e⟩ := hm.2.2
    have hc := Nat.card_congr (e.symm.trans d).toEquiv
    rw [Atlas.Order20160A8.sl4Two_card, Sporadic.Mathieu.m22_order] at hc
    norm_num at hc

end Catalogue

/-- A.3.6 has no nonsimple C-component with a quotient SL₄(2). -/
theorem a36RankFourRecognition : A36RankFourRecognition.{u} := by
  intro X _ _ B hB hA f hf
  let : Group.IsPerfect B := hB.perfect
  rcases hA with ⟨halt, hcommon⟩
  cases halt with
  | simple hc hs hm =>
    let := hs
    exact Catalogue.simple_injective f hf
  | cover hc hz hm =>
    let : IsQuasisimple B := hc.2
    exact (Catalogue.threeCover_impossible hm f hf).elim
  | natural h =>
    obtain ⟨p, hp, hlarge, F, hfield, hfinite, hF, v, e, haction⟩ := h.2
    exact (Catalogue.radical_alternative_impossible hcommon h.1 hp hlarge
      ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ f hf).elim
  | nilpotent h =>
    exact (Catalogue.radical_alternative_impossible hcommon h.1 (by decide : Nat.Prime 5)
      (by decide) h.2.2.1 f hf).elim

/-- Apply the proved catalogue comparison to the literal C-component image
used by `cComponentFourEquiv`. Only the universal earlier A.3.6 theorem remains
as a source input; the representative formula retains the supplied action map. -/
theorem exists_cComponentFourEquiv_of_a36 {G : Type u} [Group G] [Finite G]
    {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → A36Conclusion B)
    (hG : IsSQTK 𝒦 G) (B : Subgroup G) (hB : B.IsCComponent)
    (f : B →* SL(4, ZMod 2)) (hf : Function.Surjective f) :
    ∃ e : B ⧸ pCore 2 B ≃* SL(4, ZMod 2),
      ∀ b : B, e (QuotientGroup.mk' _ b) = f b := by
  let : Group.IsPerfect B := hB.perfect
  let : Group.IsPerfect SL(4, ZMod 2) := Group.IsPerfect.ofSurjective hf
  let := pCore_isNilpotent (p := 2) (G := SL(4, ZMod 2))
  have hcore : pCore 2 SL(4, ZMod 2) = ⊥ := by
    apply bot_unique
    simpa using Catalogue.solvable_le_ker (pCore 2 SL(4, ZMod 2))
      (MonoidHom.id SL(4, ZMod 2)) Function.surjective_id
  exact ⟨cComponentFourEquiv hA36 a36RankFourRecognition hG B hB f hf hcore,
    cComponentFourEquiv_mk hA36 a36RankFourRecognition hG B hB f hf hcore⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection

