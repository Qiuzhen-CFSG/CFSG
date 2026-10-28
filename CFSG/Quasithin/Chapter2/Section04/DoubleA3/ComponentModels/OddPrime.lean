module
public import Theory.SpecificGroups.PSL2.CubicActorParameter
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActionNormalizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import GorensteinWalter.LinearRingEquiv
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.BenderOdd
/-!
# Odd-prime rows in the original paired-cubic component inspection

The actual first cubic block acts faithfully on the component. Its image
normalizer has index at most two in the prescribed Sylow automorphism
image. Intersecting the component normalizer's Sylow with the component
supplies an actual intrinsic Sylow; transport to the prime-field PSL₂ model
then reduces its Fermat–Mersenne parameter to 5, 7, 17; the marked binary-field comparison then excludes 5. The proof does not assume
that the block has already been absorbed into the component.

Source: Aschbacher–Smith, inspection preceding 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource

private theorem cubic_coreIn_kleinFour
    {X : Type*} [Group X] [Finite X] (B : Subgroup X) (hB : IsAlternatingBlock B 3) :
    IsKleinFour (B.pCoreIn 2) := by
  have hc : Nat.card (B ⧸ pCore 2 B) = 3 := by
    obtain ⟨e⟩ := hB.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hfour := hB.2.1.core_card_four_of_quotient_three hc
  let : IsElementaryAbelian 2 (pCore 2 B) := by
    rw [hB.2.1.core_eq_blockU_of_quotient_three hc]
    exact hB.2.1.elementary
  let : IsElementaryAbelian 2 (B.pCoreIn 2) := IsElementaryAbelian.map B.subtype
  have hcard : Nat.card (B.pCoreIn 2) = 4 := by
    change Nat.card ((pCore 2 B).map B.subtype) = 4
    rw [←Nat.card_congr ((pCore 2 B).equivMapOfInjective B.subtype B.subtype_injective).toEquiv]
    exact hfour
  let : Nontrivial (B.pCoreIn 2) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    let := hs
    have hh := Nat.card_of_subsingleton (1 : B.pCoreIn 2)
    omega
  exact ⟨hcard,IsElementaryAbelian.exponent_eq_prime⟩

/-- The prime parameter bound with a faithful literal cubic action, before
any assertion that the acting block lies in its component. -/
theorem prime_parameter_of_faithful_cubic_action
    {L K : Type*} [Group L] [Group K] [Finite L] [Finite K]
    (hL : IsAlternatingBlock L 3) {p k : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpk : p-1=2^k ∨ p+1=2^k)
    (e : K ≃* PSL(2,ZMod p)) (f : L →* MulAut K) (hf : Function.Injective f)
    (A : Subgroup (MulAut K)) (P : Sylow 2 K)
    (hPA : (P : Subgroup K).map MulAut.conj ≤ A)
    (hindex : (normalizer (f.range : Set (MulAut K))).relIndex A ≤ 2) :
    p=5 ∨ p=7 ∨ p=17 := by
  let eA := MulAut.congr e
  let f' := eA.toMonoidHom.comp f
  let A' := A.map eA.toMonoidHom
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hB : IsAlternatingBlock f'.range 3 :=
    hL.of_mulEquiv (MonoidHom.ofInjective (eA.injective.comp hf))
  let := cubic_coreIn_kleinFour f'.range hB
  have hPA' : (P' : Subgroup PSL(2,ZMod p)).map MulAut.conj ≤ A' := by
    rintro a ⟨u,hu,rfl⟩
    obtain ⟨v,hv,rfl⟩ := hu
    refine ⟨MulAut.conj v,hPA (mem_map_of_mem MulAut.conj hv),?_⟩
    ext x
    change e (v * e.symm x * v⁻¹) = e v * x * (e v)⁻¹
    simp only [map_mul,map_inv,e.apply_symm_apply]
  have hi' : (normalizer (f'.range : Set (MulAut PSL(2,ZMod p)))).relIndex A' ≤ 2 := by
    have hr : f'.range = f.range.map eA.toMonoidHom := (MonoidHom.map_range _ _).symm
    rw [hr,←map_equiv_normalizer_eq,relIndex_map_map_of_injective _ _ eA.injective]
    exact hindex
  exact Theory.PSL2.prime_parameter_of_cubic_actor_normalizer_index hp5 hpk
    f'.range A' hB.2.1.twoPerfect P' hPA' hi'

private theorem prime_model_ge_five
    {K : Type*} [Group K] [Group.IsPerfect K] {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hm : ClassicalGroup.IsPSL K 2 p) : 5 ≤ p := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases hp.2 with ⟨k,hk⟩ | ⟨k,hk⟩
    · have hh : 2 ≤ 2^(2^k) := Nat.le_pow (by positivity)
      omega
    · have hk0 : k ≠ 0 := by intro he; simp [he] at hk
      have hh := dvd_pow_self 2 hk0
      rw [←hk] at hh
      norm_num at hh
  have hp3 : p ≠ 3 := by
    rintro rfl
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three hF
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  have ho := hp.1.odd_of_ne_two hp2
  have hmin := hp.1.two_le
  obtain ⟨k,hk⟩ := ho
  omega

variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

/-- The odd-prime catalogue parameter in the original paired-cubic source
is 5, 7, or 17. The Sylow, faithfulness and normalizer bound are all actual. -/
theorem SourceCentralizerGeometry.odd_prime_component_parameter
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hm : ClassicalGroup.IsPSL K 2 p) :
    p=5 ∨ p=7 ∨ p=17 := by
  let H := involutionCentralizer g.z₂
  let N := normalizer (K : Set H)
  let L := d.block.map d.H.subtype
  have hLH : L ≤ H := g.first_block_le_second_centralizer
  have hLN : L.subgroupOf H ≤ N := g.first_block_normalizes_component hG K hK
  let j : L →* N := (inclusion hLN).comp (subgroupOfEquivOfLe hLH).symm.toMonoidHom
  let f := K.normalizerMonoidHom.comp j
  have hj : j.range = (L.subgroupOf H).subgroupOf N := by
    ext n
    constructor
    · rintro ⟨l,rfl⟩
      exact l.property
    · intro hn
      exact ⟨⟨(n:H),hn⟩,rfl⟩
  have hr : f.range = ((L.subgroupOf H).subgroupOf N).map K.normalizerMonoidHom := by
    rw [←hj]
    exact (MonoidHom.map_range _ _).symm
  obtain ⟨P,_,hindex⟩ := g.component_action_normalizer_bound hG K hK
  obtain ⟨P₀,hP₀⟩ := K.exists_sylow_inner_le_normalizer_image P
  obtain ⟨f₀,hf₀,hact₀⟩ := g.faithful_first_block_action hG h K hK
  have hff : f = f₀ := by
    ext l k
    exact (hact₀ l k).symm
  have hf : Function.Injective f := hff ▸ hf₀
  let : IsQuasisimple K := hK.2
  have hp5 := prime_model_ge_five hp hm
  let : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let e := e₀.trans (GorensteinWalter.psl2RingEquiv eF)
  obtain ⟨k,hk⟩ : ∃ k,p-1=2^k ∨ p+1=2^k := by
    rcases hp.2 with ⟨r,hr⟩ | ⟨r,hr⟩
    · exact ⟨2^r,Or.inl (by omega)⟩
    · exact ⟨r,Or.inr hr⟩
  exact prime_parameter_of_faithful_cubic_action c.cubic_first hp5 hk e f hf
    ((P : Subgroup N).map K.normalizerMonoidHom) P₀ hP₀ (hr.symm ▸ hindex)
/-- The actual inner-marked odd-prime row has parameter 7 or 17: parameter 5
is the already excluded binary four-field Bender model. -/
theorem SourceCentralizerGeometry.odd_prime_marked_parameter
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hm : ClassicalGroup.IsPSL K 2 p) :
    p=7 ∨ p=17 := by
  rcases g.odd_prime_component_parameter hG h K hK hp hm with hp5 | hp7 | hp17
  · subst p
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hz : center K = ⊥ := by
      apply (center K).eq_bot_iff_card.mpr
      rw [Nat.card_congr (centerCongr e).toEquiv,GorensteinWalter.psl2_center_eq_bot F,card_bot]
    have hb : ClassificationModels.IsBenderModel K := .linear 2 (by decide)
      ⟨GaloisField 2 2,inferInstance,inferInstance,
        GaloisField.card 2 2 (by decide),
        ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.cardFiveEquivFour hF)⟩⟩
    exact (g.bender_component_action_false hG h K hK α hα hinner hz hb).elim
  · exact Or.inl hp7
  · exact Or.inr hp17
end CFSG.Quasithin.Chapter2.DoubleA3
