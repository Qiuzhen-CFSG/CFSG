module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticOddInner
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticQuotient
public import Theory.SpecificGroups.PSL2.QuinticTwoPerfect

/-!
# The whole original quintic image in an odd linear-two carrier

The original two-perfect residual acts inside the actual inner subgroup.
Its nontrivial action retains its prime two-core quotient. Transport to the
literal odd-field PSL₂ model then kills its two-core. Thus the entire
original action image, rather than only its chosen complement, has order five.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

private theorem image_five_quotient {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hp : IsPPerfect 2 A)
    (hfive : Nat.card (A ⧸ pCore 2 A) = 5) (hne : Nat.card B ≠ 1) :
    Nat.card (B ⧸ pCore 2 B) = 5 := by
  have hle : (pCore 2 A).map f ≤ pCore 2 B :=
    le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  let q := QuotientGroup.map (pCore 2 A) (pCore 2 B) f (map_le_iff_le_comap.mp hle)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective _ b
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨QuotientGroup.mk' _ a,rfl⟩
  have hc : Nat.card (B ⧸ pCore 2 B) ∣ 5 := hfive ▸ card_dvd_of_surjective q hq
  rcases (Nat.dvd_prime Nat.prime_five).mp hc with hc | hc
  · have ht : pCore 2 B = ⊤ := index_eq_one.mp hc
    have hB : IsPGroup 2 B := pCore_isPGroup.of_surjective
      ((MulEquiv.subgroupCongr ht).trans topEquiv).toMonoidHom
      ((MulEquiv.subgroupCongr ht).trans topEquiv).surjective
    have hz := hp.hom_eq_one_of_isPGroup hB f
    have hr : (⊤ : Subgroup B) = ⊥ := by
      rw [←f.range_eq_top_of_surjective hf,hz]
      simp
    apply (hne _).elim
    have he := congrArg (fun U : Subgroup B => Nat.card U) hr
    simpa using he
  · exact hc

variable {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The entire action of the original X on its odd linear-two component
carrier has order five; the original two-core acts trivially there. -/
theorem original_hermitian_quintic_odd_linear_image_card
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p d : ℕ) (hp : p.Prime) (ho : Odd p) (hd : d = 1 ∨ d = 2)
    (hc : ClassicalGroup.IsPSL (coreCentralQuotient K) 2 (p^d)) :
    Nat.card (coreCentralActorImage K (quinticResidual T L)) = 5 := by
  let X := quinticResidual T L
  let C := coreCentralQuotient K
  let Y := coreCentralActorImage K X
  let N := normalizer (K : Set G)
  have hXN : X ≤ N := original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  let ex := (subgroupOfEquivOfLe hXN).symm
  let f : X →* Y := ((normalizerCoreCentralAction K).subgroupMap (X.subgroupOf N)).comp
    ex.toMonoidHom
  have hf : Function.Surjective f :=
    ((normalizerCoreCentralAction K).subgroupMap_surjective _).comp ex.surjective
  have hpY : IsPPerfect 2 Y := (quinticResidual_twoPerfect T L).of_surjective f hf
  obtain ⟨D,hD,_,hDX,_,_,_⟩ := original_hermitian_quintic_torus h hout hm
  have hDimage := original_hermitian_quintic_central_image_card h hout hm hM₁ hCM₁ hK hnot hq D hD hDX
  have hDY : coreCentralActorImage K D ≤ Y := map_mono (subgroupOf_mono N hDX)
  have hYne : Nat.card Y ≠ 1 := by
    intro he
    have hh := card_dvd_of_le hDY
    rw [hDimage,he] at hh
    norm_num at hh
  have hYfive := image_five_quotient f hf (quinticResidual_twoPerfect T L)
    (original_hermitian_quintic_core_quotient h hout hm).2 hYne
  have hinner : Y ≤ MulAut.innerSubgroup C :=
    original_hermitian_quintic_odd_linear_inner h hout hm hM₁ hCM₁ hK p d hp ho (by omega) hc
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
  have hz : center C = ⊥ := by
    apply bot_unique
    intro x hx
    have he := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) at he
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at he
    exact e.injective (he.trans e.map_one.symm)
  let ec : C ≃* MulAut.innerSubgroup C :=
    MonoidHom.ofInjective (conj_injective_of_center_eq_bot hz)
  let em := ec.symm.trans e
  let R := (Y.subgroupOf (MulAut.innerSubgroup C)).map em.toMonoidHom
  let er : Y ≃* R := (subgroupOfEquivOfLe hinner).symm.trans
    ((Y.subgroupOf (MulAut.innerSubgroup C)).equivMapOfInjective em.toMonoidHom em.injective)
  have hpR : IsPPerfect 2 R := hpY.of_surjective er.toMonoidHom er.surjective
  have hRfive : Nat.card (R ⧸ pCore 2 R) = 5 := by
    rw [←Nat.card_congr (QuotientGroup.congr _ _ er (pCore_map_iso 2 er)).toEquiv]
    exact hYfive
  have hR := Theory.PSL2.odd_twoPerfect_quintic_subgroup
    ⟨p,d,hp,ho,by omega,hF⟩ R hpR hRfive
  exact (Nat.card_congr er.toEquiv).trans hR.2

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
