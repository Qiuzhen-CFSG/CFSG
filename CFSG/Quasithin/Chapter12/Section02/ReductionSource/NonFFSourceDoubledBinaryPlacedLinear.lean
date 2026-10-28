module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedLinear
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedMathieu
public import Theory.GroupTheory.CentralCoverTwoLocalPlacement

/-!
# Removing PSL₅(2) from the original binary-three placed branch

The entire original component center is odd, so projection through that
center is injective on the whole marked natural--dual orbit. Its image and
the original odd-actor residual lie in an actual GL₅(2) parabolic. Residual
uniqueness places the full parabolic preimage in the original normalizer;
there it normalizes both residual and orbit. This supplies the relative
normality required by the linear-five exclusion, with no new source premise.

The remaining placed models are PSp₆(2), J₄, He and Ru. The same component,
whole orbit, residual section and full central quotient are retained, as is
the separate maximal pushing-up alternative in the original H-star
application. These remaining cases and binary centralizer geometry are
still needed for odd-normalizer control and the doubled contradiction.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, as used in 7.3.4
and 7.6.1, pp.699,702, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open BinaryLinearThree
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original placed component has no PSL₅(2) central quotient. The full
center is retained; its odd order makes the whole orbit inject into the quotient. -/
theorem sourceOrbit_binary_oddNormalizer_not_linear_five
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hcent : centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G))) :
    ¬ ClassicalGroup.IsPSL (K ⧸ center K) 5 2 := by
  rintro ⟨k,_,_,hk,⟨mk⟩⟩
  let := Fintype.ofFinite k
  let ak : k ≃+* ZMod 2 := (ZMod.ringEquivOfPrime k Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hk)).symm
  let m := mk.trans ((Atlas.fieldEquivPSL 5 ak).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5)))
  let R := oddActorResidual L A
  let N := normalizer (A : Set G)
  let W := D.sourceOrbit
  let a : K.map N.subtype ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let i : R →* K := a.toMonoidHom.comp (inclusion hr)
  have hi : Function.Injective i := a.injective.comp (inclusion_injective hr)
  obtain ⟨_,_,hWR,t,ht,hnt,q,hq,hker,e,he,E,hE,hV,hVt⟩ :=
    D.sourceOrbit_binary_odd_residual_coordinates h hd F hF hmodel A hAC ho
  have hWR' : W ≤ R := hWR.trans (pCoreIn_le 2 R)
  let iW : W →* K := i.comp (inclusion hWR')
  have hiW : Function.Injective iW := hi.comp (inclusion_injective hWR')
  have hZC : (center K).map K.subtype ≤ centralizer (K : Set N) := by
    rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg K.subtype (mem_center_iff.mp hz ⟨y,hy⟩)
  have hoC : Odd (Nat.card (centralizer (K : Set N))) := by
    rw [hcent]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hoZ : Odd (Nat.card (center K)) := by
    have hh := hoC.of_dvd_nat (card_dvd_of_le hZC)
    rwa [card_map_of_injective K.subtype_injective] at hh
  let π := QuotientGroup.mk' (center K)
  have hπ : Nat.Coprime 2 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact hoZ.coprime_two_left
  have hp : IsPGroup 2 iW.range := (IsElementaryAbelian.isPGroup 2 W).of_surjective
    iW.rangeRestrict iW.rangeRestrict_surjective
  have hiπ : Function.Injective (π.comp iW) := by
    have hh := injective_comp_subtype_of_coprime_ker π hπ iW.range hp
    intro x y he
    apply hiW
    exact congrArg Subtype.val (hh (show (π.comp iW.range.subtype) (iW.rangeRestrict x) =
      (π.comp iW.range.subtype) (iW.rangeRestrict y) from he))
  let v : Multiplicative NaturalDual.Space ≃* W :=
    E.symm.toAddEquiv.toMultiplicative.trans (MulEquiv.toMultiplicative_toAdditive)
  let f := m.toMonoidHom.comp (π.comp i)
  let j := m.toMonoidHom.comp ((π.comp iW).comp v.toMonoidHom)
  have hj : Function.Injective j := m.injective.comp (hiπ.comp v.injective)
  let qR := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hqR : Function.Surjective qR := e.surjective.comp (QuotientGroup.mk'_surjective _)
  apply DoubledBinaryPlacedLinear.no_linear_five_natural_dual f qR hqR j hj
  · intro r x
    have hact : doubledSeedAction R W
        (((oddActorResidual_le L A).trans inf_le_left).trans
          D.sourceOrbit_component_normalizes) r (E.symm x) =
        E.symm (NaturalDual.action (qR r) x) := by
      apply E.injective
      rw [hE,E.apply_symm_apply,E.apply_symm_apply]
      rfl
    have hh : r * inclusion hWR' (v (Multiplicative.ofAdd x)) * r⁻¹ =
        inclusion hWR' (v (Multiplicative.ofAdd (NaturalDual.action (qR r) x))) :=
      Subtype.ext (congrArg (fun w : Additive W => (w.toMul : G)) hact)
    have hf := congrArg f hh
    simp only [map_mul,map_inv] at hf
    exact hf
  · intro b d hBP
    let P := BinaryLinear.FiveFlagGeometry.flagStabilizer b {d}
    let K₀ := K.map N.subtype
    let π₀ := m.toMonoidHom.comp (π.comp a.toMonoidHom)
    have hπ₀ : Function.Surjective π₀ := m.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp a.surjective)
    have hker₀ : π₀.ker ≤ center K₀ := by
      intro z hz
      have hzK : a z ∈ center K := (QuotientGroup.eq_one_iff _).mp
        (m.injective (hz.trans (map_one m).symm))
      apply mem_center_iff.mpr
      intro y
      apply a.injective
      simpa only [map_mul] using mem_center_iff.mp hzK (a y)
    have hfP : (π₀.comp (inclusion hr)).range ≤ P := hBP
    have hPM : (P.comap π₀).map K₀.subtype ≤ normalizer (L : Set G) :=
      central_preimage_le_of_unique_maximalTwoLocal hr hu.2.2 π₀ hπ₀ hker₀ P
        (BinaryLinear.radical (BinaryLinear.FiveFlagGeometry.flagSpace b d))
        (BinaryLinear.radical_two _)
        (BinaryLinear.radical_ne_bot (BinaryLinear.FiveFlagGeometry.flagSpace_ne_bot b d)
          (BinaryLinear.FiveFlagGeometry.flagSpace_ne_top b d))
        (by dsimp only [P]; rw [BinaryLinear.FiveFlagGeometry.flagStabilizer_singleton]
            exact BinaryLinear.parabolic_le_normalizer _) hfP
    have hPKN : (P.comap π₀).map K₀.subtype ≤ N :=
      (map_subtype_le _).trans (map_subtype_le K)
    have hBR : (f.range.subgroupOf P).Normal :=
      image_normal_in_of_preimage_normalizes hr π₀ hπ₀ P hfP
        ((le_inf hPM hPKN).trans (normalizes_oddActorResidual L A))
    have hWK : W ≤ K₀ := hWR'.trans hr
    let wq := π₀.comp (inclusion hWK)
    have hwj : wq.range = j.range := by
      apply le_antisymm
      · rintro _ ⟨w,rfl⟩
        obtain ⟨x,rfl⟩ := v.surjective w
        exact ⟨x,rfl⟩
      · rintro _ ⟨x,rfl⟩
        exact ⟨v x,rfl⟩
    have hwP : wq.range ≤ P := by
      rintro _ ⟨w,rfl⟩
      exact hfP ⟨inclusion hWR' w,rfl⟩
    have hnormW : (P.comap π₀).map K₀.subtype ≤ normalizer (W : Set G) :=
      hPM.trans (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge
    have hWN := image_normal_in_of_preimage_normalizes hWK π₀ hπ₀ P hwP hnormW
    rw [hwj] at hwP hWN
    exact ⟨hBR,hwP,hWN⟩

/-- The remaining placed component with residual uniqueness retained. -/
@[expose] def BinaryPlacedNonLinearCase (A : Subgroup G) : Prop :=
  UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 p) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 p)) ∧
    (∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 (p^2)) ∧
      (¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 (p^2))) ∧
    (K.Normal ∧ D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
      6 ≤ primeRank 2 (K ⧸ center K) ∧
      ¬ ChapterA.Section02.IsTheoremBOddModel (K ⧸ center K) ∧
      DoubledBinaryPlacedLocals.LocalData (K ⧸ center K) ∧
      (ClassicalGroup.IsPSp (K ⧸ center K) 3 2 ∨
        ∃ name : ClassificationModels.SporadicName,
          (name = .j4 ∨ name = .he ∨ name = .ru) ∧
          Nonempty ((K ⧸ center K) ≃* name.Carrier)) ∧
      (∀ p : ℕ, (∃ k : ℕ, p = 2 ^ (2 ^ k) + 1) →
        ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 p) ∧
      ∃ j : oddActorResidual L A →* K ⧸ center K, IsPGroup 2 j.ker ∧
        ∃ f : j.range →* BinaryLinearThree.Group, Function.Surjective f)

private theorem binary_placed_nonLinear_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hc : D.BinaryPlacedNonMathieuCase A) : D.BinaryPlacedNonLinearCase A := by
  obtain ⟨K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,
    hn,hW,hR,hC,hrank,hodd,hl,hrem,hfour,j,hj,f,hf⟩ := hc
  refine ⟨hu,K,hK,hm,hout,hcore,hmodels,h2,h3,hsquare,
    hn,hW,hR,hC,hrank,hodd,hl,?_,hfour,j,hj,f,hf⟩
  rcases hrem with hlin | hrem
  · exact (D.sourceOrbit_binary_oddNormalizer_not_linear_five h hd F hF hmodel
      A hAC ho K hR hu hC hlin).elim
  · exact hrem

/-- Four models remain in the original placed branch, without a new model premise. -/
theorem sourceOrbit_binary_oddNormalizer_placed_nonLinear
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    D.BinaryPlacedNonLinearCase A := by
  exact D.binary_placed_nonLinear_reduction h hd F hF hmodel A hAC ho hu
    (D.sourceOrbit_binary_oddNormalizer_placed_nonMathieu h hd F hF hmodel A hne hAC ho hu hout)

/-- The linear-five exclusion on the same original H-star actor and component.
The independent maximal pushing-up alternative is retained literally. -/
theorem sourceOrbit_binary_globalW_or_placed_nonLinear_oddLocal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ChapterE.globalW D.sourceOrbit T ≤ 1 ∨
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ((∃ J P : Subgroup G,
          J ∈ muStar (normalizer (L : Set G)) L
            (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
          PushLE L (oddActorResidual L A) J ∧
          IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
          IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
        D.BinaryPlacedNonLinearCase A) := by
  rcases D.sourceOrbit_binary_globalW_or_odd_escape h hd hmany hnon F hF hmodel with hw | hx
  · exact Or.inl hw
  obtain ⟨H,hH,_,p,hp,hpo,A,hAH,hAC,hcard,hout⟩ := hx
  refine Or.inr ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,?_⟩
  have ho : Odd (Nat.card A) := hcard.symm ▸ hpo
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · apply Or.inr
    let : Fact p.Prime := ⟨hp⟩
    let : IsCyclic A := isCyclic_of_prime_card hcard
    have hne : A ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hcard
      have := hp.one_lt
      omega
    exact D.sourceOrbit_binary_oddNormalizer_placed_nonLinear h hd F hF hmodel A hne hAC ho hu
      (fun he => hout (inf_le_right.trans he))
  · apply Or.inl
    have hA : A ≤ normalizer (L : Set G) ⊓
        centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
      rw [←D.sourceOrbit_eq]
      exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
    simpa only [←D.sourceOrbit_eq] using D.doubledOrbit_oddNormalizer_pushingUp h A hA ho hu

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
