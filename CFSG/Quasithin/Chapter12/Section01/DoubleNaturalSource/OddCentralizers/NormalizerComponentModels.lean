module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerPlacement
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.LocalModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterModels

/-!
# The remaining degree-five odd-normalizer components

When the actual fixed residual lies in K, its image in K/Z(K) has a
two-group kernel. Thus it retains cubic rank two and a factor of 31,
and normalizes the nontrivial image of the original chosen seed. These
are exactly the mathematical inputs of the already proved parabolic
exclusions; no exterior-square action marking is used. Together with the
full doubled orbit's two-rank ten, the complete B catalogue leaves J₄.

If the residual acts outer, its actual GL₅(2) section transports to the
proved outer-section exclusions. Seven remaining model families are
retained with their genuine group identifications. The original
DoubleNaturalExcludedOddNormalizers consumer constructs this alternative
without an odd-normalizer callback. Neither the J₄ configuration nor the
remaining outer section is excluded here.
Source: Aschbacher--Smith, 4.4.10--12 and 12.1.9(1), pp.621--623,793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open Chapter12.Section05.NaturalSource

/-- The surviving alternatives retain the same literal component and full orbit. -/
@[expose] def FiveNormalizerComponentCases {G : Type*} [Group G]
    (L W A : Subgroup G) (K : Subgroup (normalizer (A : Set G))) : Prop :=
((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* LinearGroup 5,
      Function.Surjective f) ∧ ExteriorRemainingOuterModel (K ⧸ center K)) ∨
    (K.Normal ∧ W ≤ K.map (normalizer (A : Set G)).subtype ∧
      Chapter4.Section04.oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model))

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  {n : ℕ} (B : DoubledBranch T L V n)
include D h B

open Chapter12.Section05.NaturalSource
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
omit D h B in
private theorem central_kernel_le_twoCore
    {F K : Type*} [Group F] [Finite F] [Group K]
    (e : (F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group)
    (j : F →* K) (hj : Function.Injective j) :
    ((QuotientGroup.mk' (center K)).comp j).ker ≤ pCore 2 F := by
  let S := Representation.SL5TenDimensional.Group
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup S := Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
  let : Group.IsPerfect S := Atlas.sl_perfect 5 (by decide)
  have hz : center S = ⊥ := by
    rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp ht)).elim
  let π : F →* S := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  intro x hx
  have hc : j x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  have hcx : x ∈ center F := mem_center_iff.mpr (fun y => hj (by
    simpa only [map_mul] using mem_center_iff.mp hc (j y)))
  have hcπ : π x ∈ center S := mem_center_iff.mpr (by
    intro y
    obtain ⟨z,rfl⟩ := hs y
    simpa only [map_mul] using congrArg π (mem_center_iff.mp hcx z))
  have he : π x = 1 := by simpa only [hz, mem_bot] using hcπ
  apply (QuotientGroup.eq_one_iff x).mp
  exact e.injective (he.trans (map_one e).symm)


omit B in
/-- The original residual has a perfect image of cubic rank two and order
divisible by 31, normalizing the nontrivial image of the original seed. -/
theorem doubledFive_oddNormalizer_placed_local (B : DoubledBranch T L V 5)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    ExteriorComponentLocalData (K ⧸ center K) := by
  let F := oddActorResidual L A
  let N := normalizer (A : Set G)
  let k := K.equivMapOfInjective N.subtype N.subtype_injective
  let j : F →* K := k.symm.toMonoidHom.comp (inclusion hFK)
  have hj : Function.Injective j := k.symm.injective.comp (inclusion_injective hFK)
  let f := (QuotientGroup.mk' (center K)).comp j
  obtain ⟨_, hmove, hVF, _⟩ := chosen_oddActorResidual_cover h.toHypothesis1221 D A (hA.trans inf_le_left)
    ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T)))
  have hVF' : V ≤ F := hVF.trans (pCoreIn_le 2 F)
  let W := V.subgroupOf F
  have hFW : F ≤ normalizer (V : Set G) :=
    ((oddActorResidual_le L A).trans inf_le_left).trans D.normalizes
  have hn : (⊤ : Subgroup F) ≤ normalizer (W : Set F) := by
    intro x _ y
    exact hFW x.property (y : G)
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let := D.elementary
  have hP : IsPGroup 2 (W.map f) := (IsElementaryAbelian.isPGroup 2 V).comap_subtype.map f
  have hne : W.map f ≠ ⊥ := by
    intro hb
    have hk := (map_eq_bot_iff W).mp hb
    have hc : V ≤ centralizer (F : Set G) := by
      intro v hv y hy
      have hz : j (⟨v,hVF' hv⟩ : F) ∈ center K :=
        (QuotientGroup.eq_one_iff _).mp (hk hv)
      have he : (⟨y,hy⟩ : F) * ⟨v,hVF' hv⟩ = ⟨v,hVF' hv⟩ * (⟨y,hy⟩ : F) :=
        hj (by simpa only [map_mul] using mem_center_iff.mp hz (j ⟨y,hy⟩))
      exact congrArg Subtype.val he
    exact D.ne_bot (hmove.trans (commutator_eq_bot_iff_le_centralizer.mpr hc))
  obtain ⟨e₀,_⟩ := D.doubledOrbit_oddActorResidual_marking h B A hA ho
  let e := e₀.trans ((projectiveEquivLinear (by decide : 0 < 5)).symm.trans
    Representation.SL5TenDimensional.projectiveEquiv.symm)
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.to_le (central_kernel_le_twoCore e j hj)
  have hr : 2 ≤ primeRank 3 F := by
    rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 F) pCore_isPGroup,
      primeRank_equiv 3 (e.trans Representation.SL5TenDimensional.projectiveEquiv)]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
  have hr' : primeRank 3 f.range = primeRank 3 F := by
    rw [MonoidHom.range_eq_map f]
    exact (ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) f hk
      (⊤ : Subgroup F)).trans (primeRank_equiv 3 Subgroup.topEquiv)
  have h31F : 31 ∣ Nat.card F := by
    have hc : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
      have hh := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
      calc
        _ = ∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ)) := by
          simpa only [Nat.card_zmod, Nat.reduceSub, Nat.gcd_one_right, mul_one] using hh
        _ = 9999360 := by decide
    have hd : 31 ∣ Nat.card (F ⧸ pCore 2 F) := by
      rw [Nat.card_congr (e.trans Representation.SL5TenDimensional.projectiveEquiv).toEquiv, hc]
      decide
    exact hd.trans (card_quotient_dvd_card _)
  have h31 : 31 ∣ Nat.card f.range := by
    have hcount : Nat.card f.ker * Nat.card f.range = Nat.card F := by
      rw [← index_ker]
      exact f.ker.card_mul_index
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    have hc : Nat.Coprime 31 (Nat.card f.ker) := by
      rw [hn]
      exact (by decide : Nat.Coprime 31 2).pow_right n
    exact hc.dvd_of_dvd_mul_left (hcount.symm ▸ h31F)
  refine ⟨f.range,W.map f,Group.IsPerfect.range f,hr' ▸ hr,hP,hne,?_,map_le_range f W,h31⟩
  simpa only [← MonoidHom.range_eq_map] using
    (map_mono (f := f) hn).trans (W.le_normalizer_map f)

omit D h B in
private theorem five_janko_of_local {Q : Type*} [Group Q] [Finite Q]
    (hm : ChapterA.Section02.IsTheoremBModel Q) (hr : 10 ≤ primeRank 2 Q)
    (hl : ExteriorComponentLocalData Q) : Nonempty (Q ≃* Janko4.Model) := by
  rcases hm.remaining_of_twoRank_ge_eight (by omega) with ho | hb | htwo | hs | hj
  · exact (ChapterA.Section02.no_theoremB_odd_model_of_twoRank_ge_eight (by omega) ho).elim
  · exact (hl.not_bender hb).elim
  · obtain ⟨f,hf⟩ := htwo
    exact (hl.not_rank_two f hf).elim
  · obtain ⟨E,_,_,hE,⟨e⟩⟩ := hs
    have hu : primeRank 2 (Theory.SpecificGroups.SymplecticSix.PSp E) ≤ 9 := by
      apply primeRank_le_of_prime_pow_not_dvd
      intro hd
      have hh := hd.trans (card_quotient_dvd_card
        (center (Theory.SpecificGroups.SymplecticSix.Sp E)))
      rw [Theory.SpecificGroups.SymplecticSix.card_sp_of_card_two hE] at hh
      norm_num at hh
    rw [primeRank_equiv 2 e] at hr
    change 10 ≤ primeRank 2 (Theory.SpecificGroups.SymplecticSix.PSp E) at hr
    exact (by omega : False).elim
  · exact hj

omit B in
/-- The full source B-list reduces to the actual J₄ component or the
remaining outer-section models, on the originally selected component. -/
theorem doubledFive_oddNormalizer_component_cases (B : DoubledBranch T L V 5)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) :
    FiveNormalizerComponentCases L (componentOrbit V (T : Subgroup G)) A K := by
  rcases D.doubledOrbit_oddNormalizer_inner_or_outer_section h B A hA ho K hK with hi | he
  · obtain ⟨hn,hw,hf,hc,hr⟩ := D.doubledOrbit_oddNormalizer_inner_placement h B A hA ho hu hout K hK houtK hi
    exact Or.inr ⟨hn,hw,hf,hc,hr,
      five_janko_of_local hm hr (D.doubledFive_oddNormalizer_placed_local h B A hA ho K hf)⟩
  · refine Or.inl ⟨he,?_⟩
    let : IsQuasisimple K := hK.2
    apply exterior_remaining_outer_models hm
    obtain ⟨U,f,hf⟩ := he
    let e := (projectiveEquivLinear (by decide : 0 < 5)).symm.trans
      Representation.SL5TenDimensional.projectiveEquiv.symm
    exact ⟨U,e.toMonoidHom.comp f,e.surjective.comp hf⟩

omit B in
/-- Residual uniqueness constructs the selected component and discharges its
full B-model hypothesis before applying the degree-five exclusions. -/
theorem doubledFive_oddNormalizer_component_of_unique (B : DoubledBranch T L V 5)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,(componentOrbit V (T : Subgroup G)).subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ FiveNormalizerComponentCases L (componentOrbit V (T : Subgroup G)) A K := by
  have hcore := (oddNormalizer_reduction_of_cover_uniqueness D A hu hout).2
  obtain ⟨K,hK,hm,houtK,hcoreK,hqt,_,_,_⟩ :=
    D.doubledOrbit_oddNormalizer_full_component h B A hne hA ho hcore
  let : IsQuasisimple K := hK.2
  have hkg : IsKGroup KnownSimple.IsKnownSimple K :=
    ((oddNormalizer_properQTK h.simpleQTKE A hne).2.2).subgroup K
  have hmodel := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple hqt hkg
  exact ⟨K,hK,hm,houtK,hcoreK,
    D.doubledFive_oddNormalizer_component_cases h B A hA ho hu hout K hK houtK hmodel⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
