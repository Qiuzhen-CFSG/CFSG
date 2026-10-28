module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicOuterExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneSetup
public import CFSG.Quasithin.ChapterE.Section06.Basic
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.ResidualAbelianBound

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.ResidualElementary

/-!
# Identification of the original module in the compared J₄ residual branch

The entire compared residual centralizes the original involution and lies in
N_G(L). The relative TI property of the chosen module therefore makes this
residual normalize V. Transport through the full original involution
centralizer excludes the first native row by its abelian-subgroup bound. In
the second row it identifies V, via the original inclusions, with the full
two-core and proves that V has order 2048.

The final Hall application discharges these normalization and size premises
from the original chosen-module hypotheses. It retains the separate M₁₂/M₂₂
pushing-up alternative and all original component and seed data. This is a
reduction of the remaining source cases, not yet Hall faithfulness.

Source: Aschbacher–Smith, 4.4.3 and 4.4.14, printed pp.623–625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
namespace JankoNormalizerAction
variable {N : Type*} [Group N] [Finite N] {K : Subgroup N}
    (a : JankoNormalizerAction K) [IsQuasisimple K]
include a in
theorem first_residual_normalized_abelian_card_le
    (z : K) (hz : orderOf z = 2)
    (e : (centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
      Janko4.InvolutionCentralizers.First.centralizer)
    (W : Subgroup (centralizer ({z} : Set K))) [IsElementaryAbelian 2 W]
    (hn : solvableResidual (centralizer ({z} : Set K)) ≤ normalizer (W : Set _)) :
    Nat.card W ≤ 256 := by
  let C := centralizer ({z} : Set K)
  let d : C ≃* Janko4.InvolutionCentralizers.First.centralizer :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (a.involution_oddCore_eq_bot z hz).symm).trans e)
  let E := W.map d.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map d.toMonoidHom
  have hnE : solvableResidual Janko4.InvolutionCentralizers.First.centralizer ≤
      normalizer (E : Set _) := by
    rw [←map_solvableResidual_eq d.toMonoidHom d.surjective]
    exact (map_mono hn).trans (W.le_normalizer_map d.toMonoidHom)
  have hh := Janko4.InvolutionCentralizers.First.residual_normalized_abelian_card_le
    E (IsElementaryAbelian.isPGroup 2 E) hnE
  rwa [card_map_of_injective d.injective] at hh
include a in
/-- The second residual identifies the full original centralizer core. -/
theorem second_residual_normalized_large_elementary_core
    (z : K) (hz : orderOf z = 2)
    (e : (centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
      Janko4.InvolutionCentralizers.Second.ambientCentralizer)
    (W : Subgroup (centralizer ({z} : Set K))) [IsElementaryAbelian 2 W]
    (hW : 1024 ≤ Nat.card W)
    (hn : solvableResidual (centralizer ({z} : Set K)) ≤ normalizer (W : Set _))
    (hzW : (⟨z,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({z} : Set K)) ∈ W) :
    W = pCore 2 (centralizer ({z} : Set K)) ∧ Nat.card W = 2048 := by
  let C := centralizer ({z} : Set K)
  let d : C ≃* Janko4.InvolutionCentralizers.Second.ambientCentralizer :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (a.involution_oddCore_eq_bot z hz).symm).trans e)
  let E := W.map d.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map d.toMonoidHom
  let t : C := ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩
  have ht : t ≠ 1 := by
    intro hh
    have hz1 : z = 1 := congrArg C.subtype hh
    rw [hz1,orderOf_one] at hz
    omega
  have htc : t ∈ center C := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp x.property))
  have hnE : solvableResidual Janko4.InvolutionCentralizers.Second.ambientCentralizer ≤
      normalizer (E : Set _) := by
    rw [←map_solvableResidual_eq d.toMonoidHom d.surjective]
    exact (map_mono hn).trans (W.le_normalizer_map d.toMonoidHom)
  have hE := Janko4.InvolutionCentralizers.Second.residual_normalized_large_elementary_eq_kernel
    E (by rwa [card_map_of_injective d.injective]) hnE (d t)
    (mem_map_of_mem d.toMonoidHom hzW)
    (fun hh => ht (d.injective (hh.trans (map_one d).symm)))
    (by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨x,rfl⟩ := d.surjective y
      simpa only [map_mul] using congrArg d (mem_center_iff.mp htc x))
  refine ⟨?_,?_⟩
  · apply map_injective (f := d.toMonoidHom) d.injective
    rw [pCore_map_iso,Janko4.InvolutionCentralizers.Second.ambient_twoCore_eq_kernel]
    exact hE
  · have hh := congrArg (fun U : Subgroup _ => Nat.card U) hE
    rwa [card_map_of_injective d.injective,Janko4.InvolutionCentralizers.Second.ambientKernel_card] at hh

end JankoNormalizerAction
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem original_compared_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (K : Subgroup (normalizer (A : Set G)))
    (hVK : V ≤ K.map (normalizer (A : Set G)).subtype)
    (z : K) (hzV : ((z : normalizer (A : Set G)) : G) ∈ V) (hz : orderOf z = 2)
    (hRM : ((solvableResidual (centralizer ({z} : Set K))).map
      (centralizer ({z} : Set K)).subtype).map
        ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ normalizer (L : Set G)) :
    let k := ((normalizer (A : Set G)).subtype.comp K.subtype).comp
      (centralizer ({z} : Set K)).subtype
    ∃ W : Subgroup (centralizer ({z} : Set K)), IsElementaryAbelian 2 W ∧
      W.map k = V ∧ Nat.card W = Nat.card V ∧
      solvableResidual (centralizer ({z} : Set K)) ≤ normalizer (W : Set _) ∧
      (⟨z,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({z} : Set K)) ∈ W := by
  let := D.elementary
  let zG : G := ((z : normalizer (A : Set G)) : G)
  let Ck := centralizer ({z} : Set K)
  let j := (normalizer (A : Set G)).subtype.comp K.subtype
  let k := j.comp Ck.subtype
  have hj : Function.Injective j := (normalizer (A : Set G)).subtype_injective.comp K.subtype_injective
  have hki : Function.Injective k := hj.comp Ck.subtype_injective
  have hVr : V ≤ k.range := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := hVK hv
    let w : K := ⟨u,hu⟩
    have hw : w ∈ Ck := by
      apply mem_centralizer_singleton_iff.mpr
      apply hj
      exact setLike_mul_comm hv hzV
    exact ⟨⟨w,hw⟩,rfl⟩
  let W := V.comap k
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (k.subgroupComap V) (fun x y he => Subtype.ext (hki (congrArg (fun v : V => (v : G)) he)))
  have hWcard : Nat.card W = Nat.card V := by
    let d := (W.equivMapOfInjective k hki).trans (MulEquiv.subgroupCongr (map_comap_eq_self hVr))
    exact Nat.card_congr d.toEquiv
  have hzG : orderOf zG = 2 := (orderOf_coe (z : normalizer (A : Set G))).trans
    ((orderOf_coe z).trans hz)
  have hzne : zG ≠ 1 := by intro he; rw [he,orderOf_one] at hzG; omega
  have hZne : zpowers zG ≠ ⊥ := by
    intro he
    exact hzne (mem_bot.mp (he ▸ mem_zpowers zG))
  have hNV : normalizer (L : Set G) ⊓ centralizer ({zG} : Set G) ≤ normalizer (V : Set G) := by
    have hh := (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).localCentralizer_le_normalizer hZne (zpowers_le.mpr (hV ▸ hzV))
    simpa only [zpowers_eq_closure,centralizer_closure,hV] using hh
  have hn : solvableResidual Ck ≤ normalizer (W : Set Ck) := by
    apply le_trans _ (V.le_normalizer_comap k)
    intro r hr
    apply hNV
    refine ⟨?_,?_⟩
    · exact hRM (mem_map_of_mem j (mem_map_of_mem Ck.subtype hr))
    · exact mem_centralizer_singleton_iff.mpr
        (congrArg j (mem_centralizer_singleton_iff.mp r.property))
  exact ⟨W,inferInstance,map_comap_eq_self hVr,hWcard,hn,hzV⟩

theorem sourceOrbit_no_first_compared_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (K : Subgroup (normalizer (A : Set G))) [IsQuasisimple K]
    (a : JankoNormalizerAction K)
    (hVK : V ≤ K.map (normalizer (A : Set G)).subtype)
    (z : K) (hzV : ((z : normalizer (A : Set G)) : G) ∈ V) (hz : orderOf z = 2)
    (ef : (centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
      Janko4.InvolutionCentralizers.First.centralizer)
    (hRM : ((solvableResidual (centralizer ({z} : Set K))).map
      (centralizer ({z} : Set K)).subtype).map
        ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ normalizer (L : Set G)) : False := by
  obtain ⟨W,hW,hmap,hcard,hn,hzW⟩ := D.original_compared_module h hmany hV hnon K hVK z hzV hz hRM
  let := hW
  have hb := a.first_residual_normalized_abelian_card_le z hz ef W hn
  rw [hcard] at hb
  let := D.elementary
  rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) V] at hb
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (D.sourceOrbit_mathieu_twoRank_ge_ten hV hm)
  norm_num at hh
  omega

/-- The compared residual forces the second native row and identifies its
entire two-core with the original module through the original inclusions. -/
theorem sourceOrbit_compared_residual_module_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (K : Subgroup (normalizer (A : Set G))) [IsQuasisimple K]
    (a : JankoNormalizerAction K)
    (hVK : V ≤ K.map (normalizer (A : Set G)).subtype)
    (z : K) (hzV : ((z : normalizer (A : Set G)) : G) ∈ V) (hz : orderOf z = 2)
    (hRM : ((solvableResidual (centralizer ({z} : Set K))).map
      (centralizer ({z} : Set K)).subtype).map
        ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ normalizer (L : Set G)) :
    Nonempty ((centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
      Janko4.InvolutionCentralizers.Second.ambientCentralizer) ∧
    V = ((pCore 2 (centralizer ({z} : Set K))).map
      (centralizer ({z} : Set K)).subtype).map
        ((normalizer (A : Set G)).subtype.comp K.subtype) ∧ Nat.card V = 2048 := by
  have he := (a.involution_centralizer_models z hz).resolve_left (fun ef =>
    D.sourceOrbit_no_first_compared_residual h hmany hV hm hnon K a hVK z hzV hz ef.some hRM)
  obtain ⟨W,hW,hmap,hcard,hn,hzW⟩ := D.original_compared_module h hmany hV hnon K hVK z hzV hz hRM
  let := hW
  have hlarge : 1024 ≤ Nat.card W := by
    rw [hcard]
    let := D.elementary
    rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) V]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (D.sourceOrbit_mathieu_twoRank_ge_ten hV hm)
  obtain ⟨hcore,hsize⟩ := a.second_residual_normalized_large_elementary_core z hz he.some W hlarge hn hzW
  refine ⟨he,?_,hcard.symm.trans hsize⟩
  rw [←hmap,hcore,map_map]
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
/-- The compared source case retains its original component, involution and
seed family, and identifies V with the full second-centralizer core. -/
@[expose] def MathieuJankoCoreComparedResidualCase {G : Type*} [Group G]
    (T L V A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    ∃ a : JankoNormalizerAction K, a.ResidualSeedFamily ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        T ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ normalizer (L : Set G) ∧
        Nonempty ((centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
          Janko4.InvolutionCentralizers.Second.ambientCentralizer) ∧
        V = ((pCore 2 (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ∧ Nat.card V = 2048
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A : Subgroup G}
    (D : ChosenModule T L V)

/-- The original compared residual discharges all core-identification premises. -/
theorem sourceOrbit_mathieu_compared_residual_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hc : MathieuJankoComparedResidualCase (T : Subgroup G) L V A) :
    MathieuJankoCoreComparedResidualCase (T : Subgroup G) L V A := by
  obtain ⟨K,hK,hn,hout,hVK,hFK,a,hseed,z,hzV,hz,hTz,hRM⟩ := hc
  let := hK.2
  exact ⟨K,hK,hn,hout,hVK,hFK,a,hseed,z,hzV,hz,hTz,hRM,
    D.sourceOrbit_compared_residual_module_core h hmany hV hm hnon K a hVK z hzV hz hRM⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall obstruction retains the small-Mathieu pushing-up branch.
Its compared branch now has exactly the original order-2048 module as the
full core of the second involution centralizer, with no added hypothesis. -/
theorem sourceOrbit_mathieu_hall_residual_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (((Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
          Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
          MathieuPushingUpFactoredCase T L V A ∧ MathieuPushingUpFactorGap T L V A) ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent) ∧
          MathieuJankoCoreComparedResidualCase (T : Subgroup G) L V A)) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_cubic_excluded G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  obtain ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hcases⟩ := hA
  refine ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,?_⟩
  exact hcases.imp id (fun hc => ⟨hc.1,hc.2.1,
    D.sourceOrbit_mathieu_compared_residual_core h hmany hV hm hnon hc.2.2⟩)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
