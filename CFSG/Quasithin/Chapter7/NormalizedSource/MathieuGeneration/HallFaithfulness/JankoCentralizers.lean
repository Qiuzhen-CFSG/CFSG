module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.JankoActions
public import Theory.GroupTheory.OddKernelInvolutionCentralizer
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First

/-!
# Involution centralizers in the full Mathieu J₄ component

Restrict the actual odd-normalizer projection to its full component. It is
surjective with odd kernel. Kernel conjugacy of involutions makes every
involution centralizer surject onto the centralizer in the literal J₄ model.
The native centralizers have characteristic two, hence trivial odd core;
the preimage theorem identifies the kernel with the original centralizer's
odd core. This gives the two genuine native centralizer models, retaining
the first model's triple M₂₂ cover and its extraspecial two-core.

The application chooses an involution in the original V, lifts it to the
same full component, and keeps the residual placement and escape. It does
not yet identify the source's T-fixed line or promote the centralizer's
residual to the ambient M₂₂ C-component.

Source: Aschbacher--Smith 4.4.3, printed p.623; GLS3 Table 5.3i.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace JankoNormalizerAction
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}
  (a : JankoNormalizerAction K)

omit [Finite G] in
private theorem componentProjection_surjective :
    Function.Surjective (a.projection.comp K.subtype) := by
  intro y
  obtain ⟨x,rfl⟩ := a.quotientEquiv.surjective y
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (center K) x
  exact ⟨k,a.on_component k⟩

private theorem componentProjection_coprime :
    Nat.Coprime 2 (Nat.card (a.projection.comp K.subtype).ker) := by
  have hker : (a.projection.comp K.subtype).ker = a.projection.ker.subgroupOf K := rfl
  rw [hker,a.kernel]
  exact pPrimeCore_coprime_card.of_dvd_right
    (card_dvd_of_injective (K.subtype.subgroupComap (pPrimeCore 2 G))
      (fun x y h => Subtype.ext (Subtype.ext
        (congrArg (fun z : pPrimeCore 2 G => (z : G)) h))))

/-- Identify the literal centralizer quotient with the native centralizer
of its actual involution image. The displayed formula fixes the quotient map. -/
theorem involution_centralizer_quotient (z : K) (hz : orderOf z = 2) :
    ∃ e : (centralizer ({z} : Set K) ⧸
      pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
        centralizer ({a.projection (z : G)} : Set Janko4.Model),
      (∀ x : centralizer ({z} : Set K),
        (e (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({z} : Set K))) x) : Janko4.Model) =
          a.projection ((x : K) : G)) ∧
      orderOf (a.projection (z : G)) = 2 := by
  let f := a.projection.comp K.subtype
  let c := f.elementCentralizerMap z
  have hs := f.elementCentralizerMap_surjective_of_odd_kernel
    a.componentProjection_surjective a.componentProjection_coprime z hz
  have ho : orderOf (f z) = 2 :=
    orderOf_map_involution_of_odd_kernel f a.componentProjection_coprime hz
  have hk : Nat.Coprime 2 (Nat.card c.ker) := by
    rw [show c.ker = f.ker.subgroupOf (centralizer ({z} : Set K)) from
      f.elementCentralizerMap_ker z]
    exact a.componentProjection_coprime.of_dvd_right
      (card_dvd_of_injective ((centralizer ({z} : Set K)).subtype.subgroupComap f.ker)
        (fun x y h => Subtype.ext (Subtype.ext
          (congrArg (fun w : f.ker => (w : K)) h))))
  have hcore : pPrimeCore 2 (centralizer ({f z} : Set Janko4.Model)) = ⊥ :=
    pPrimeCore_eq_bot_of_centralizer_pCore_le 2
      (Janko4.InvolutionCentralizers.centralizer_characteristic_two (f z) ho)
  have hker : c.ker = pPrimeCore 2 (centralizer ({z} : Set K)) := by
    have hh := pPrimeCore_comap_eq_of_surjective_coprime 2 c hs hk
    rw [hcore] at hh
    exact hh
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective c hs)
  refine ⟨e,?_,ho⟩
  intro x
  rfl

include a in
/-- Both intrinsic involution-centralizer rows hold on the full covering
component after its genuine odd core, with the triple cover retained. -/
theorem involution_centralizer_models (z : K) (hz : orderOf z = 2) :
    Nonempty ((centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
      Janko4.InvolutionCentralizers.First.centralizer) ∨
    Nonempty ((centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
      Janko4.InvolutionCentralizers.Second.ambientCentralizer) := by
  obtain ⟨e,he,ho⟩ := a.involution_centralizer_quotient z hz
  rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second
    (a.projection (z : G)) ho with hb | hb
  · obtain ⟨b⟩ := hb
    exact .inl ⟨e.trans b⟩
  · obtain ⟨b⟩ := hb
    exact .inr ⟨e.trans b⟩

end JankoNormalizerAction

open Chapter4 Chapter4.Section04
/-- The native involution centralizers on a full escaping component containing
both the original residual and the original module. -/
@[expose] def MathieuJankoInvolutionCase {G : Type*} [Group G]
    (L V A : Subgroup G) : Prop :=
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      V ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        (Nonempty ((centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
          Janko4.InvolutionCentralizers.First.centralizer) ∨
        Nonempty ((centralizer ({z} : Set K) ⧸ pPrimeCore 2 (centralizer ({z} : Set K))) ≃*
          Janko4.InvolutionCentralizers.Second.ambientCentralizer))

/-- An original module involution lies in the same escaping component, and
its full component centralizer has one of the two native M₂₂ local models. -/
theorem mathieu_janko_module_involution {G S : Type*} [Group G] [Finite G] [Group S]
    {L V A : Subgroup G} (he : IsElementaryAbelian 2 V) (hne : V ≠ ⊥)
    (h : MathieuJankoActionCase L V A S) : MathieuJankoInvolutionCase L V A := by
  obtain ⟨K,hK,hn,hKV,hout,hcore,hV,hF,hcent,hr,hsection,a,hi,hA⟩ := h
  obtain ⟨v,hv,hvne⟩ := V.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨k,hk,hkv⟩ := hV hv
  let z : K := ⟨k,hk⟩
  have hzv : ((z : normalizer (A : Set G)) : G) = v := hkv
  have hz : orderOf z = 2 := by
    rw [← orderOf_coe z,← orderOf_coe (z : normalizer (A : Set G)),hzv]
    let := he
    exact orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian v hv,hvne⟩
  exact ⟨K,hK,hn,hout,hV,hF,z,hzv.symm ▸ hv,hz,a.involution_centralizer_models z hz⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- The literal Hall obstruction now supplies the actual component
involution-centralizer models. No source T-fixed-line or ambient component
promotion assertion is included in this intermediate conclusion. -/
theorem sourceOrbit_mathieu_hall_janko_centralizers
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
      (MathieuPushingUpJankoInnerCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoActionCase L V A (D.orbitComponent ⧸ center D.orbitComponent) ∧
          MathieuJankoInvolutionCase L V A)) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hcase⟩ :=
    @sourceOrbit_mathieu_hall_janko_actions G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,?_⟩
  rcases hcase with hpush | ⟨hu,hj⟩
  · exact .inl hpush
  · exact .inr ⟨hu,hj,mathieu_janko_module_involution D.elementary D.ne_bot hj⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
