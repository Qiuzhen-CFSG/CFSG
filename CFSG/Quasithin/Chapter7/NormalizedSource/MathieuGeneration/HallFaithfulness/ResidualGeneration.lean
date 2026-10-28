module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.Comparison
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.ResidualCover

/-!
# Mathieu residual generation on the original full component

The actual odd-normalizer action has an odd central covering kernel. Pull
back a native Sylow-compatible Mathieu local subgroup through this same
projection. The perfect residual of that preimage generates the full
covering component with the perfect residual of any involution centralizer
whose involution centralizes the chosen Sylow subgroup. All residuals use
the original inclusions; the full component is never replaced by its quotient.

The terminal odd-actor comparison now consumes placement of this native
seed residual in the original L_A, instead of a generation equality. The
literal Hall obstruction constructs these seeds on its already chosen K,
with the same involution and ambient M₂₂ residual component. Its pushing-up
branch is preserved. Order-three residual uniqueness, the source M₂₄/Sylow
identification, and the odd-local comparison subgroup still require proof.
This module supplies a source reduction and does not assert Hall faithfulness.

Source: Aschbacher--Smith 4.4.3, printed p.623, and its application in
4.4.14, printed pp.624--625. The separate order-three argument is in
4.2.13, printed pp.611--612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
namespace JankoNormalizerAction
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}
  (a : JankoNormalizerAction K) [Group.IsPerfect K]

include a in
omit [Group.IsPerfect K] in
/-- Oddness of the actual covering center follows from the original action kernel. -/
theorem center_coprime_two : Nat.Coprime 2 (Nat.card (center K)) := by
  let f := a.projection.comp K.subtype
  have hf : f = a.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (center K)) := by
    ext k
    exact a.on_component k
  have hk : f.ker = center K := by
    rw [hf,MonoidHom.ker_comp_of_injective _ _ a.quotientEquiv.injective,
      QuotientGroup.ker_mk']
  have hker : f.ker = a.projection.ker.subgroupOf K := rfl
  rw [←hk,hker,a.kernel]
  exact pPrimeCore_coprime_card.of_dvd_right
    (card_dvd_of_injective (K.subtype.subgroupComap (pPrimeCore 2 G))
      (fun x y h => Subtype.ext (Subtype.ext
        (congrArg (fun z : pPrimeCore 2 G => (z : G)) h))))

/-- Construct the native Mathieu preimage on the original full component,
retaining its actual projection and every Sylow-central involution. -/
theorem exists_mathieu_residual_seed (P : Sylow 2 K) :
    ∃ R : Subgroup K,
      (∃ R₀ : Subgroup Janko4.Model,
        Nonempty (R₀ ≃* Janko4.LocalStructure.SylowCore.Local) ∧
        R = R₀.comap (a.projection.comp K.subtype)) ∧
      (P : Subgroup K) ≤ R ∧
      (∀ b : MulAut K, (P : Subgroup K).map b.toMonoidHom = P →
        R.map b.toMonoidHom = R) ∧
      ∀ z : K, orderOf z = 2 → z ∈ centralizer (P : Set K) →
        (solvableResidual R).map R.subtype ⊔
          (solvableResidual (centralizer ({z} : Set K))).map
            (centralizer ({z} : Set K)).subtype = ⊤ := by
  let q := a.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have he : q = a.projection.comp K.subtype := by
    ext k
    exact (a.on_component k).symm
  obtain ⟨R₀,hmodel,hP,hi,hgen⟩ :=
    Janko4.LocalStructure.exists_sylow_mathieu_residual_seed_of_odd_central_cover
      a.quotientEquiv a.center_coprime_two P
  refine ⟨R₀.comap q,⟨R₀,hmodel,?_⟩,hP,hi,hgen⟩
  rw [he]

/-- A chosen seed is always the full preimage under the original quotient action. -/
noncomputable def mathieuResidualSeed (P : Sylow 2 K) : Subgroup K :=
  (a.exists_mathieu_residual_seed P).choose

theorem mathieuResidualSeed_model (P : Sylow 2 K) :
    ∃ R₀ : Subgroup Janko4.Model,
      Nonempty (R₀ ≃* Janko4.LocalStructure.SylowCore.Local) ∧
      a.mathieuResidualSeed P = R₀.comap (a.projection.comp K.subtype) :=
  (a.exists_mathieu_residual_seed P).choose_spec.1

theorem sylow_le_mathieuResidualSeed (P : Sylow 2 K) :
    (P : Subgroup K) ≤ a.mathieuResidualSeed P :=
  (a.exists_mathieu_residual_seed P).choose_spec.2.1

theorem mathieuResidualSeed_invariant (P : Sylow 2 K) (b : MulAut K)
    (hP : (P : Subgroup K).map b.toMonoidHom = P) :
    (a.mathieuResidualSeed P).map b.toMonoidHom = a.mathieuResidualSeed P :=
  (a.exists_mathieu_residual_seed P).choose_spec.2.2.1 b hP

/-- Generation holds for the perfect residuals in the full component. -/
theorem mathieuResidualSeed_generation (P : Sylow 2 K) (z : K)
    (hz : orderOf z = 2) (hc : z ∈ centralizer (P : Set K)) :
    (solvableResidual (a.mathieuResidualSeed P)).map (a.mathieuResidualSeed P).subtype ⊔
      (solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype = ⊤ :=
  (a.exists_mathieu_residual_seed P).choose_spec.2.2.2 z hz hc

/-- The generation identity uses the same ambient inclusion as the source
involution-centralizer residual. -/
theorem mathieuResidualSeed_generation_map (P : Sylow 2 K) (z : K)
    (hz : orderOf z = 2) (hc : z ∈ centralizer (P : Set K))
    {E : Type*} [Group E] (i : G →* E) :
    K.map i =
      ((solvableResidual (a.mathieuResidualSeed P)).map
        (a.mathieuResidualSeed P).subtype).map (i.comp K.subtype) ⊔
      ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map (i.comp K.subtype) := by
  have hh := congrArg (Subgroup.map (i.comp K.subtype))
    (a.mathieuResidualSeed_generation P z hz hc)
  have ht : (⊤ : Subgroup K).map (i.comp K.subtype) = K.map i := by
    rw [←map_map,←MonoidHom.range_eq_map,range_subtype]
  rw [Subgroup.map_sup,ht] at hh
  exact hh.symm

end JankoNormalizerAction
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- In the literal odd-actor comparison, native Mathieu placement suffices:
the full-cover residual-generation equality is proved, not an input. The
source must still place this seed residual in L_A and construct I. -/
theorem sourceOrbit_janko_residual_comparison_of_seed
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hne : A ≠ ⊥) (hA : A ≤ sectionCentralizer L)
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G))) [Group.IsPerfect K]
    (a : JankoNormalizerAction K)
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (P : Sylow 2 K) (z : K) (hz : orderOf z = 2)
    (hc : z ∈ centralizer (P : Set K))
    (hseed : ((solvableResidual (a.mathieuResidualSeed P)).map
      (a.mathieuResidualSeed P).subtype).map
        ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ oddActorResidual L A)
    (I : Subgroup G) (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    (hAI : A ≤ sectionCentralizer I)
    (hRI : ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map
          ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I) : False := by
  apply hout
  rw [a.mathieuResidualSeed_generation_map P z hz hc (normalizer (A : Set G)).subtype]
  exact sup_le
    (hseed.trans (((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer))
    (hRI.trans (D.sourceOrbit_oddActor_comparison h A hne hA ho I hTI hAI))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
namespace JankoNormalizerAction
/-- The model marking and all literal residual generation maps of the constructed
Sylow-compatible seeds. This is proved for each full component below. -/
@[expose] def ResidualSeedFamily {G : Type*} [Group G] {K : Subgroup G}
    (a : JankoNormalizerAction K) : Prop :=
  ∀ P : Sylow 2 K, ∃ R : Subgroup K,
    (∃ R₀ : Subgroup Janko4.Model,
      Nonempty (R₀ ≃* Janko4.LocalStructure.SylowCore.Local) ∧
      R = R₀.comap (a.projection.comp K.subtype)) ∧
    (P : Subgroup K) ≤ R ∧
    (∀ b : MulAut K, (P : Subgroup K).map b.toMonoidHom = P →
      R.map b.toMonoidHom = R) ∧
    ∀ z : K, orderOf z = 2 → z ∈ centralizer (P : Set K) →
      (solvableResidual R).map R.subtype ⊔
        (solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype = ⊤
end JankoNormalizerAction

open Chapter4 Chapter4.Section04 Sporadic.Mathieu
/-- The source involution and ambient C-component retain the original maps;
the same full J₄ component now carries constructed Mathieu residual seeds.
The selected involution's Sylow arrangement and the source L_A placement
are not included among the conclusions of this reduction. -/
@[expose] def MathieuJankoSeedResidualCase {G : Type*} [Group G]
    (T L V A : Subgroup G) (S : Type*) [Group S] : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧
    (∃ U : Subgroup (K ⧸ center K), ∃ f : U →* S, Function.Surjective f) ∧
    ∃ a : JankoNormalizerAction K,
      Function.Injective (a.projection.comp (V.subgroupOf (normalizer (A : Set G))).subtype) ∧
      (A.subgroupOf (normalizer (A : Set G))).map a.projection = ⊥ ∧
      a.ResidualSeedFamily ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        T ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ∧
        (solvableResidual (centralizer ({z} : Set K))).IsCComponent ∧
        Nonempty ((solvableResidual (centralizer ({z} : Set K)) ⧸
          solvableRadical (solvableResidual (centralizer ({z} : Set K)))) ≃* M22) ∧
        ∃ P : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G) : Subgroup G),
          P.IsCComponent ∧ P.Normal ∧ Nonempty ((P ⧸ solvableRadical P) ≃* M22) ∧
          P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G)).subtype =
              ((solvableResidual (centralizer ({z} : Set K))).map
                (centralizer ({z} : Set K)).subtype).map
                  ((normalizer (A : Set G)).subtype.comp K.subtype) ∧
          ∃! Q : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)),
            Q.IsCComponent ∧ P.map (inclusion inf_le_left) ≤ Q ∧ Q.Normal ∧
              IsQuasisimple (Q ⧸ pCore 2 Q)

/-- Construct the seeds on the same component and projection already chosen
by the literal involution-centralizer argument. -/
theorem mathieu_janko_fixed_residual_seed {G S : Type*} [Group G] [Finite G] [Group S]
    {T L V A : Subgroup G} (h : MathieuJankoFixedResidualCase T L V A S) :
    MathieuJankoSeedResidualCase T L V A S := by
  obtain ⟨K,hK,hn,hKV,hout,hcore,hV,hF,hcent,hr,hsection,a,hi,hA,hz⟩ := h
  let := hK.2
  exact ⟨K,hK,hn,hKV,hout,hcore,hV,hF,hcent,hr,hsection,a,hi,hA,
    a.exists_mathieu_residual_seed,hz⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- The literal Hall obstruction constructs residual-generation seeds on
its full escaping component. No generation callback is assumed. Original
pushing-up uniqueness, source Mathieu placement, and the odd-local comparison
remain required before this reduction can imply Hall faithfulness. -/
theorem sourceOrbit_mathieu_hall_seed_obstruction
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
      (MathieuPushingUpJankoInnerCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,hcase⟩ :=
    @sourceOrbit_mathieu_hall_comparison_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,?_⟩
  rcases hcase with hpush | ⟨hu,hfixed⟩
  · exact .inl hpush
  · exact .inr ⟨hu,mathieu_janko_fixed_residual_seed hfixed⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
