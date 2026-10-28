module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.JankoConfigurations
public import Theory.SpecificGroups.Janko4.PerfectCoverActions
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Actual J₄ actions in the two Mathieu configurations

The full ordinary component in the pushing-up configuration supplements its
relative centralizer. In the odd-normalizer configuration, conjugation on the
full component, followed by its central quotient, gives an epimorphism onto
the literal J₄ model. Its kernel is exactly the original odd core, so the
original binary module embeds in that model. The odd actor itself maps to
the identity. The formula on the full component retains the prescribed
central quotient map, including any covering kernel.

The literal nonfaithful Hall consumer constructs these actions with the same
components, residuals and ambient witnesses as the previous reduction.
The order-three centralizer argument of 4.2.13 and the involution-centralizer
comparison of 4.4.3 remain separate mathematical obligations.

Source: Aschbacher--Smith, 4.2.13 and 4.4.3, printed pp.612,621--623;
application to 4.4.14, printed pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape

/-- The action data is tied to the original full component and its actual
central quotient. It is constructed below, with no model-action premise. -/
structure JankoNormalizerAction {G : Type*} [Group G]
    (K : Subgroup G) where
  quotientEquiv : (K ⧸ center K) ≃* Janko4.Model
  projection : G →* Janko4.Model
  surjective : Function.Surjective projection
  kernel : projection.ker = pPrimeCore 2 G
  on_component : ∀ k : K, projection (k : G) =
    quotientEquiv (QuotientGroup.mk' (center K) k)

/-- Construct the genuine quotient action from normality and the proved
centralizer identity, without discarding the central cover. -/
def jankoNormalizerAction {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hc : centralizer (K : Set G) = pPrimeCore 2 G) :
    JankoNormalizerAction K where
  quotientEquiv := e
  projection := Janko4.perfectCoverAction K e
  surjective := Janko4.perfectCoverAction_surjective K e
  kernel := (Janko4.perfectCoverAction_ker K e).trans hc
  on_component := Janko4.perfectCoverAction_on_subgroup K e

namespace JankoNormalizerAction
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}
  (a : JankoNormalizerAction K)

/-- The model action is faithful on every original binary subgroup. -/
theorem injective_on_twoSubgroup (P : Subgroup G) (hp : IsPGroup 2 P) :
    Function.Injective (a.projection.comp P.subtype) := by
  apply injective_comp_subtype_of_coprime_ker a.projection _ P hp
  rw [a.kernel]
  exact pPrimeCore_coprime_card

/-- The full original quotient, rather than only its family, is J₄. -/
def quotientEquivModel : (G ⧸ pPrimeCore 2 G) ≃* Janko4.Model :=
  (QuotientGroup.quotientMulEquivOfEq a.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective a.projection a.surjective)

end JankoNormalizerAction

/-- Keep all pushing-up witnesses and the full ordinary component while
adding its actual relative centralizer factorization. -/
@[expose] def MathieuPushingUpJankoInnerCase {G : Type*} [Group G] [Finite G]
    (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G))

/-- The same moved component with its canonical J₄ projection and the
faithful image of the original binary module. -/
@[expose] def MathieuJankoActionCase {G : Type*} [Group G]
    (L V A : Subgroup G) (S : Type*) [Group S] : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧
    (∃ U : Subgroup (K ⧸ center K), ∃ f : U →* S, Function.Surjective f) ∧
    ∃ a : JankoNormalizerAction K,
      Function.Injective (a.projection.comp (V.subgroupOf (normalizer (A : Set G))).subtype) ∧
      (A.subgroupOf (normalizer (A : Set G))).map a.projection = ⊥

/-- Innerness gives the source's ambient factorization for the same selected
component. The full component is retained on the right-hand side. -/
theorem mathieu_pushingUp_janko_inner {G : Type*} [Group G] [Finite G]
    {L V A : Subgroup G} (h : MathieuPushingUpJankoCase L V A) :
    MathieuPushingUpJankoInnerCase L V A := by
  obtain ⟨J,H,W,hw,hf,K,hK,hn,hout,hF,hW,⟨e⟩⟩ := h
  let := hK.2
  let := hn
  let Kg := K.map H.subtype
  let f : Kg ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let : Group.IsPerfect Kg := Group.IsPerfect.ofSurjective
    (f := f.symm.toMonoidHom) f.symm.surjective
  refine ⟨J,H,W,hw,hf,K,hK,hn,hout,hF,hW,⟨e⟩,?_⟩
  apply Janko4.perfect_cover_overgroup Kg H
    ((centerQuotientCongr f).trans e) (map_subtype_le K)
  intro x hx
  exact K.le_normalizer_map H.subtype
    (mem_map_of_mem H.subtype (show (⟨x,hx⟩ : H) ∈ normalizer (K : Set H) by
      rw [normalizer_eq_top]; trivial))

/-- Construct the actual projection for the original odd actor. Its odd
order and normality in its normalizer discharge the vanishing assertion. -/
theorem mathieu_janko_action {G S : Type*} [Group G] [Finite G] [Group S]
    {L V A : Subgroup G} (hpV : IsPGroup 2 V) (ho : Odd (Nat.card A))
    (h : MathieuJankoComponentCase L V A S) : MathieuJankoActionCase L V A S := by
  obtain ⟨K,hK,hn,hKV,hout,hcore,⟨e⟩,hV,hF,hcent,hr,hsection⟩ := h
  let N := normalizer (A : Set G)
  let := hn
  let := hK.2
  let a := jankoNormalizerAction K e hcent
  refine ⟨K,hK,hn,hKV,hout,hcore,hV,hF,hcent,hr,hsection,a,
    a.injective_on_twoSubgroup _ hpV.comap_subtype,?_⟩
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [a.kernel]
  apply le_sSup
  refine ⟨inferInstance,?_⟩
  rw [Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv]
  exact ho.coprime_two_left

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- Literal Hall consumer with the actual inner factorization and faithful
binary-module projection. Both centralizer exclusions remain open. -/
theorem sourceOrbit_mathieu_hall_janko_actions
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
          MathieuJankoActionCase L V A (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hcase⟩ :=
    @sourceOrbit_mathieu_hall_two_janko_configurations G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,?_⟩
  rcases hcase with hpush | ⟨hu,hj⟩
  · exact .inl (mathieu_pushingUp_janko_inner hpush)
  · have hodd : Odd (Nat.card A) := by
      let : Fact p.Prime := ⟨hp⟩
      let := he
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
      rw [hn]
      exact ho.pow
    let := D.elementary
    exact .inr ⟨hu,mathieu_janko_action (IsElementaryAbelian.isPGroup 2 V) hodd hj⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
