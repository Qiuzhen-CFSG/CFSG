module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicResidual
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.ResidualGeneration

/-!
# The cubic residual in the original Mathieu pushing-up branch

The original maximal two-local witness has trivial odd core. Since the
full covering component is normal there, its center has order prime to
three. Apply the native J₄ cubic construction through its specified central
quotient, retaining the full inverse image of the marked involution
centralizer. The simultaneous-centralizer residual is quasisimple and its
central quotient is the native M₂₂.

The literal Hall obstruction now constructs this residual in its ordinary
pushing-up branch. This does not yet identify it with the full cubic
centralizer residual, place its cubic element in the original intersection
residual, or prove pushing-up uniqueness. The moved-component branch keeps
its existing involution-centralizer maps and residual-generation seeds.

Source: Aschbacher--Smith 4.2.13, printed pp.611--612; the separate
involution-centralizer comparison is 4.4.3 and 4.4.14, pp.623--625.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape

private theorem center_three_coprime {H : Type*} [Group H] [Finite H]
    (hodd : pPrimeCore 2 H = ⊥) (K : Subgroup H) [K.Normal] :
    Nat.Coprime 3 (Nat.card (center K)) := by
  have hm : (pCore 3 K).map K.subtype ≤ pPrimeCore 2 H := by
    apply le_sSup
    refine ⟨inferInstance,?_⟩
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := K)).exists_card_eq
    rw [card_map_of_injective K.subtype_injective,hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  have hc : pCore 3 K = ⊥ := (map_eq_bot_iff_of_injective _ K.subtype_injective).mp
    (bot_unique (hodd ▸ hm))
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := center K) 3 hd
  have hxK : orderOf (x : K) = 3 := (orderOf_coe x).trans hx
  have hz : zpowers (x : K) ≤ center K := zpowers_le.mpr x.property
  have hn : (zpowers (x : K)).Normal := by
    refine ⟨fun y hy g => ?_⟩
    rw [mem_center_iff.mp (hz hy) g,mul_inv_cancel_right]
    exact hy
  have hp : IsPGroup 3 (zpowers (x : K)) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hxK)
  have hle : zpowers (x : K) ≤ pCore 3 K := le_sSup ⟨hn,hp⟩
  have hx1 : (x : K) = 1 := mem_bot.mp (hc ▸ hle (mem_zpowers _))
  have he := hxK
  rw [hx1,orderOf_one] at he
  omega

/-- The original trivial odd core supplies the lifting coprimality on the full component. -/
theorem pushingUp_component_center_three_coprime {G : Type*} [Group G] [Finite G]
    {L V A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) [K.Normal] : Nat.Coprime 3 (Nat.card (center K)) :=
  center_three_coprime hw.2.2.2.2.2.2.2.2.2.2.2.2.1 K

/-- Construct the cubic M₂₂ cover on the original ordinary pushing-up
component, retaining the same central quotient and its full preimage. -/
theorem pushingUp_cubic_residual {G : Type*} [Group G] [Finite G]
    {L V A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hn : K.Normal) (e : (K ⧸ center K) ≃* Janko4.Model) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let R := Janko4.InvolutionCentralizers.First.centralizer.comap q
    ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
      IsQuasisimple (solvableResidual (centralizer ({x} : Set R))) ∧
      Nonempty (((solvableResidual (centralizer ({x} : Set R))) ⧸
        center (solvableResidual (centralizer ({x} : Set R)))) ≃* Sporadic.Mathieu.M22) := by
  have ho : pPrimeCore 2 H = ⊥ := hw.2.2.2.2.2.2.2.2.2.2.2.2.1
  let := hn
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hk : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  exact Janko4.InvolutionCentralizers.First.CubicResidual.exists_cubic_residual_of_central_cover
    q (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le
    (hk.symm ▸ center_three_coprime ho K)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration


namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape

/-- The original pushing-up witnesses, now carrying an actual cubic M₂₂
residual on the same full component and specified central quotient map. -/
@[expose] def MathieuPushingUpCubicCase {G : Type*} [Group G] [Finite G]
    (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ e : (K ⧸ center K) ≃* Janko4.Model,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
        let R := Janko4.InvolutionCentralizers.First.centralizer.comap q
        ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
          IsQuasisimple (solvableResidual (centralizer ({x} : Set R))) ∧
          Nonempty (((solvableResidual (centralizer ({x} : Set R))) ⧸
            center (solvableResidual (centralizer ({x} : Set R)))) ≃* Sporadic.Mathieu.M22)

/-- Construct the cubic residual without changing the ordinary component,
its ambient witnesses or its relative centralizer factorization. -/
theorem mathieu_pushingUp_cubic {G : Type*} [Group G] [Finite G]
    {L V A : Subgroup G} (h : MathieuPushingUpJankoInnerCase L V A) :
    MathieuPushingUpCubicCase L V A := by
  obtain ⟨J,H,W,hw,hf,K,hK,hn,hout,hF,hW,⟨e⟩,hprod⟩ := h
  exact ⟨J,H,W,hw,hf,K,hK,hn,hout,hF,hW,hprod,e,pushingUp_cubic_residual hw K hn e⟩

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
/-- The literal Hall obstruction now supplies an actual order-three residual
in its pushing-up branch. The second branch retains the previous involution,
residual-generation seeds and ambient M₂₂ component, unchanged. Neither
remaining source exclusion is assumed or claimed here. -/
theorem sourceOrbit_mathieu_hall_cubic_obstruction
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
      (MathieuPushingUpCubicCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,hcase⟩ :=
    @sourceOrbit_mathieu_hall_seed_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  exact ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,
    hcase.imp mathieu_pushingUp_cubic id⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
