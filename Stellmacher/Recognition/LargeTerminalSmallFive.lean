module

public import Stellmacher.Recognition.LargeTerminalSmallCore
public import Stellmacher.Recognition.LargeTerminalFiveAction
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupAction.Order512FiveStructure
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# An actual Sylow-five actor in the full small terminal centralizer

Whenever an omega-central involution has the literal first residual as
its full centralizer two-core, the large terminal context supplies the
following Sylow-five data. The order 2048 wrapper obtains that equality
from the cardinal squeeze. The general form also lets the order 4096
argument exclude a putative small centralizer core. The theorem
retains the intrinsic core order 512 and class at least three, proves that
its Frattini quotient has order sixteen, and supplies an actual Sylow
five-subgroup of the full centralizer of order five whose core fixed
subgroup is central.

The previously constructed order-five actor lies in the mapped first
residual group, which is subnormal in the full omega-center centralizer.
Transport along the literal core inclusion preserves the established
fixed-center action. Parrott's intrinsic two-group theorem gives
Frattini equal to the derived subgroup of order thirty-two. The full
centralizer acts on this Frattini quotient with kernel exactly its
self-centralizing two-core. Any Sylow five-subgroup therefore embeds in
GL4(2), whose order has five-part five. The constructed actor is consequently
already a Sylow five-subgroup, preserving its fixed-center property.

The full centralizer quotient is not identified here with F20. That is the
remaining quotient hypothesis of Parrott's original characterization.
Source: the established large Stellmacher configuration and Parrott,
*A characterization of the Tits' simple group* (1972), Lemma 1, printed
p.672, using only that lemma's intrinsic two-group argument.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped IsMulCommutative
universe u

private theorem five_sylow_card
    {G : Type*} [Group G] [Finite G]
    (hcentral : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hVcard : Nat.card (pCore 2 G ⧸ frattini (pCore 2 G)) = 16)
    (hdiv : 5 ∣ Nat.card G) (P : Sylow 5 G) : Nat.card P = 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Q := pCore 2 G
  let V := Q ⧸ frattini Q
  let _ : Fact (IsPGroup 2 Q) := ⟨pCore_isPGroup⟩
  let _ : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini (p := 2)
  let action := (quotientAut (frattini Q)).comp (MulAut.conjNormal : G →* MulAut Q)
  have hk : action.ker = Q := pCore_frattini_action_kernel 2 hcentral
  have hdis : Disjoint (P : Subgroup G) Q :=
    IsPGroup.disjoint_of_ne 5 2 (by decide) _ _ P.isPGroup' pCore_isPGroup
  let restriction := action.comp (P : Subgroup G).subtype
  have hinj : Function.Injective restriction := by
    apply (MonoidHom.ker_eq_bot_iff restriction).mp
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdis a.property (hk ▸ ha)
  have hAut : Nat.card (MulAut V) = 20160 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow V 4 hVcard]
    decide
  have hPdiv : Nat.card P ∣ 20160 := hAut ▸ card_dvd_of_injective restriction hinj
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra hnot
    have h25 : 25 ∣ 20160 :=
      dvd_trans (Nat.pow_dvd_pow 5 (by omega : 2 ≤ n)) (hn ▸ hPdiv)
    norm_num at h25
  have hne : Nat.card P ≠ 1 := by
    intro h
    exact (Sylow.ne_bot_of_dvd_card P hdiv) (Subgroup.card_eq_one.mp h)
  interval_cases n
  · exact (hne (by simpa using hn)).elim
  · simpa using hn

/-- The full centralizer has the actual core and Sylow-five action data
required by Parrott, retaining the prescribed ambient Sylow. -/
public theorem LargeTerminalContext.exists_sylow_five_fixed_center_of_core_eq
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0)
    (hcore : ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      twoCoreIn (centralizer ({z} : Set G)) = ctx.firstResidual) :
    ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      twoCoreIn (centralizer ({z} : Set G)) = ctx.firstResidual ∧
      Nat.card (pCore 2 (centralizer ({z} : Set G))) = 512 ∧
      3 ≤ Group.nilpotencyClass (pCore 2 (centralizer ({z} : Set G))) ∧
      Nat.card (pCore 2 (centralizer ({z} : Set G)) ⧸
        frattini (pCore 2 (centralizer ({z} : Set G)))) = 16 ∧
      ∃ P : Sylow 5 (centralizer ({z} : Set G)),
        Nat.card P = 5 ∧
        (centralizer (P : Set (centralizer ({z} : Set G)))).subgroupOf
          (pCore 2 (centralizer ({z} : Set G))) ≤
            center (pCore 2 (centralizer ({z} : Set G))) := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨z, hz, hgen, hcore⟩ := hcore
  let C := centralizer ({z} : Set G)
  let J := pCore 2 C
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let E := (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map K.subtype
  have hC : C = centralizer (omegaOneCenter (S0 : Subgroup G) : Set G) := by
    change centralizer ({z} : Set G) = _
    rw [← centralizer_closure, ← zpowers_eq_closure, hgen]
  have hEC : E ≤ C := by
    rw [hC]
    exact (nine_two_ambient_setup
      (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.2.1
  obtain ⟨A, hAcard, hAE, _, hAfixed⟩ := ctx.exists_five_subgroup_fixed_center
  have hAC : A ≤ C := hAE.trans hEC
  let AC := A.subgroupOf C
  have hACcard : Nat.card AC = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv).trans hAcard
  let e : J ≃* ctx.firstResidual :=
    (J.equivMapOfInjective C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hcore)
  have he (j : J) : (e j : G) = ((j : C) : G) := rfl
  have hJcard : Nat.card J = 512 :=
    (Nat.card_congr e.toEquiv).trans ctx.first_residual_structure.1
  let _ : Group.IsNilpotent J := (pCore_isPGroup (p := 2) (G := C)).isNilpotent
  have hclass : 3 ≤ Group.nilpotencyClass J := by
    have h := Group.nilpotencyClass_le_of_surjective e.toMonoidHom e.surjective
    rw [ctx.first_residual_structure.2.2.2.2.2] at h
    exact h
  have hACfixed : (centralizer (AC : Set C)).subgroupOf J ≤ center J := by
    intro j hj
    have hjfixed : (e j : G) ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      have h := mem_centralizer_iff.mp hj (⟨a, hAC ha⟩ : C) ha
      have h' := congrArg C.subtype h
      change a * ((j : C) : G) = ((j : C) : G) * a at h'
      simpa only [he] using h'
    have hjcenter : e j ∈ center ctx.firstResidual :=
      hAfixed (show e j ∈ (centralizer (A : Set G)).subgroupOf ctx.firstResidual from hjfixed)
    have h := (centerCongr e.symm ⟨e j, hjcenter⟩).property
    change e.symm (e j) ∈ center J at h
    simpa only [e.symm_apply_apply] using h
  let _ : MulDistribMulAction AC J :=
    conjMulDistribMulActionOfLeNormalizer AC J (le_normalizer_of_normal (H := J))
  have hfixed : FixedPoints.subgroup AC J ≤ center J := by
    intro j hj
    apply hACfixed
    change (j : C) ∈ centralizer (AC : Set C)
    rw [mem_centralizer_iff]
    intro a ha
    have h := congrArg Subtype.val (hj ⟨a, ha⟩)
    change a * (j : C) * a⁻¹ = (j : C) at h
    exact mul_inv_eq_iff_eq_mul.mp h
  obtain ⟨_, _, hPhi, _, _, hDcard⟩ := Theory.GroupAction.parrott_twoGroup_structure
    (pCore_isPGroup (p := 2) (G := C)) hJcard hclass hACcard hfixed
  have hPhicard : Nat.card (frattini J) = 32 := by rw [← hPhi]; exact hDcard
  have hVcard : Nat.card (J ⧸ frattini J) = 16 := by
    have h := (frattini J).card_mul_index
    rw [hPhicard, hJcard] at h
    change 32 * Nat.card (J ⧸ frattini J) = 512 at h
    omega
  have hchar : IsCharacteristicTwoType C := by
    obtain ⟨w, _, hw, _, _, hchar⟩ := ctx.involution_centralizer_core
    rw [← centralizer_closure, ← zpowers_eq_closure, hw, ← hC] at hchar
    exact hchar
  have hdiv : 5 ∣ Nat.card C := hACcard ▸ AC.card_subgroup_dvd_card
  obtain ⟨P, hACP⟩ := (IsPGroup.of_card (p := 5) (n := 1)
    (by simpa using hACcard) : IsPGroup 5 AC).exists_le_sylow
  have hPcard : Nat.card P = 5 := five_sylow_card hchar hVcard hdiv P
  have hAP : AC = (P : Subgroup C) := eq_of_le_of_card_ge hACP (by rw [hACcard, hPcard])
  refine ⟨z, hz, hgen, hcore, hJcard, hclass, hVcard, P, hPcard, ?_⟩
  change (centralizer ((P : Subgroup C) : Set C)).subgroupOf J ≤ center J
  rw [← hAP]
  exact hACfixed

/-- The order-2048 specialization retains the original public interface. -/
public theorem LargeTerminalContext.exists_sylow_five_fixed_center_of_card
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) (hS : Nat.card S0 = 2048) :
    ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      twoCoreIn (centralizer ({z} : Set G)) = ctx.firstResidual ∧
      Nat.card (pCore 2 (centralizer ({z} : Set G))) = 512 ∧
      3 ≤ Group.nilpotencyClass (pCore 2 (centralizer ({z} : Set G))) ∧
      Nat.card (pCore 2 (centralizer ({z} : Set G)) ⧸
        frattini (pCore 2 (centralizer ({z} : Set G)))) = 16 ∧
      ∃ P : Sylow 5 (centralizer ({z} : Set G)),
        Nat.card P = 5 ∧
        (centralizer (P : Set (centralizer ({z} : Set G)))).subgroupOf
          (pCore 2 (centralizer ({z} : Set G))) ≤
            center (pCore 2 (centralizer ({z} : Set G))) := by
  exact ctx.exists_sylow_five_fixed_center_of_core_eq (ctx.involution_centralizer_core_eq_of_card hS)

end Stellmacher.Recognition
