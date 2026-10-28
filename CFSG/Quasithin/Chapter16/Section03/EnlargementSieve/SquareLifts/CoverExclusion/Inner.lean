module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.Core
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.Action
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic

/-!
# Inner action forces membership in the enlargement

An inner representative k has square in Z(K), hence order dividing four.
The discrepancy k⁻¹z centralizes K and is a two-element in C_G(t). The
second Sylow conclusion of 16.3.11 places it in the central Sylow subgroup
⟨t⟩, which already lies in K. Thus z belongs to the actual subgroup K.

Source: Aschbacher–Smith, 16.3.11(3), printed p.1181.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve
open ComponentTransfer.Intrinsic Theory.GroupTheory.DoubleCoverCentralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}
/-- The source membership assertion for the inner-action branch. -/
theorem inner_action_mem_enlargement (h : TerminalCounterexample T z L t)
    (hshape : ∀ a, TerminalCounterexample T z L a → NonterminalCentralizerShape T z L a)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hcomm : ⁅enlargement t L, zpowers z⁆ = enlargement t L)
    (hZ : center (enlargement t L) = pCore 2 (enlargement t L))
    (he : (pCore 2 (enlargement t L)).map (enlargement t L).subtype = zpowers t)
    (hn : z ∈ normalizer (enlargement t L))
    (hinner : ∃ k : enlargement t L, action hn = MulAut.conj k) :
    z ∈ enlargement t L := by
  let K := enlargement t L
  have htK : t ∈ K := mem_enlargement_of_twoCore_image he
  have hZcard : Nat.card (center K) = 2 := by
    rw [center_eq_zpowers_of_twoCore_image hZ he, Nat.card_zpowers, ← orderOf_coe]
    exact h.involution
  obtain ⟨k, hk⟩ := hinner
  have ha2 : action hn ^ 2 = 1 := by
    change K.normalizerMonoidHom (⟨z, hn⟩ : normalizer K) ^ 2 = 1
    rw [← map_pow, show (⟨z, hn⟩ : normalizer K) ^ 2 = 1 from
      Subtype.ext (h.localSetup.involution ▸ pow_orderOf_eq_one z), map_one]
  have hk2 : k ^ 2 ∈ center K := by
    rw [← conj_kernel, MonoidHom.mem_ker, map_pow, ← hk]
    exact ha2
  have hk4 : (k : G) ^ 4 = 1 := by
    have hp := pow_card_eq_one' (x := (⟨k ^ 2, hk2⟩ : center K))
    rw [hZcard] at hp
    have hh := congrArg (fun a : center K => ((a : K) : G)) hp
    simpa only [coe_pow, coe_one, ← pow_mul] using hh
  have hzk : Commute z (k : G) := by
    have hh := congrArg Subtype.val (DFunLike.congr_fun hk k)
    change z * (k : G) * z⁻¹ = (k : G) * k * (k : G)⁻¹ at hh
    simp only [mul_assoc, mul_inv_cancel, mul_one] at hh
    exact mul_inv_eq_iff_eq_mul.mp (by simpa only [mul_assoc] using hh)
  let c := (k : G)⁻¹ * z
  have hc4 : c ^ 4 = 1 := by
    rw [(hzk.symm.inv_left).mul_pow, inv_pow, hk4, inv_one, one_mul]
    have hz2 := h.localSetup.involution ▸ pow_orderOf_eq_one z
    calc
      z ^ 4 = (z ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hz2, one_pow]
  let H := involutionCentralizer t ⊓ centralizer (K : Set G)
  have hcK : c ∈ centralizer (K : Set G) := by
    intro x hx
    have hh := congrArg Subtype.val (DFunLike.congr_fun hk ⟨x, hx⟩)
    change z * x * z⁻¹ = (k : G) * x * (k : G)⁻¹ at hh
    have hh' := mul_inv_eq_iff_eq_mul.mp hh
    change x * ((k : G)⁻¹ * z) = ((k : G)⁻¹ * z) * x
    calc
      _ = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹ * z) := by group
      _ = _ := by rw [← hh']; group
  have hcH : c ∈ H := ⟨(involutionCentralizer t).mul_mem
    ((involutionCentralizer t).inv_mem (enlargement_le h k.property)) (setup h).t_mem, hcK⟩
  obtain ⟨Q, hQ⟩ := (both_sylow_centralizers h hshape hK hcomm).2
  have hQcent : (Q : Subgroup H) ≤ center H := by
    intro q hq
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    have hqt : (q : G) ∈ zpowers t := hQ ▸ mem_map_of_mem H.subtype hq
    have hat : zpowers t ≤ centralizer ({(a : G)} : Set G) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp a.property.1).symm)
    exact (mem_centralizer_singleton_iff.mp (hat hqt)).symm
  have hQnormal : (Q : Subgroup H).Normal := ⟨fun x hx a => by
    have hc := mem_center_iff.mp (hQcent hx) a
    simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using hx⟩
  let := Sylow.unique_of_normal Q hQnormal
  let cH : H := ⟨c, hcH⟩
  have hp : IsPGroup 2 (zpowers cH) := IsPGroup.of_card_dvd_pow (n := 2) (by
    rw [Nat.card_zpowers, ← orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hc4)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hcQ : cH ∈ (Q : Subgroup H) := by
    rw [← Subsingleton.elim P Q]
    exact hP (mem_zpowers cH)
  have hcK' : c ∈ K := by
    have hct : c ∈ zpowers t := hQ ▸ mem_map_of_mem H.subtype hcQ
    exact (zpowers_le.mpr htK) hct
  have := K.mul_mem k.property hcK'
  simpa only [c, mul_inv_cancel_left] using this
end CFSG.Quasithin.Chapter16.EnlargementSieve
