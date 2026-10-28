module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.ActorCentralizers.Control
public import Theory.PPrimeCore
public import Mathlib.GroupTheory.FixedPointFree
/-!
# The odd core of the actual actor centralizer

For each nonidentity v in the four E ∩ C(a), the centralizer of v in C(a)
lies in the local two-group U. Its intersection with O_{2′}(C(a)) is trivial
by coprime orders. Thus all three involutions act fixed-point freely on this
normal odd subgroup. Two act by inversion, so their nonidentity product acts
trivially; fixed-point freeness forces the odd core to be trivial.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, C(a) analysis on p.6, reused in Lemma 7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

public theorem actorCentralizer_oddCore (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) :
    pPrimeCore 2 (centralizer ({into D k a} : Set G)) = ⊥ := by
  let H := centralizer ({into D k a} : Set G)
  let U := actorLocalCentralizer D k
  let K := pPrimeCore 2 H
  have hUH : U ≤ H := inf_le_left
  have hUcard : Nat.card (U.subgroupOf H) = 32 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv, actorLocalCentralizer_card]
  have hKU : Disjoint K (U.subgroupOf H) := disjoint_of_coprime_natCard (by
    rw [hUcard]
    exact (show Nat.Coprime (Nat.card K) 2 from pPrimeCore_coprime_card.symm).pow_right 5)
  let action : H →* MulAut K := MulAut.conjNormal
  have hfixed (v : H) (hv : (v : G) ∈ E D k) (hvne : (v : G) ≠ 1) :
      MonoidHom.FixedPointFree (action v) := by
    intro w hw
    have hcomm : ((w : H) : G) ∈ centralizer ({(v : G)} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have hweq := congrArg (fun x : K => ((x : H) : G)) hw
      change (v : G) * ((w : H) : G) * (v : G)⁻¹ = ((w : H) : G) at hweq
      exact (mul_inv_eq_iff_eq_mul.mp hweq).symm
    have hwN := E_element_centralizer_le_normalizer D k hE _ hv hvne hcomm
    have hwU : ((w : H) : G) ∈ U := by
      change ((w : H) : G) ∈ actorLocalCentralizer D k
      rw [← actor_normalizer_centralizer_eq D k hE hn]
      exact ⟨(w : H).property, hwN⟩
    apply Subtype.ext
    exact hKU.le_bot ⟨w.property, hwU⟩
  have hinverts (v : H) (hv : (v : G) ∈ E D k) (hvne : (v : G) ≠ 1)
      (hv2 : v ^ 2 = 1) (w : K) : action v w = w⁻¹ := by
    apply congrFun ((hfixed v hv hvne).coe_eq_inv_of_involutive ?_) w
    intro w
    change (action v * action v) w = w
    rw [← map_mul, ← pow_two, hv2, map_one]
    rfl
  have hmem (v : TwistedModel) (hv : v ∈ modelActorCentralizer) : into D k v ∈ H :=
    (modelActorCentralizer_map D k ▸ mem_map_of_mem (into D k) hv).1
  have hz0 := modelActorCentralizer_z_mem
  have hz2 : z 2 ∈ modelActorCentralizer :=
    ((modelActorCentralizer_four (z 2)).mpr (Or.inr (Or.inr (Or.inl rfl)))).1
  let x : H := ⟨into D k (z 0), hmem _ hz0⟩
  let y : H := ⟨into D k (z 2), hmem _ hz2⟩
  have hxE : (x : G) ∈ E D k := modelE_map D k ▸ mem_map_of_mem _ (z_mem_modelE 0)
  have hyE : (y : G) ∈ E D k := modelE_map D k ▸ mem_map_of_mem _ (z_mem_modelE 2)
  have hxe : (x : G) ≠ 1 := by
    change into D k (z 0) ≠ 1
    rw [into_z_zero]
    exact D.z_ne_one
  have hye : (y : G) ≠ 1 := by
    intro h
    have hz : z 2 = 1 := into_injective D k (h.trans (map_one (into D k)).symm)
    have ho := z_order 2
    simp [hz] at ho
  have hxy : ((x * y : H) : G) ≠ 1 := by
    intro h
    have hz : z 0 * z 2 = 1 := into_injective D k
      ((map_mul (into D k) _ _).trans (h.trans (map_one (into D k)).symm))
    exact (show z 0 * z 2 ≠ 1 from by decide +kernel) hz
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    change (into D k (z 0)) ^ 2 = 1
    rw [← map_pow, show z 0 ^ 2 = 1 from by simpa only [z_order] using pow_orderOf_eq_one (z 0), map_one]
  have hy2 : y ^ 2 = 1 := by
    apply Subtype.ext
    change (into D k (z 2)) ^ 2 = 1
    rw [← map_pow, show z 2 ^ 2 = 1 from by simpa only [z_order] using pow_orderOf_eq_one (z 2), map_one]
  apply bot_unique
  intro w hw
  change w = 1
  have heq : action (x * y) (⟨w, hw⟩ : K) = ⟨w, hw⟩ := by
    rw [map_mul, MulAut.mul_apply, hinverts y hyE hye hy2,
      hinverts x hxE hxe hx2, inv_inv]
  exact congrArg Subtype.val (hfixed (x * y) ((E D k).mul_mem hxE hyE) hxy _ heq)
end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
