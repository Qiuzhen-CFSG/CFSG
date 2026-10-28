module

public import Theory.SpecificGroups.BinaryLinear.SylowCubic
public import Theory.Representation.BinarySylowTransvection

/-!
# A cubic normalized by a full binary linear Sylow forces degree two

The cubic averaging argument makes the cubic fixed-point free. A nontrivial
central element of the Sylow is a transvection. It cannot centralize the
cubic, because its binary axis would then be fixed by the cubic. Thus it
inverts the cubic, and the fixed-free rank calculation forces dimension two.
The transvection is constructed from the Sylow; none is an input.

Source application: the actor sieve in Aschbacher–Smith C.5.12, printed
p.163, following the transvection classification G.6.4. This stronger group
calculation also excludes binary linear actors in repeated or dual modules.
-/

public section

namespace BinaryLinear
open Subgroup OuterCyclic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] [FiniteDimensional (ZMod 2) V]

theorem finrank_eq_two_of_sylow_normalizes_cubic
    (hdim : 1 < Module.finrank (ZMod 2) V)
    (S : Sylow 2 (BinaryLinear.GL V)) (c : BinaryLinear.GL V)
    (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hn : (S : Subgroup (BinaryLinear.GL V)) ≤
      normalizer (zpowers c : Set (BinaryLinear.GL V))) : Module.finrank (ZMod 2) V = 2 := by
  classical
  let : Finite (BinaryLinear.GL V) :=
    Finite.of_injective (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  have hV : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 (by omega)
  have hS : (S : Subgroup (BinaryLinear.GL V)) ≠ ⊥ := by
    intro he
    have hnon : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) V)
    let := hnon
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    let W := Submodule.span (ZMod 2) {w}
    have hW : W ≠ ⊥ := by
      intro hh
      have : w ∈ W := Submodule.mem_span_singleton_self w
      have hw0 : w ∈ (⊥ : Submodule (ZMod 2) V) := hh ▸ this
      exact hw hw0
    have hWt : W ≠ ⊤ := by
      intro hh
      have hr : Module.finrank (ZMod 2) W = 1 := finrank_span_singleton hw
      rw [hh, finrank_top] at hr
      omega
    have hRS : radical W ≤ S := (radical_two W).le_sylow_of_normalized S (by rw [he]; exact bot_le)
    exact radical_ne_bot hW hWt (bot_unique (he ▸ hRS))
  let : Nontrivial (S : Subgroup (BinaryLinear.GL V)) :=
    (Subgroup.nontrivial_iff_ne_bot (S : Subgroup (BinaryLinear.GL V))).mpr hS
  let : Nontrivial (Subgroup.center S) := S.isPGroup'.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center S)
  let a : BinaryLinear.GL V := z.val.val
  have hane : a ≠ 1 := fun he => hz (Subtype.ext (Subtype.ext he))
  have hat := isTransvection_of_central_sylow hV hdim S hane (fun x hx =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property (⟨x, hx⟩ : S)))
  have hafree := normalized_cubic_fixed_free S c hc hcne hn
  have hi : a * c = c ^ 2 * a := by
    have hcard : Nat.card (zpowers c) = 3 := by rw [Nat.card_zpowers]; exact orderOf_eq_prime hc hcne
    rcases Subgroup.cyclicThree_normalizer_conjugates (zpowers c) hcard
      c (mem_zpowers c) hcne a (hn z.val.property) with h | h
    · exfalso
      have hac : a * c = c * a := by
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg (fun x => x * a) h
      obtain ⟨w, f, hw, hf, hfw, hae⟩ := hat
      obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
        by_contra! hzero
        exact hf (LinearMap.ext hzero)
      have hv1 : f v = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hv
      have hh := congrArg (fun g : BinaryLinear.GL V => g v) hac
      change a (c v) = c (a v) at hh
      rw [hae] at hh
      change c v + f (c v) • w = c (v + f v • w) at hh
      rw [map_add, map_smul, hv1, one_smul] at hh
      have hwc : f (c v) • w = c w := add_left_cancel hh
      have hfcn : f (c v) ≠ 0 := by
        intro he
        rw [he, zero_smul] at hwc
        exact hw (c.map_eq_zero_iff.mp hwc.symm)
      have hfc1 : f (c v) = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hfcn
      rw [hfc1, one_smul] at hwc
      exact hw (hafree w hwc.symm)
    · have hc2 : c⁻¹ = c ^ 2 := by
        apply inv_eq_of_mul_eq_one_left
        simpa only [← pow_succ] using hc
      simpa only [mul_assoc, inv_mul_cancel, mul_one, hc2] using congrArg (fun x => x * a) h
  have ha : a ^ 2 = 1 := by
    obtain ⟨w, f, _, _, hfw, hae⟩ := hat
    rw [hae]
    ext v
    exact (transvection w f hfw).left_inv v
  exact finrank_eq_two_of_normalized_cubic_inverted_transvection S c a hc hcne hn ha hi
    hat.displacement_rank
end BinaryLinear
