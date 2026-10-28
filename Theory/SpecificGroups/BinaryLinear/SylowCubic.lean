module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.GroupTheory.CyclicThreeNormalizer
public import Theory.Representation.CyclicFixedRank

/-!
# Cubics normalized by binary linear Sylow subgroups

An idempotent commuting with a full Sylow two-subgroup of GL(V,2) is zero
or the identity. The unipotent radical of its image lies in that Sylow,
yet commuting with the projection makes the radical trivial. Applied to
the cubic averaging projection, this says that a nonidentity cubic
normalized by the Sylow has no fixed vectors. If a transvection inverts
the cubic, rank-nullity then forces dimension two.

This is the natural-linear-model exclusion in the transvection argument
of Aschbacher–Smith, C.5.12, printed p.163, using G.6.4, pp.345–346.
It assumes no classification of the acting group.
-/

public section

namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem sylow_idempotent_eq_zero_or_one (S : Sylow 2 (BinaryLinear.GL V))
    (e : Module.End (ZMod 2) V) (hee : e * e = e)
    (heS : ∀ s ∈ S, ∀ v, e (s v) = s (e v)) : e = 0 ∨ e = 1 := by
  let W := e.range
  have hSW : (S : Subgroup (BinaryLinear.GL V)) ≤ parabolic W := by
    intro s hs v
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨s⁻¹ w, ?_⟩
      rw [heS _ (S.inv_mem hs), hw]
      simp
    · rintro ⟨w, rfl⟩
      exact ⟨s w, heS s hs w⟩
  have hRS : radical W ≤ S := (radical_two W).le_sylow_of_normalized S
    (hSW.trans (parabolic_le_normalizer W))
  have hR : radical W = ⊥ := by
    apply bot_unique
    intro r hr
    change r = 1
    ext v
    have hd := hr.2 v
    have hfix : e (r v - v) = r v - v := by
      obtain ⟨w, hw⟩ := hd
      rw [← hw]
      exact LinearMap.congr_fun hee w
    have hz : e (r v - v) = 0 := by
      rw [map_sub, heS r (hRS hr), hr.1 _ ⟨v, rfl⟩, sub_self]
    exact sub_eq_zero.mp (hfix.symm.trans hz)
  by_cases hW : W = ⊥
  · left
    exact LinearMap.range_eq_bot.mp hW
  · right
    have hWt : W = ⊤ := by
      by_contra hWt
      exact radical_ne_bot hW hWt hR
    ext v
    obtain ⟨w, hw⟩ := show v ∈ e.range from hWt.ge Submodule.mem_top
    rw [← hw]
    exact LinearMap.congr_fun hee w

private theorem twice (v : V) : v + v = 0 := by
  have h := @two_smul (ZMod 2) V _ _ _ v
  simpa only [show (2 : ZMod 2) = 0 by decide, zero_smul] using h.symm

theorem normalized_cubic_fixed_free [Finite V]
    (S : Sylow 2 (BinaryLinear.GL V)) (c : BinaryLinear.GL V) (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hn : (S : Subgroup (BinaryLinear.GL V)) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set (BinaryLinear.GL V))) :
    ∀ v, c v = v → v = 0 := by
  let : Finite (BinaryLinear.GL V) := Finite.of_injective (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  let e : Module.End (ZMod 2) V := 1 + c.toLinearMap + c.toLinearMap * c.toLinearMap
  have hc3 (v : V) : c (c (c v)) = v := by
    have h := congrArg (fun g : BinaryLinear.GL V => g v) hc
    simpa only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply,
      LinearEquiv.coe_one, id_eq] using h
  have he (v : V) : e v = v + c v + c (c v) := rfl
  have hce (v : V) : c (e v) = e v := by
    rw [he, map_add, map_add, hc3]
    abel
  have hee : e * e = e := by
    ext v
    change e (e v) = e v
    rw [he, hce, hce, twice, zero_add]
  have hc2 : c⁻¹ = c ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [← pow_succ] using hc
  have hcard : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hc hcne
  have heS : ∀ s ∈ S, ∀ v, e (s v) = s (e v) := by
    intro s hs v
    rcases Subgroup.cyclicThree_normalizer_conjugates
      (Subgroup.zpowers c) hcard c (Subgroup.mem_zpowers c) hcne s (hn hs) with h | h
    · have hsc : s * c = c * s := by
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg (fun x => x * s) h
      have hsc' (w : V) : s (c w) = c (s w) := congrArg (fun g : BinaryLinear.GL V => g w) hsc
      simp only [he, map_add, hsc']
    · have hsc : s * c = c ^ 2 * s := by
        simpa only [mul_assoc, inv_mul_cancel, mul_one, hc2] using congrArg (fun x => x * s) h
      have hsc' (w : V) : s (c w) = c (c (s w)) := by
        simpa only [pow_two, LinearEquiv.mul_apply] using congrArg (fun g : BinaryLinear.GL V => g w) hsc
      have hsc'' : s (c (c v)) = c (s v) := by
        rw [hsc', hsc', hc3]
      simp only [he, map_add, hsc'', hsc']
      abel
  have he0 : e = 0 := by
    rcases sylow_idempotent_eq_zero_or_one S e hee heS with h | h
    · exact h
    · exfalso
      apply hcne
      ext v
      simpa only [h, Module.End.one_apply, LinearEquiv.coe_one, id_eq] using hce v
  intro v hv
  have hev : e v = v := by rw [he, hv, hv, twice, zero_add]
  simpa only [he0, LinearMap.zero_apply] using hev.symm
theorem finrank_eq_two_of_normalized_cubic_inverted_transvection [Finite V]
    [FiniteDimensional (ZMod 2) V]
    (S : Sylow 2 (BinaryLinear.GL V)) (c a : BinaryLinear.GL V)
    (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hn : (S : Subgroup (BinaryLinear.GL V)) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set (BinaryLinear.GL V)))
    (ha : a ^ 2 = 1) (hi : a * c = c ^ 2 * a)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) = 1) :
    Module.finrank (ZMod 2) V = 2 := by
  let ρ : Representation (ZMod 2) (BinaryLinear.GL V) V :=
    { toFun := LinearEquiv.toLinearMap, map_one' := rfl, map_mul' _ _ := rfl }
  have h := Representation.CyclicFixedRank.ker_eq_range_of_inverted_cubic
    ρ c a hc ha hi (normalized_cubic_fixed_free S c hc hcne hn)
  have hr := (a.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
  change LinearMap.ker (a.toLinearMap - LinearMap.id) =
    LinearMap.range (a.toLinearMap - LinearMap.id) at h
  rw [h, ht] at hr
  omega
end BinaryLinear
