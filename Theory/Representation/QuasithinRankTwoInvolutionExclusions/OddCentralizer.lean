module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.Representation.NormalInvariants
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.TensorCoordinates
public import Mathlib.Tactic

/-!
# Normal cubic actors on binary moved planes

An involution inverting a fixed-point-free cubic operator has equal fixed and
moved spaces: if `x` is fixed, its preimage under displacement is `t x`.
Rank-nullity gives twice the displacement rank as the ambient dimension.
Consequently a rank-two involution in dimension six centralizes a normal C₃,
provided C₃ has no nonzero fixed vectors. Faithfulness and irreducibility imply
this fixed-space condition when C₃ is normal.

These are conditional linear-algebra tools for the extraspecial-three case of
Aschbacher–Smith, *The Classification of Quasithin Groups*, G.11.2(3), printed
p.364, and the proof of 6.2.19, printed p.691. The actual SD₁₆ extension model
must still supply its normal C₃ and identify it with the center of the odd core.
The imported tensor coordinates prove general ranks and the cubic action; the
concrete tensor-product models of G.11.2(9) still require identification. This
module does not assert that either concrete source case has been established.
-/

@[expose] public section

namespace Representation.RankTwo
variable {B G : Type*} [AddCommGroup B] [Module (ZMod 2) B] [Group G]

private lemma binary_add_self (x : B) : x + x = 0 := by
  have h := @two_smul (ZMod 2) B _ _ _ x
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_smul] at h
  exact h.symm

/-- The norm of a fixed-point-free cubic operator is zero. -/
lemma quadratic_of_cubic_fixed_free (t : Module.End (ZMod 2) B)
    (ht : t ^ 3 = 1) (hfix : ∀ x, t x = x → x = 0) : t ^ 2 + t + 1 = 0 := by
  ext x
  apply hfix
  change t (t (t x) + t x + x) = t (t x) + t x + x
  have ht' : t (t (t x)) = x := by
    simpa [pow_succ, Module.End.mul_apply] using LinearMap.congr_fun ht x
  simp only [map_add, ht']
  abel

/-- Inversion of a quadratic cubic operator identifies the moved and fixed spaces. -/
lemma range_eq_ker_of_inverts_cubic (t b : Module.End (ZMod 2) B)
    (ht : t ^ 2 + t + 1 = 0) (hb : b * b = 1)
    (hbt : b * t = t ^ 2 * b) :
    LinearMap.range (b - 1) = LinearMap.ker (b - 1) := by
  have hbb (x : B) : b (b x) = x := LinearMap.congr_fun hb x
  have hsum (x : B) : t (t x) + t x = x := by
    have h : (t (t x) + t x) + x = 0 := LinearMap.congr_fun ht x
    exact add_right_cancel (h.trans (binary_add_self x).symm)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change b (b x - x) - (b x - x) = 0
    rw [map_sub, hbb]
    have hn : -(b x - x) = b x - x := by
      exact neg_eq_iff_add_eq_zero.mpr (binary_add_self _)
    calc
      x - b x - (b x - x) = -(b x - x) - (b x - x) := by abel
      _ = 0 := by rw [hn, sub_self]
  · intro x hx
    have hbx : b x = x := sub_eq_zero.mp hx
    refine ⟨t x, ?_⟩
    change b (t x) - t x = x
    have h : b (t x) = t (t x) := by
      simpa only [Module.End.mul_apply, pow_two, hbx] using LinearMap.congr_fun hbt x
    have hn : -(t x) = t x := neg_eq_iff_add_eq_zero.mpr (binary_add_self _)
    rw [h, sub_eq_add_neg, hn, hsum]

/-- An inverting involution moves exactly half the ambient dimension. -/
lemma finrank_range_inverting_cubic [FiniteDimensional (ZMod 2) B]
    (t b : Module.End (ZMod 2) B)
    (ht : t ^ 3 = 1) (hfix : ∀ x, t x = x → x = 0)
    (hb : b * b = 1) (hbt : b * t = t ^ 2 * b) :
    2 * Module.finrank (ZMod 2) (LinearMap.range (b - 1)) =
      Module.finrank (ZMod 2) B := by
  have hr := range_eq_ker_of_inverts_cubic t b (quadratic_of_cubic_fixed_free t ht hfix) hb hbt
  have h := (b - 1).finrank_range_add_finrank_ker
  rw [← hr] at h
  omega

/-- Conjugation on a normal group of order three is trivial or inversion. -/
lemma commute_or_invert_of_normal_three (c v : G) (hc : orderOf c = 3)
    (hn : (Subgroup.zpowers c).Normal) :
    Commute c v ∨ v * c = c ^ 2 * v := by
  classical
  have hf : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, by rw [← hc, pow_orderOf_eq_one]⟩
  have hm := hn.conj_mem c (Subgroup.mem_zpowers c) v
  rw [hf.mem_zpowers_iff_mem_range_orderOf, hc] at hm
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
  have hn' : n < 3 := Finset.mem_range.mp hn
  interval_cases n
  · have hc1 : c = 1 := by
      have hh : v * c * v⁻¹ = 1 := by simpa using he.symm
      have := congrArg (fun x => v⁻¹ * x * v) hh
      simpa [mul_assoc] using this
    simp [hc1] at hc
  · left
    have hh : c = v * c * v⁻¹ := by simpa using he
    have := congrArg (fun x => x * v) hh
    exact this.trans (by simp [mul_assoc])
  · right
    have := congrArg (fun x => x * v) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using this.symm

/-- Rank two in dimension six excludes inversion of a fixed-point-free normal C₃. -/
lemma commute_of_rank_two_normal_three [FiniteDimensional (ZMod 2) B]
    (ρ : Representation (ZMod 2) G B) (v c : G)
    (hdim : Module.finrank (ZMod 2) B = 6)
    (hv : v * v = 1) (hc : orderOf c = 3)
    (hn : (Subgroup.zpowers c).Normal)
    (hfix : ∀ x, ρ c x = x → x = 0)
    (hrank : Module.finrank (ZMod 2) (movedSpace ρ v) = 2) : Commute c v := by
  rcases commute_or_invert_of_normal_three c v hc hn with h | h
  · exact h
  · have ht : (ρ c) ^ 3 = 1 := by
      rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
    have hb : ρ v * ρ v = 1 := by rw [← map_mul, hv, map_one]
    have hbt : ρ v * ρ c = (ρ c) ^ 2 * ρ v := by
      rw [← map_pow, ← map_mul, ← map_mul, h]
    have hf := finrank_range_inverting_cubic (ρ c) (ρ v) ht hfix hb hbt
    change 2 * Module.finrank (ZMod 2) (movedSpace ρ v) = _ at hf
    rw [hrank, hdim] at hf
    omega

/-- A fixed-point-free normal C₃ is transitive on a rank-two moved plane in dimension six. -/
lemma stabilizerTransitive_of_rank_two_normal_three [FiniteDimensional (ZMod 2) B]
    (ρ : Representation (ZMod 2) G B) (v c : G)
    (hdim : Module.finrank (ZMod 2) B = 6)
    (hv : v * v = 1) (hc : orderOf c = 3)
    (hn : (Subgroup.zpowers c).Normal)
    (hfix : ∀ x, ρ c x = x → x = 0)
    (hrank : Module.finrank (ZMod 2) (movedSpace ρ v) = 2) :
    StabilizerTransitive ρ (movedSpace ρ v) := by
  apply stabilizerTransitive_of_order_three ρ v c hrank
    (commute_of_rank_two_normal_three ρ v c hdim hv hc hn hfix hrank)
  · rw [← hc, pow_orderOf_eq_one]
  · intro x _ hx
    exact hfix x hx

/-- A normal C₃ has no nonzero fixed vectors in a faithful irreducible module. -/
lemma fixed_free_of_faithful_irreducible_normal_three
    (ρ : Representation (ZMod 2) G B) [Representation.IsIrreducible ρ]
    (hfaith : Function.Injective ρ) (c : G) (hc : orderOf c = 3)
    (hn : (Subgroup.zpowers c).Normal) : ∀ x, ρ c x = x → x = 0 := by
  classical
  have := hn
  have hf : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨3, by decide, by rw [← hc, pow_orderOf_eq_one]⟩
  intro x hx
  by_contra hx0
  have hxmem : x ∈ Representation.invariants (ρ.comp (Subgroup.zpowers c).subtype) := by
    intro g
    have hg := g.property
    rw [hf.mem_zpowers_iff_mem_range_orderOf, hc] at hg
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hg
    change ρ (g : G) x = x
    rw [← he]
    have hn' : n < 3 := Finset.mem_range.mp hn
    interval_cases n <;> simp [pow_succ, map_mul, Module.End.mul_apply, hx]
  have hnon : Representation.invariants (ρ.comp (Subgroup.zpowers c).subtype) ≠ ⊥ := by
    intro h
    rw [h] at hxmem
    exact hx0 hxmem
  have hk := Representation.le_ker_of_normal_invariants_ne_bot ρ (Subgroup.zpowers c) hnon
  have hc1 : c = 1 := hfaith ((hk (Subgroup.mem_zpowers c)).trans (map_one ρ).symm)
  simp [hc1] at hc

/-- Faithful irreducibility discharges the fixed-space premise of the dimension-six criterion. -/
lemma stabilizerTransitive_of_irreducible_normal_three [FiniteDimensional (ZMod 2) B]
    (ρ : Representation (ZMod 2) G B) [Representation.IsIrreducible ρ]
    (hfaith : Function.Injective ρ) (v c : G)
    (hdim : Module.finrank (ZMod 2) B = 6)
    (hv : v * v = 1) (hc : orderOf c = 3)
    (hn : (Subgroup.zpowers c).Normal)
    (hrank : Module.finrank (ZMod 2) (movedSpace ρ v) = 2) :
    Commute c v ∧ StabilizerTransitive ρ (movedSpace ρ v) := by
  have hfix := fixed_free_of_faithful_irreducible_normal_three ρ hfaith c hc hn
  exact ⟨commute_of_rank_two_normal_three ρ v c hdim hv hc hn hfix hrank,
    stabilizerTransitive_of_rank_two_normal_three ρ v c hdim hv hc hn hfix hrank⟩
end Representation.RankTwo


