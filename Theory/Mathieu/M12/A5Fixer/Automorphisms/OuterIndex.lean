module

public import Theory.Mathieu.M12.A5Fixer.Automorphisms.SylowBound
public import Theory.Mathieu.M12.Properties.AutCover

/-!
# The outer automorphism index of M₁₂

Sylow conjugacy gives a surjection from the full automorphism stabilizer of
the marked Sylow two-subgroup onto Out(M₁₂). The kernel contains the 64
inner automorphisms induced by the Sylow subgroup: conjugation is injective
because the actual M₁₂ carrier has trivial center. The stabilizer's checked
order bound of 128 therefore gives outer index at most two.

This includes every abstract automorphism and does not require an explicit
outer automorphism, a permutation normalizer model, or a splitting of Aut(M₁₂).
Source context: Aschbacher–Smith 16.1.5(4) and 16.3.5, combined manuscript
of 1 March 2004, printed pp.1171 and 1178–1179.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M12A5Fixer.Automorphisms
open M12SmallPair

private theorem conjugation_injective :
    Function.Injective (MulAut.conj : M12 →* MulAut M12) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hc : g ∈ center M12 := by
    rw [mem_center_iff]
    intro x
    have hx := congrArg (fun a : MulAut M12 => a x) hg
    change g * x * g⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  simpa only [m12_center_eq_bot, mem_bot] using hc

/-- The inner automorphisms have index at most two in the full abstract
M₁₂ automorphism group. -/
theorem outerIndexBound : OuterIndexBound := by
  have hbound := sylowStabilizer_bound
  let H := sylowStabilizer
  let q := (QuotientGroup.mk' (MulAut.innerSubgroup M12)).comp H.subtype
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup M12) x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 (a • commonSylow) commonSylow
    have hm : MulAut.conj g * a ∈ H := by
      change (MulAut.conj g * a) • sylowCandidate = sylowCandidate
      rw [mul_smul]
      exact congrArg Sylow.toSubgroup hg
    refine ⟨⟨MulAut.conj g * a, hm⟩, ?_⟩
    change QuotientGroup.mk' (MulAut.innerSubgroup M12) (MulAut.conj g * a) = _
    have hi : QuotientGroup.mk' (MulAut.innerSubgroup M12) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff (N := MulAut.innerSubgroup M12) (MulAut.conj g)).mpr ⟨g, rfl⟩
    rw [map_mul, hi, one_mul]
  let f : sylowCandidate → q.ker := fun s =>
    ⟨⟨MulAut.conj (s : M12), conj_smul_eq_self_of_mem s.property⟩,
      (QuotientGroup.eq_one_iff (N := MulAut.innerSubgroup M12) _).mpr ⟨s, rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply conjugation_injective
    exact congrArg (fun t : q.ker => (t : H).val) h
  have hker : 64 ≤ Nat.card q.ker := by
    rw [← card_sylowCandidate]
    exact Nat.card_le_card_of_injective f hf
  have hindex : q.ker.index = (MulAut.innerSubgroup M12).index := by
    rw [index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv]
    rfl
  have hcard := q.ker.card_mul_index
  rw [hindex] at hcard
  change Nat.card H ≤ 128 at hbound
  change (MulAut.innerSubgroup M12).index ≤ 2
  have hmul : 64 * (MulAut.innerSubgroup M12).index ≤ 128 := by
    calc
      _ ≤ Nat.card q.ker * (MulAut.innerSubgroup M12).index := Nat.mul_le_mul_right _ hker
      _ = Nat.card H := hcard
      _ ≤ 128 := hbound
  omega

end Sporadic.Mathieu.M12A5Fixer.Automorphisms
