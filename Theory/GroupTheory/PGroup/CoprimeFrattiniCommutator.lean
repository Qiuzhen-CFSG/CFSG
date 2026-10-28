module

public import Theory.GroupTheory.PGroup.FrattiniActionImage
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Coprime commutators detected on the Frattini quotient

For a q-subgroup acting on a finite p-subgroup, with distinct primes,
containment of their commutator in the embedded Frattini subgroup forces
centralization. The Frattini automorphism kernel makes the action image a
p-group; it is also a q-group, hence trivial. This retains the original
subgroups and their conjugation action.
Source application: Aschbacher--Smith, 3.2.13, printed pp.584--585.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative

namespace Subgroup
theorem commutator_eq_bot_of_le_frattini_of_isPGroup
    {H : Type*} [Group H] [Finite H] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hne : p ≠ q) (P A : Subgroup H) (hP : IsPGroup p P) (hA : IsPGroup q A)
    (hAP : A ≤ normalizer (P : Set H))
    (hcomm : ⁅P, A⁆ ≤ (frattini P).map P.subtype) : ⁅P, A⁆ = ⊥ := by
  let := conjMulDistribMulActionOfLeNormalizer A P hAP
  let a := MulDistribMulAction.toMulAut A P
  have hfix : (quotientAut (frattini P)).comp a = 1 := by
    ext s y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) y
    change quotientAut (frattini P) (a s) (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ x
    rw [quotientAut_apply_mk]
    have hc : ⁅(s : H), (x : H)⁆ ∈ (frattini P).map P.subtype := by
      apply hcomm
      rw [commutator_comm P A]
      exact commutator_mem_commutator s.property x.property
    obtain ⟨z, hz, he⟩ := hc
    have hz' : z = a s x * x⁻¹ := Subtype.ext he
    have hq : QuotientGroup.mk' (frattini P) (a s x * x⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hz' ▸ hz)
    rw [map_mul, map_inv] at hq
    exact mul_inv_eq_one.mp hq
  have hap : IsPGroup p a.range := MonoidHom.isPGroup_range_of_frattini_range hP a
    (by rw [hfix]; exact IsPGroup.of_card (n := 0) (by simp))
  have haq : IsPGroup q a.range := hA.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  have ha : a = 1 := MonoidHom.range_eq_bot_iff.mp (disjoint_self.mp
    (IsPGroup.disjoint_of_ne p q hne _ _ hap haq))
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx s hs
  have he := congrArg Subtype.val
    (DFunLike.congr_fun (DFunLike.congr_fun ha (⟨s, hs⟩ : A)) (⟨x, hx⟩ : P))
  change s * x * s⁻¹ = x at he
  exact mul_inv_eq_iff_eq_mul.mp he
end Subgroup
