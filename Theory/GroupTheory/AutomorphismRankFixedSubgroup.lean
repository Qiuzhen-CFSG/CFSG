module

public import Theory.GroupTheory.AutomorphismRankCyclicOuter
public import Theory.GroupAction.AutomorphismFixedResidualTransport

/-!
# Sharp automorphism rank from outer involution fixed groups

For a finite centerless group with cyclic outer quotient, an elementary
abelian automorphism subgroup either embeds in the group of inner
automorphisms, or contains a noninner involution. In the second case its
inner kernel embeds in the literal fixed subgroup of that involution, and
the outer image contributes at most one generator.

This refines the coarse cyclic-outer bound and supplies the mixed-coset
step in the triality rank calculation used on printed p.356 of
Aschbacher--Smith (`refs/quasithin.pdf`).
-/

public section
namespace Theory.GroupTheory
open Subgroup

private theorem inner_injective {S : Type*} [Group S] (hz : center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (MulAut.conj : S →* MulAut S).ker.eq_bot_iff_forall.mpr
  intro x hx
  have hc : x ∈ center S := by
    rw [mem_center_iff]
    intro y
    have hy := MulEquiv.congr_fun (show MulAut.conj x = 1 from hx) y
    change x * y * x⁻¹ = y at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm
  simpa only [hz, mem_bot] using hc

/-- The inner kernel of an elementary subgroup outside `Inn(S)` fixes the
chosen outer involution. Bounding that fixed group saves the extra generator
in the coarse cyclic-outer estimate. -/
theorem automorphism_twoRank_le_of_cyclic_outer_fixed
    {S : Type*} [Group S] [Finite S] (hz : center S = ⊥)
    [IsCyclic (MulAut.Outer S)] {r : ℕ}
    (hr : primeRank 2 S ≤ r)
    (hfixed : ∀ a : MulAut S, a ^ 2 = 1 → a ∉ MulAut.innerSubgroup S →
      primeRank 2 a.fixedSubgroup + 1 ≤ r) :
    primeRank 2 (MulAut S) ≤ r := by
  let e : S ≃* MulAut.innerSubgroup S := MonoidHom.ofInjective (inner_injective hz)
  have hfix (a : MulAut S) (g : S)
      (h : a * MulAut.conj g = MulAut.conj g * a) : a g = g := by
    apply inner_injective hz
    have he : a * MulAut.conj g * a⁻¹ = MulAut.conj (a g) := by
      ext x
      simp
    rw [← he, h, mul_assoc, mul_inv_cancel, mul_one]
  have hout : primeRank 2 (MulAut.Outer S) ≤ 1 := by
    let P : Sylow 2 (MulAut.Outer S) := Classical.choice inferInstance
    exact P.primeRank_le_one_of_isCyclic inferInstance
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hEr : primeRank 2 E ≤ r := by
    by_cases hi : E ≤ MulAut.innerSubgroup S
    · let f : E →* S := e.symm.toMonoidHom.comp (Subgroup.inclusion hi)
      exact (primeRank_le_of_injective 2 f
        (e.symm.injective.comp (Subgroup.inclusion_injective hi))).trans hr
    · obtain ⟨a, haE, ha⟩ := SetLike.not_le_iff_exists.mp hi
      have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := E) a haE
      let π : E →* MulAut.Outer S :=
        (QuotientGroup.mk' (MulAut.innerSubgroup S)).comp E.subtype
      let j : π.ker →* MulAut.innerSubgroup S := {
        toFun x := ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
      let k : π.ker →* S := e.symm.toMonoidHom.comp j
      have hk (x : π.ker) : MulAut.conj (k x) = x.val.val :=
        congrArg Subtype.val (e.apply_symm_apply (j x))
      let f : π.ker →* a.fixedSubgroup := k.codRestrict _ (fun x => by
        rw [MulAut.mem_fixedSubgroup]
        apply hfix
        rw [hk]
        exact congrArg Subtype.val (mul_comm (⟨a, haE⟩ : E) x.val))
      have hf : Function.Injective f := by
        intro x y h
        have hxy := congrArg (fun z : a.fixedSubgroup => MulAut.conj z.val) h
        change MulAut.conj (k x) = MulAut.conj (k y) at hxy
        rw [hk, hk] at hxy
        exact Subtype.ext (Subtype.ext hxy)
      have hker := primeRank_le_of_injective 2 f hf
      have hb := primeRank_le_ker_add (p := 2) π
      have hc := hfixed a ha2 ha
      omega
  have htop : IsElementaryAbelian 2 (⊤ : Subgroup E) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x.val)) }
  have hc := (primeRank_le_iff_elementary_card_le E).mp hEr ⊤ htop
  simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using hc

end Theory.GroupTheory
