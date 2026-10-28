module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ModuleCentralizer
public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer

/-!
# The field-prime condition for the natural binary-three block

The marked natural module transports each intertwiner to an additive map
commuting with SL₃(2). The transvection calculation makes this map a scalar,
hence zero or identity. Its unit group is trivial, so the prime set in C.1.10
is empty. The final lemma applies C.1.10 with only relative normality in the
local overgroup and the literal core-commutator hypothesis.

Source: Aschbacher–Smith, C.1.10 and proof of 12.4.6, printed pp.124,814.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open ChapterC ChapterC.ExceptionalRestrictions

private theorem end_eq_zero_or_one {A : Type*} [Group A]
    (hs : IsShort A)
    (hm : IsLinearBlockModel A (specialLinearNatural (k := ZMod 2) 3))
    (f : BlockEndRing hs) : f = 0 ∨ f = 1 := by
  let _ := hs.elementary
  let _ := hs.module_elementary
  obtain ⟨rho, ⟨model⟩, hmodel⟩ := hm
  let e : Additive (BlockModule A) ≃+ (Fin 3 → ZMod 2) := {
    toFun := fun v => (model.moduleIso v.toMul).toAdd
    invFun := fun v => Additive.ofMul (model.moduleIso.symm (Multiplicative.ofAdd v))
    left_inv := fun v => model.moduleIso.symm_apply_apply v
    right_inv := fun v => model.moduleIso.apply_symm_apply v
    map_add' := fun v w => model.moduleIso.map_mul v w }
  have he (g : A ⧸ pCore 2 A) (v : Additive (BlockModule A)) :
      e (moduleRepresentation hs g v) = specialLinearNatural 3 (model.quotientIso g) (e v) := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) g
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (blockFixed A) v.toMul
    have hv : v = Additive.ofMul (QuotientGroup.mk' (blockFixed A) u) := hu.symm
    rw [hv]
    change (model.moduleIso (hs.exists_quotient_moduleAction.choose
      (QuotientGroup.mk' (pCore 2 A) a) (QuotientGroup.mk' (blockFixed A) u))).toAdd = _
    rw [hs.exists_quotient_moduleAction.choose_spec, model.intertwining, hmodel]
    rfl
  let F : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
    e.toAddMonoidHom.comp (f.toLinearMap.toAddMonoidHom.comp e.symm.toAddMonoidHom)
  have hF (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
      F (g.val.mulVec v) = g.val.mulVec (F v) := by
    obtain ⟨a, rfl⟩ := model.quotientIso.surjective g
    obtain ⟨w, rfl⟩ := e.surjective v
    change e (f (e.symm (specialLinearNatural 3 (model.quotientIso a) (e w)))) =
      specialLinearNatural 3 (model.quotientIso a) (e (f (e.symm (e w))))
    rw [← he, e.symm_apply_apply, e.symm_apply_apply,
      f.isIntertwining, he]
  obtain ⟨c, hc⟩ := Representation.SL3DoubledNaturalOffenders.natural_centralizer_scalar F hF
  have hc' (v : Additive (BlockModule A)) : e (f v) = c • e v := by
    have hh := hc (e v)
    change e (f (e.symm (e v))) = c • e v at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  fin_cases c
  · left
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply e.injective
    exact (hc' v).trans (by change (0 : ZMod 2) • e v = e 0; simp)
  · right
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply e.injective
    exact (hc' v).trans (by change (1 : ZMod 2) • e v = e v; simp)

/-- The actual natural binary-three marking makes the endomorphism units trivial.
Thus the prime set in C.1.10 is empty. -/
theorem linearThree_blockEndPrimes_empty {A : Type*} [Group A]
    (h : IsLinearTwoBlock A 3) : blockEndPrimes h.2.1 = ∅ := by
  let _ := h.2.1.elementary
  let _ := h.2.1.module_elementary
  let _ := (blockEndRing_isField h.2.1).toField
  have hunit (a : (BlockEndRing h.2.1)ˣ) : a = 1 := by
    apply Units.ext
    rcases end_eq_zero_or_one h.2.1 h.2.2.2 a.val with hz | ho
    · have hne : (0 : BlockEndRing h.2.1) ≠ 1 := by
        let _ : Nontrivial (BlockEndRing h.2.1) :=
          ⟨(blockEndRing_isField h.2.1).exists_pair_ne⟩
        intro he
        obtain ⟨a, b, hab⟩ := (blockEndRing_isField h.2.1).exists_pair_ne
        apply hab
        calc
          a = a * 1 := (mul_one a).symm
          _ = a * 0 := congrArg (a * ·) he.symm
          _ = 0 := mul_zero a
          _ = b * 0 := (mul_zero b).symm
          _ = b * 1 := congrArg (b * ·) he
          _ = b := mul_one b
      have hh := a.val_inv
      rw [hz, zero_mul] at hh
      exact (hne hh).elim
    · exact ho
  have : Subsingleton (BlockEndRing h.2.1)ˣ := ⟨fun a b => (hunit a).trans (hunit b).symm⟩
  have hc : Nat.card (BlockEndRing h.2.1)ˣ = 1 := Nat.card_eq_one_iff_unique.mpr
    ⟨inferInstance, inferInstance⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact p.property.not_dvd_one (hc ▸ hp)

/-- C.1.10 on the genuine marked short group, with the field-prime condition
proved instead of assumed. Normality is only in the given local overgroup. -/
theorem linearThree_centralizes_of_coreQuotient {H : Type*} [Group H] [Finite H]
    (A Y : Subgroup H) [A.Normal] (hA : IsLinearTwoBlock A 3)
    (hY : IsPPerfect 2 Y) (hc : ⁅Y, A⁆ ≤ (pCore 2 A).map A.subtype) :
    Y ≤ centralizer (A : Set H) :=
  hA.2.1.centralizes_of_coreQuotient A Y hY
    (block_residual_condition_of_empty_primes hA.2.1 (linearThree_blockEndPrimes_empty hA)) hc
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
