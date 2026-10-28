module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Action
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Representatives

/-!
# Fixed geometry of the natural six-letter action

The even action is transitive on the fifteen nonzero duad vectors, so it
has no common fixed vector. Inside the exceptional subgroup, fixing the
duads {0,1} and {0,2} leaves only the identity and (4,5). The same calculation
is transported through the literal conjugation coordinates to the actual
relative centralizer used in C.1.37's application of B.2.20.

Source: Aschbacher--Smith C.1.37, printed pp.141--143, and B.3.4.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Stellmacher
open ChapterB.BaumannArgument
open scoped IsMulCommutative
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders.Six
universe u

namespace Model

/-- The natural A₆-module has no fixed vector. -/
theorem fixedSpace_alternating_eq_bot :
    fixedSpace rho (alternatingGroup (Fin 6)) = ⊥ := by
  apply bot_unique
  intro v hv
  by_contra hv0
  rw [Submodule.mem_bot] at hv0
  obtain ⟨g, hg⟩ := NaturalTransport.transitive_nonzero v
    (pairVector 4 5) hv0 pairVector45_ne_zero
  obtain ⟨h, hh⟩ := NaturalTransport.transitive_nonzero v
    (pairVector 0 1) hv0 pairVector01_ne_zero
  have hfix : ∀ a : alternatingGroup (Fin 6), rho a.val v = v :=
    (Representation.mem_invariants (rho.comp (alternatingGroup (Fin 6)).subtype) v).mp hv
  have he : pairVector 4 5 = pairVector 0 1 :=
    hg.symm.trans ((hfix g).trans ((hfix h).symm.trans hh))
  have hp := (pairVector_eq_iff (by decide : (4 : Fin 6) ≠ 5)
    (by decide : (0 : Fin 6) ≠ 1)).mp he
  exact (by decide : pair 4 5 ≠ pair 0 1) hp

theorem fixedCodim_alternating : fixedCodim rho (alternatingGroup (Fin 6)) = 4 := by
  have h := fixedCodim_add_finrank rho (alternatingGroup (Fin 6))
  have hbot : Module.finrank (ZMod 2) (fixedSpace rho (alternatingGroup (Fin 6))) = 0 := by
    rw [fixedSpace_alternating_eq_bot]
    exact Module.finrank_zero_of_subsingleton
  rw [hbot] at h
  rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at h
  norm_num at h
  exact h

private theorem pairVector_fixed_last (i j : Fin 6) (hi : i ≠ 4 ∧ i ≠ 5)
    (hj : j ≠ 4 ∧ j ≠ 5) : pairVector i j ∈ fixedSpace rho last := by
  apply (mem_fixedSpace_closure_iff rho {ChapterB.Offenders.pairSwap 6 2} _).mpr
  rintro a rfl
  rw [pairVector_map]
  change pairVector ((Equiv.swap 4 5) i) ((Equiv.swap 4 5) j) = pairVector i j
  simp only [Equiv.swap_apply_of_ne_of_ne hi.1 hi.2,
    Equiv.swap_apply_of_ne_of_ne hj.1 hj.2]

private theorem exceptional_pair_fixer : ∀ i : Fin 8,
    pair (exceptionalWords i 0) (exceptionalWords i 1) = pair 0 1 →
    pair (exceptionalWords i 0) (exceptionalWords i 2) = pair 0 2 →
    ∃ j : Fin 2, lineWords 0 j = exceptionalWords i := by decide

/-- The transposition subgroup is the pointwise fixer of its fixed hyperplane in E. -/
theorem last_pointwise_fixer : subspaceKernel rho (fixedSpace rho last) E = last := by
  apply le_antisymm
  · intro g hg
    have h01 := hg.2 _ (pairVector_fixed_last 0 1 (by decide) (by decide))
    have h02 := hg.2 _ (pairVector_fixed_last 0 2 (by decide) (by decide))
    rw [pairVector_map, pairVector_eq_iff (g.injective.ne (by decide)) (by decide)] at h01 h02
    obtain ⟨i, rfl⟩ := (mem_exceptional_iff g).mp hg.1
    exact (mem_last_iff _).mpr (exceptional_pair_fixer i h01 h02)
  · intro g hg
    refine ⟨last_le_exceptional hg, fun w hw => ?_⟩
    exact (Representation.mem_invariants (rho.comp last.subtype) w).mp hw ⟨g,hg⟩

end Model
namespace NaturalAction
variable {K : Type u} [Group K] {V : Subgroup K} [V.Normal]
  (d : NaturalAction V)

/-- The actual relative centralizer has image contained in the transposition subgroup. -/
theorem last_fixed_fixer_image_le :
    ((Model.E.comap d.q) ⊓ centralizer
      ((V ⊓ centralizer ((last.comap d.q : Subgroup K) : Set K) : Subgroup K) : Set K)).map d.q ≤
      last := by
  rintro g ⟨a, ha, rfl⟩
  rw [← Model.last_pointwise_fixer]
  refine ⟨ha.1, fun w hw => ?_⟩
  let v : V := d.coordinates.symm (Multiplicative.ofAdd w)
  have hvcoord : (d.coordinates v).toAdd = w := d.coordinates.apply_symm_apply _
  have hv : (v : K) ∈ V ⊓ centralizer ((last.comap d.q : Subgroup K) : Set K) := by
    refine ⟨v.property, fun b hb => ?_⟩
    have hfix : Model.rho (d.q b) w = w :=
      (Representation.mem_invariants (Model.rho.comp last.subtype) w).mp hw ⟨d.q b,hb⟩
    have he : MulAut.conjNormal b v = v := by
      apply d.coordinates.injective
      apply Multiplicative.toAdd.injective
      rw [d.action, hvcoord, hfix]
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
  have hcomm : (v : K) * a = a * (v : K) := ha.2 v hv
  have hfix : MulAut.conjNormal a v = v := by
    apply Subtype.ext
    change a * (v : K) * a⁻¹ = (v : K)
    rw [← hcomm, mul_inv_cancel_right]
  rw [← hvcoord, ← d.action, hfix]

end NaturalAction
end CFSG.Quasithin.ChapterC.NaturalSixControl
