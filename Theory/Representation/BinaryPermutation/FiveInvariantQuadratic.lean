module
public import Theory.Representation.BinaryPermutation.FiveAction

/-!
# The invariant square form in five-point coordinates

The two nonzero A₅ orbits determine every invariant nonzero binary quadratic
form which vanishes at a singular point. It is the minus form. A subgroup
consisting of singular vectors consequently has order at most two.

Source: Aschbacher–Smith, the orthogonal A₅ module in B.3 and the
field-four case of 14.2.16, printed pp.985–986.
-/

public noncomputable section
open Subgroup Module Representation
open scoped IsMulCommutative
namespace BinaryPermutation.FiveGeometry

private theorem binary_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem eq_form_of_invariant_seed
    (q : QuadraticForm (ZMod 2) (core (Fin 5))) (hq : q ≠ 0)
    (hinv : ∀ a : alternatingGroup (Fin 5), ∀ x,
      q (coreRepresentation (Fin 5) a.val x) = q x)
    (w : core (Fin 5)) (hw : w ≠ 0) (hqw : q w = 0) (hfw : form w = 0) :
    q = form := by
  have hs (x : core (Fin 5)) (hx : form x = 0) : q x = 0 := by
    by_cases hx0 : x = 0
    · simp [hx0]
    obtain ⟨a,ha⟩ := exists_even_transport w x hw hx0 (hfw.trans hx.symm)
    rw [←ha,hinv,hqw]
  have hn (x : core (Fin 5)) (hx : form x ≠ 0) : q x ≠ 0 := by
    intro hxq
    apply hq
    ext y
    by_cases hy : form y = 0
    · exact hs y hy
    have hvalues : form x = form y := by
      rcases binary_cases (form x) with hh | hh
      · exact (hx hh).elim
      rcases binary_cases (form y) with hh' | hh'
      · exact (hy hh').elim
      exact hh.trans hh'.symm
    obtain ⟨a,ha⟩ := exists_even_transport x y
      (fun he => hx (he ▸ map_zero form)) (fun he => hy (he ▸ map_zero form)) hvalues
    rw [←ha,hinv,hxq]
    rfl
  ext x
  rcases binary_cases (form x) with hx | hx
  · exact (hs x hx).trans hx.symm
  · rcases binary_cases (q x) with hh | hh
    · exact (hn x (hx ▸ one_ne_zero) hh).elim
    · exact hh.trans hx.symm

/-- A singular subgroup in five-point coordinates has at most two elements. -/
theorem card_le_two_of_all_singular (A : Subgroup (Multiplicative (core (Fin 5))))
    (hA : ∀ a : A, form a.val.toAdd = 0) : Nat.card A ≤ 2 := by
  by_cases hn : A = ⊥
  · simp [hn]
  · have he := card_eq_two_of_singular ⊤ A le_top
      (Subgroup.topEquiv : (⊤ : Subgroup (Multiplicative (core (Fin 5)))) ≃* _) hn
      (fun a => hA a)
    exact he.le

end BinaryPermutation.FiveGeometry
