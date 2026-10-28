module

public import Theory.SpecificGroups.BinaryLinear.FourSevenGraph
public import Theory.SpecificGroups.BinaryLinear.FiveSevenGraph
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# Seven-element conjugacy detects inner automorphisms

In degrees four and five over F₂, an automorphism preserving the conjugacy
class of a seven-element is inner. Correct it by a conjugator to fix that
element; inner/graph coverage and the reciprocal-polynomial calculation
exclude the graph case. This applies to a marked subgroup without classifying
its embedding in the larger binary group.

Source: Aschbacher--Smith, 12.9, printed pp.862--864.
-/

public section
namespace BinaryLinear
open OuterCyclic

/-- Preserving a seven-element conjugacy class excludes the graph coset. -/
theorem inner_of_seven_conjugacy {d : ℕ} (hd : d = 4 ∨ d = 5)
    (x : LinearGroup d) (hx : orderOf x = 7) (a : MulAut (LinearGroup d))
    (hconj : IsConj x (a x)) : a ∈ MulAut.innerSubgroup (LinearGroup d) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let b := MulAut.conj g⁻¹ * a
  have hbfix : b x = x := by
    change g⁻¹ * a x * (g⁻¹)⁻¹ = x
    rw [← hg]
    group
  have hb : b ∈ MulAut.innerSubgroup (LinearGroup d) := by
    obtain ⟨k,hk | hk⟩ := inner_graph hd b
    · exact ⟨k,hk.symm⟩
    · have hp : x ^ 7 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
      have he : x = 1 := by
        rcases hd with rfl | rfl
        · exact FourSevenGraph.graph_fixed_seven_eq_one k x hp (hk ▸ hbfix)
        · exact FiveSevenGraph.graph_fixed_seven_eq_one k x hp (hk ▸ hbfix)
      rw [he,orderOf_one] at hx
      omega
  have he : a = MulAut.conj g * b := by
    dsimp [b]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [he]
  exact (MulAut.innerSubgroup _).mul_mem ⟨g,rfl⟩ hb

end BinaryLinear
