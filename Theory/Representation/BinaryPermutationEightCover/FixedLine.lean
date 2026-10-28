module
public import Theory.Representation.BinaryPermutation.EightCoreOrbits

/-!
# The central line and weight-four vectors in the A₈ augmentation cover

The unique nonzero fixed word in the eight-point core is the constant word.
If a linear subspace containing it has a subgroup transitive off that line,
a vector and its complement have the same weight, forcing weight four.
These statements preserve the full core and do not pass to its six-dimensional
quotient. The source application supplies the actual residual action on V.

Source: Aschbacher–Smith Lemma 12.3.3, printed p.808, the augmentation-core
normalizer calculation.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.EightCore

theorem fixed_nonzero_eq_oneWord {v : core (Fin 8)}
    (hv : ∀ a : alternatingGroup (Fin 8), alternatingCoreRepresentation (Fin 8) a v = v)
    (hv0 : v ≠ 0) : v = oneWord := by
  obtain ⟨c,hc⟩ := (mem_constants_iff v.val).mp
    ((core_fixed_iff_constant (by simp : 3 ≤ Nat.card (Fin 8)) v).mp hv)
  have hc0 : c ≠ 0 := by
    intro hz
    apply hv0
    exact Subtype.ext (funext fun i => (hc i).trans hz)
  have hc1 : c = 1 := ((by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c).resolve_left hc0
  exact Subtype.ext (funext fun i => (hc i).trans hc1)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Transitivity off the fixed line forces the image to be a doubly-even
code: the fourteen vectors off that line all have weight four. -/
theorem weight_four_of_transitive_off_line
    (f : V →ₗ[ZMod 2] core (Fin 8)) {z : V} (hfz : f z = oneWord)
    (ht : ∀ x y : V, x ≠ 0 → y ≠ 0 → x ≠ z → y ≠ z →
      ∃ a : alternatingGroup (Fin 8), alternatingCoreRepresentation (Fin 8) a (f x) = f y)
    {x : V} (hx0 : x ≠ 0) (hxz : x ≠ z) : wordWeight (f x).val = 4 := by
  have hy0 : x + z ≠ 0 := by
    intro he
    have hzz : z + z = 0 := by
      calc
        z + z = ((1 : ZMod 2) + 1) • z := by rw [add_smul,one_smul]
        _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 from by decide,zero_smul]
    exact hxz (add_right_cancel (he.trans hzz.symm))
  have hyz : x + z ≠ z := by
    intro he
    exact hx0 (add_right_cancel (he.trans (zero_add z).symm))
  obtain ⟨a,ha⟩ := ht x (x+z) hx0 hy0 hxz hyz
  have hw := wordWeight_permute a.val (f x).val
  change wordWeight (alternatingCoreRepresentation (Fin 8) a (f x)).val = _ at hw
  rw [ha,map_add,hfz,weight_complement] at hw
  have hbound : wordWeight (f x).val ≤ 8 := by
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  omega

/-- A full augmentation marking sends any nonzero fixed vector to the
constant word. This keeps track of the original marked central line. -/
theorem marked_fixed_vector
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (C : Subgroup D)
    (a : C ≃* alternatingGroup (Fin 8)) (E : W ≃ₗ[ZMod 2] core (Fin 8))
    (he : ∀ c : C, ∀ w, E (ρ c.val w) = alternatingCoreRepresentation (Fin 8) (a c) (E w))
    {z : W} (hz : z ∈ fixedSpace ρ C) (hz0 : z ≠ 0) : E z = oneWord := by
  apply fixed_nonzero_eq_oneWord
  · intro g
    obtain ⟨c,rfl⟩ := a.surjective g
    rw [← he]
    exact congrArg E (hz c)
  · exact fun h => hz0 (E.injective (h.trans E.map_zero.symm))

end BinaryPermutation.EightCore
