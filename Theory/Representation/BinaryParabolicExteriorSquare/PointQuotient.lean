module
public import Theory.Representation.BinaryParabolicExteriorSquare.PlaneSpan
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The point-parabolic quotient of the exterior six-space

The natural point stabilizer preserves the exterior three-space with
coordinates 01, 02, 03. Its transvections on coordinates 1, 2, 3 act
irreducibly on the quotient with coordinates 12, 13, 23: transvection
differences extract a nonzero basis vector, then generate the other two.
Thus every invariant subspace containing the first three-space is either
that three-space or the whole exterior module.

This supplies the quotient irreducibility used in the exact intersection
in Aschbacher–Smith, The Classification of Quasithin Groups, 13.8.29(3),
printed p.964. The exterior model retains the imported ATLAS attribution.
-/

public section
open Atlas.Order20160A8.Bivectors
namespace Representation.BinaryParabolicExteriorSquare.PointQuotient
open PlaneSpan
private theorem delta_13 (x : Six) : delta 1 3 x = ![x 2,0,0,x 5,0,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_23 (x : Six) : delta 2 3 x = ![0,x 2,0,x 4,0,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_31 (x : Six) : delta 3 1 x = ![0,0,x 0,0,0,x 3] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_32 (x : Six) : delta 3 2 x = ![0,0,x 1,0,x 3,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;> ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

/-- The point parabolic is irreducible on the quotient by the first exterior three-space. -/
theorem invariant_above_first (P : Submodule Bit Six) (hfirst : firstSpace ≤ P)
    (hP : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j →
      ∀ x ∈ P, exteriorMap (Matrix.transvection i j (1:Bit)) x ∈ P) :
    P = firstSpace ∨ P = ⊤ := by
  classical
  by_cases hp : P ≤ firstSpace
  · exact Or.inl (le_antisymm hp hfirst)
  right
  have hd (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j)
      (x : Six) (hx : x ∈ P) : delta i j x ∈ P :=
    P.sub_mem (hP i j hi hj hij x hx) hx
  obtain ⟨x,hx,hxf⟩ : ∃ x ∈ P, x ∉ firstSpace := by
    by_contra hn
    apply hp
    intro x hx
    by_contra hxf
    exact hn ⟨x,hx,hxf⟩
  let y : Six := ![0,0,0,x 3,x 4,x 5]
  have hy : y ∈ P := by
    have hu : (![x 0,x 1,x 2,0,0,0] : Six) ∈ P :=
      hfirst (by change _ ∧ _ ∧ _; simp)
    have hh := P.sub_mem hx hu
    convert hh using 1
    ext i
    fin_cases i <;> simp [y]
  have hb3 : (Pi.single 3 1 : Six) ∈ P := by
    by_cases h3 : x 3 = 0
    · by_cases h4 : x 4 = 0
      · have h5 : x 5 ≠ 0 := fun h5 => hxf ⟨h3,h4,h5⟩
        have h51 : x 5 = 1 := ((by decide : ∀ c : Bit, c = 0 ∨ c = 1) (x 5)).resolve_left h5
        have hh := hd 1 3 (by decide) (by decide) (by decide) y hy
        convert hh using 1
        ext i
        fin_cases i <;> simp [delta_13,y,h51]
      · have h41 : x 4 = 1 := ((by decide : ∀ c : Bit, c = 0 ∨ c = 1) (x 4)).resolve_left h4
        have hh := hd 2 3 (by decide) (by decide) (by decide) y hy
        convert hh using 1
        ext i
        fin_cases i <;> simp [delta_23,y,h41]
    · have h31 : x 3 = 1 := ((by decide : ∀ c : Bit, c = 0 ∨ c = 1) (x 3)).resolve_left h3
      have hh := hd 1 3 (by decide) (by decide) (by decide) _
        (hd 3 1 (by decide) (by decide) (by decide) y hy)
      convert hh using 1
      ext i
      fin_cases i <;> simp [delta_13,delta_31,y,h31]
  have hb (i : Fin 6) : (Pi.single i 1 : Six) ∈ P := by
    fin_cases i
    · exact hfirst (by change _ ∧ _ ∧ _; simp)
    · exact hfirst (by change _ ∧ _ ∧ _; simp)
    · exact hfirst (by change _ ∧ _ ∧ _; simp)
    · exact hb3
    · have hh := hd 3 2 (by decide) (by decide) (by decide) _ hb3
      convert hh using 1
      ext i
      fin_cases i <;> simp [delta_32]
    · have hh := hd 3 1 (by decide) (by decide) (by decide) _ hb3
      convert hh using 1
      ext i
      fin_cases i <;> simp [delta_31]
  apply top_unique
  intro v _
  rw [← (Pi.basisFun Bit (Fin 6)).sum_repr v]
  apply Submodule.sum_mem
  intro i _
  exact P.smul_mem _ (by simpa only [Pi.basisFun_apply] using hb i)

end Representation.BinaryParabolicExteriorSquare.PointQuotient
