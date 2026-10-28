module
public import Theory.Representation.BinaryParabolicExteriorSquare.PointQuotient

/-!
# Forced point-parabolic subspaces of the exterior square

On the binary exterior six-space, every nonzero proper subspace invariant
under the natural point parabolic is the three-space 01,02,03. Radical
transvection differences first produce a nonzero vector in that three-space;
the Levi transvections generate it, and the quotient is irreducible.
Three plane-parabolic transvections also force their common fixed vectors
into the wedge line 01.

These calculations align the actual subgroup images in the compatible
natural/exterior marking in Aschbacher--Smith, The Classification of
Quasithin Groups, 13.8.29(3),(5), printed p.964. The exterior action is the
attributed ATLAS compound-matrix model imported above.
-/

public section

open Atlas.Order20160A8.Bivectors
namespace Representation.BinaryParabolicExteriorSquare.PointAlignment
open PlaneSpan

private theorem delta_02 (x : Six) : delta 0 2 x = ![x 3,0,x 5,0,0,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;>
    ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_13 (x : Six) : delta 1 3 x = ![x 2,0,0,x 5,0,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;>
    ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_21 (x : Six) : delta 2 1 x = ![0,x 0,0,0,0,x 4] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;>
    ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_31 (x : Six) : delta 3 1 x = ![0,0,x 0,0,0,x 3] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;>
    ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem delta_32 (x : Six) : delta 3 2 x = ![0,0,x 1,0,x 3,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;>
    ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

private theorem contains_first (P : Submodule Bit Six)
    (hP : ∀ i j : Fin 4, j ≠ 0 → i ≠ j →
      ∀ x ∈ P, exteriorMap (Matrix.transvection i j (1:Bit)) x ∈ P)
    (x : Six) (hx : x ∈ P) (hf : x ∈ firstSpace) (hne : x ≠ 0) : firstSpace ≤ P := by
  have hd (i j : Fin 4) (hj : j ≠ 0) (hij : i ≠ j)
      (y : Six) (hy : y ∈ P) : delta i j y ∈ P := P.sub_mem (hP i j hj hij y hy) hy
  have hb0 : (Pi.single 0 1 : Six) ∈ P := by
    by_cases h2 : x 2 = 0
    · by_cases h1 : x 1 = 0
      · have h0 : x 0 = 1 := by
          have hn0 : x 0 ≠ 0 := by
            intro hz
            apply hne
            ext i
            fin_cases i <;> simp_all [firstSpace]
          exact ((by decide : ∀ c : Bit, c = 0 ∨ c = 1) (x 0)).resolve_left hn0
        have hh := hd 1 3 (by decide) (by decide) _
          (hd 3 1 (by decide) (by decide) x hx)
        convert hh using 1
        ext i
        fin_cases i <;> simp [delta_31,delta_13,h0,hf.1]
      · have h11 : x 1 = 1 := ((by decide : ∀ c : Bit, c = 0 ∨ c = 1) (x 1)).resolve_left h1
        have hh := hd 1 3 (by decide) (by decide) _
          (hd 3 2 (by decide) (by decide) x hx)
        convert hh using 1
        ext i
        fin_cases i <;> simp [delta_32,delta_13,h11]
    · have h21 : x 2 = 1 := ((by decide : ∀ c : Bit, c = 0 ∨ c = 1) (x 2)).resolve_left h2
      have hh := hd 1 3 (by decide) (by decide) x hx
      convert hh using 1
      ext i
      fin_cases i <;> simp [delta_13,h21,hf.2.2]
  have hb1 : (Pi.single 1 1 : Six) ∈ P := by
    have hh := hd 2 1 (by decide) (by decide) _ hb0
    convert hh using 1
    ext i
    fin_cases i <;> simp [delta_21]
  have hb2 : (Pi.single 2 1 : Six) ∈ P := by
    have hh := hd 3 1 (by decide) (by decide) _ hb0
    convert hh using 1
    ext i
    fin_cases i <;> simp [delta_31]
  intro y hy
  have he : y = y 0 • Pi.single 0 1 + y 1 • Pi.single 1 1 + y 2 • Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp_all [firstSpace]
  rw [he]
  exact P.add_mem (P.add_mem (P.smul_mem _ hb0) (P.smul_mem _ hb1)) (P.smul_mem _ hb2)

/-- The point parabolic has exactly one proper nonzero submodule on the exterior six-space. -/
theorem invariant_subspaces (P : Submodule Bit Six)
    (hP : ∀ i j : Fin 4, j ≠ 0 → i ≠ j →
      ∀ x ∈ P, exteriorMap (Matrix.transvection i j (1:Bit)) x ∈ P) :
    P = ⊥ ∨ P = firstSpace ∨ P = ⊤ := by
  by_cases hz : P = ⊥
  · exact Or.inl hz
  right
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff _).mp hz
  have hf : firstSpace ≤ P := by
    by_cases hxf : x ∈ firstSpace
    · exact contains_first P hP x hx hxf hx0
    have hd (i j : Fin 4) (hj : j ≠ 0) (hij : i ≠ j) : delta i j x ∈ P :=
      P.sub_mem (hP i j hj hij x hx) hx
    by_cases h01 : delta 0 1 x = 0
    · have h3 : x 3 = 0 := by simpa [delta_01] using congrFun h01 1
      have h4 : x 4 = 0 := by simpa [delta_01] using congrFun h01 2
      have h5 : x 5 ≠ 0 := fun he => hxf ⟨h3,h4,he⟩
      apply contains_first P hP (delta 0 2 x) (hd 0 2 (by decide) (by decide))
      · rw [delta_02]; change _ ∧ _ ∧ _; simp
      · intro he
        exact h5 (by simpa [delta_02] using congrFun he 2)
    · apply contains_first P hP (delta 0 1 x) (hd 0 1 (by decide) (by decide)) _ h01
      rw [delta_01]; change _ ∧ _ ∧ _; simp
  exact PointQuotient.invariant_above_first P hf (fun i j _ hj hij => hP i j hj hij)

/-- The three-dimensional section is forced to be the standard point exterior subspace. -/
theorem eq_first_of_finrank_three (P : Submodule Bit Six)
    (hP : ∀ i j : Fin 4, j ≠ 0 → i ≠ j →
      ∀ x ∈ P, exteriorMap (Matrix.transvection i j (1:Bit)) x ∈ P)
    (hdim : Module.finrank Bit P = 3) : P = firstSpace := by
  rcases invariant_subspaces P hP with hz | he | ht
  · rw [hz,finrank_bot] at hdim
    contradiction
  · exact he
  · have hh : Module.finrank Bit P = 6 := by rw [ht]; simp [PlaneSpan.Six]
    omega

/-- Three plane-parabolic transvections already have the marked wedge line as fixed space. -/
theorem mem_point_of_fixed (x : Six)
    (h01 : exteriorMap (Matrix.transvection 0 1 (1:Bit)) x = x)
    (h10 : exteriorMap (Matrix.transvection 1 0 (1:Bit)) x = x)
    (h02 : exteriorMap (Matrix.transvection 0 2 (1:Bit)) x = x) : x ∈ pointSpace := by
  have h01' : delta 0 1 x = 0 := sub_eq_zero.mpr h01
  have h10' : delta 1 0 x = 0 := sub_eq_zero.mpr h10
  have h02' : delta 0 2 x = 0 := sub_eq_zero.mpr h02
  exact ⟨by simpa [delta_10] using congrFun h10' 3,
    by simpa [delta_10] using congrFun h10' 4,
    by simpa [delta_01] using congrFun h01' 1,
    by simpa [delta_01] using congrFun h01' 2,
    by simpa [delta_02] using congrFun h02' 2⟩

end Representation.BinaryParabolicExteriorSquare.PointAlignment
