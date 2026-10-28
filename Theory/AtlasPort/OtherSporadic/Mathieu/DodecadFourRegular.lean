/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadProjectionSurjective
public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadProjectionKernel
public import Theory.AtlasPort.OtherSporadic.GroupTheory.FreeActionCard

/-!
# DodecadFourRegular

The affine dodecad stabilizer acts regularly on the eight points outside its fixed
tetrad. Its Klein quotient and two-element kernel give order eight, while fifth-point
fixation proves the action is free.

Source: `Atlas/Mathieu/DodecadFourRegular.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

theorem dodecadAffineStabilizer_card (i : HexIndex) (p : DodecadParameters i) :
    Nat.card (dodecadAffineStabilizer i p) = 8 := by
  obtain ⟨j,hj,_⟩ := hexZeroCoordinate_unique_other_zero i p.1.val p.1.prop
  let f := dodecadKleinProjection i p j hj.1 hj.2
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr
    (dodecadKleinProjection_surjective i p j hj.1 hj.2),Subgroup.card_top] at hc
  rw [dodecadKleinProjection_kernel_card,hexFiberPermutation_kernel_card i j hj.1.symm] at hc
  exact hc.symm

abbrev DodecadRemainingPoints (i : HexIndex) (p : DodecadParameters i) :=
  {z : Omega // z ∈ (dodecadParametersSupport i p).val.val \ tetrad i}

theorem dodecadRemainingPoints_card (i : HexIndex) (p : DodecadParameters i) :
    Nat.card (DodecadRemainingPoints i p) = 8 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,
    Finset.card_sdiff_of_subset (dodecadParametersSupport i p).prop,
    dodecad_size _ (dodecadParametersSupport i p).val.prop,tetrad_card]

def dodecadAffineToTetrad (i : HexIndex) (p : DodecadParameters i) :
    dodecadAffineStabilizer i p →* TetradPointStabilizer i :=
  (tetradPointStabilizerEquiv i).toMonoidHom.comp (dodecadAffineStabilizer i p).subtype

theorem dodecadAffineToTetrad_injective (i : HexIndex) (p : DodecadParameters i) :
    Function.Injective (dodecadAffineToTetrad i p) :=
  (tetradPointStabilizerEquiv i).injective.comp Subtype.val_injective

theorem dodecadAffineToTetrad_preserves (i : HexIndex) (p : DodecadParameters i)
    (x : dodecadAffineStabilizer i p) :
    permuteBlock (dodecadAffineToTetrad i p x).val.val (dodecadParametersSupport i p).val.val =
      (dodecadParametersSupport i p).val.val := by
  have hx := (dodecadAffineStabilizer_mem i p x.val).mp x.prop
  exact (coordinatePermutation_support _ _).symm.trans (congrArg support hx)

instance dodecadRemainingAction (i : HexIndex) (p : DodecadParameters i) :
    MulAction (dodecadAffineStabilizer i p) (DodecadRemainingPoints i p) where
  smul x z := ⟨(dodecadAffineToTetrad i p x).val.val z.val,by
    obtain ⟨hz,hzi⟩ := Finset.mem_sdiff.mp z.prop
    let g := dodecadAffineToTetrad i p x
    have hd : g.val.val z.val ∈ (dodecadParametersSupport i p).val.val := by
      have hm : g.val.val z.val ∈ permuteBlock g.val.val (dodecadParametersSupport i p).val.val :=
        Finset.mem_image.mpr ⟨z.val,hz,rfl⟩
      have he := dodecadAffineToTetrad_preserves i p x
      change permuteBlock g.val.val _ = _ at he
      simpa only [he] using hm
    refine Finset.mem_sdiff.mpr ⟨hd,?_⟩
    intro ht
    have hg : g.val.val (g.val.val z.val) = g.val.val z.val := g.prop ⟨_,ht⟩
    have he := g.val.val.injective hg
    exact hzi (he ▸ ht)⟩
  one_smul z := by apply Subtype.ext; change (dodecadAffineToTetrad i p 1).val.val z.val = z.val; rw [map_one]; rfl
  mul_smul x y z := by
    apply Subtype.ext
    change (dodecadAffineToTetrad i p (x*y)).val.val z.val = _
    rw [map_mul]
    rfl

theorem dodecadRemaining_free (i : HexIndex) (p : DodecadParameters i)
    (z : DodecadRemainingPoints i p) (x : dodecadAffineStabilizer i p)
    (hx : x • z = z) : x = 1 := by
  have hz := Finset.mem_sdiff.mp z.prop
  have hi : z.val.1 ≠ i := fun he => hz.2 ((mem_tetrad _ _).mpr he)
  have hg := dodecad_tetrad_fifth_fixed i p (dodecadAffineToTetrad i p x)
    (dodecadAffineToTetrad_preserves i p x) z.val hz.1 hi (congrArg Subtype.val hx)
  apply dodecadAffineToTetrad_injective i p
  rw [map_one]
  exact hg

theorem dodecadRemaining_regular (i : HexIndex) (p : DodecadParameters i)
    (z w : DodecadRemainingPoints i p) :
    ∃! x : dodecadAffineStabilizer i p, x • z = w := by
  let : Finite (dodecadAffineStabilizer i p) :=
    Finite.of_injective _ (dodecadAffineToTetrad_injective i p)
  apply Atlas.GroupTheory.unique_smul_of_free_card _ (dodecadRemaining_free i p) z w
  rw [dodecadAffineStabilizer_card,dodecadRemainingPoints_card]

end Atlas.Codes
