module

public import Theory.SpecificGroups.SU3.EvenSemilinear.Coordinates

/-!
# Torus and Weyl coset from the two unitary root groups

The intersection of the normalizers of the upper and opposite root groups
is the actual projective diagonal torus. An upper root element with first
coordinate one forces a normalizing matrix to preserve its unique fixed
line. The opposite root imposes the opposite column condition; unitarity and
determinant one then force a torus matrix.

Only existence of that coordinate is needed, including characteristic two.
An automorphism preserving both roots therefore preserves the torus and
sends the Weyl element into its torus coset. This adapts the existing odd
characteristic proof without changing its public interfaces.
Source: Steinberg, Theorem 36, steps (1)–(5),
`refs/KGroup/GLS3/Chapter2St1.tex`; concrete matrices: Huppert II.10.12.
-/

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private theorem weylGL_sq :
    (hermitianWeylGL : GL (Fin 3) E) * hermitianWeylGL = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylGL, hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem weyl_sq : weyl J hJ * weyl J hJ = 1 := by
  apply Subtype.ext
  change ProjGenLinGroup.mk hermitianWeylGL * ProjGenLinGroup.mk hermitianWeylGL = 1
  rw [← map_mul, weylGL_sq, map_one]

private theorem weyl_inv : (weyl J hJ)⁻¹ = weyl J hJ :=
  inv_eq_of_mul_eq_one_left (weyl_sq J hJ)

private theorem weyl_swaps_opposite :
    (oppositeRootGroup J hJ).map (MulAut.conj (weyl J hJ)).toMonoidHom =
      rootGroup J hJ := by
  rw [oppositeRootGroup_eq_map, Subgroup.map_map]
  have hh : (MulAut.conj (weyl J hJ)).toMonoidHom.comp
      (MulAut.conj (weyl J hJ)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    change weyl J hJ * (weyl J hJ * x * (weyl J hJ)⁻¹) * (weyl J hJ)⁻¹ = x
    rw [weyl_inv]
    have hw := weyl_sq J hJ
    calc
      _ = (weyl J hJ * weyl J hJ) * x * (weyl J hJ * weyl J hJ) := by group
      _ = x := by rw [hw, one_mul, mul_one]
  rw [hh, Subgroup.map_id]

private theorem normalizer_first_column (hfirst : ∃ z : hermitianUnipotentCoord J, z.val.1 = 1)
    (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (hg : g ∈ Subgroup.normalizer (rootGroup J hJ))
    (A : GL (Fin 3) E) (hA : ProjGenLinGroup.mk A = g.val) :
    A.val 1 0 = 0 ∧ A.val 2 0 = 0 := by
  obtain ⟨t, ht⟩ := hfirst
  obtain ⟨z, hz⟩ := (Subgroup.mem_normalizer_iff''.mp hg (root J hJ t)).mp
    (show root J hJ t ∈ rootGroup J hJ from ⟨t, rfl⟩)
  have he : g * root J hJ z = root J hJ t * g := by
    rw [hz]
    group
  have hp : ProjGenLinGroup.mk (A * hermitianUnipotentGL J z) =
      ProjGenLinGroup.mk (hermitianUnipotentGL J t * A) := by
    simpa only [map_mul, hA, hermitianUnipotentPSU_val, Subgroup.coe_mul] using
      congrArg Subtype.val he
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have h0 := congrArg (fun M : GL (Fin 3) E => M.val 0 0) hc
  have h1 := congrArg (fun M : GL (Fin 3) E => M.val 1 0) hc
  have h2' := congrArg (fun M : GL (Fin 3) E => M.val 2 0) hc
  simp [GeneralLinearGroup.coe_scalar, hermitianUnipotentMatrix,
    Matrix.mul_apply, Fin.sum_univ_three, ht] at h0 h1 h2'
  by_cases hc1 : (c : E) = 1
  · rw [hc1, mul_one] at h0 h1
    have h20 : A.val 2 0 = 0 := by linear_combination h1
    refine ⟨?_, h20⟩
    rw [h20] at h0
    linear_combination -h0
  · have h20 : A.val 2 0 = 0 := by
      exact (mul_eq_zero.mp (show A.val 2 0 * ((c : E) - 1) = 0 by
        linear_combination h2')).resolve_right (sub_ne_zero.mpr hc1)
    refine ⟨?_, h20⟩
    exact (mul_eq_zero.mp (show A.val 1 0 * ((c : E) - 1) = 0 by
      rw [h20] at h1
      linear_combination h1)).resolve_right (sub_ne_zero.mpr hc1)

private theorem opposite_normalizer_last_column (hfirst : ∃ z : hermitianUnipotentCoord J, z.val.1 = 1)
    (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (hg : g ∈ Subgroup.normalizer (oppositeRootGroup J hJ))
    (A : GL (Fin 3) E) (hA : ProjGenLinGroup.mk A = g.val) :
    A.val 1 2 = 0 ∧ A.val 0 2 = 0 := by
  have hn : (MulAut.conj (weyl J hJ)) g ∈ Subgroup.normalizer (rootGroup J hJ) := by
    rw [← weyl_swaps_opposite J hJ]
    exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hg)
  have hproj : ProjGenLinGroup.mk (hermitianWeylGL * A * hermitianWeylGL) =
      ((MulAut.conj (weyl J hJ)) g).val := by
    change _ = ((weyl J hJ * g * (weyl J hJ)⁻¹).val)
    simp only [Subgroup.coe_mul, weyl_inv, hermitianWeylPSU_val, map_mul, hA]
  have hz := normalizer_first_column J hJ hfirst _ hn _ hproj
  simpa [hermitianWeylGL, hermitianWeylMatrix, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail] using hz

include hJ in
private theorem torus_of_columns (A : GL (Fin 3) E) (hA : A ∈ J.specialSubgroup)
    (h10 : A.val 1 0 = 0) (h20 : A.val 2 0 = 0)
    (h12 : A.val 1 2 = 0) (h02 : A.val 0 2 = 0) :
    ∃ k : Eˣ, A = hermitianTorusGL J k := by
  have hu := (J.mem_specialSubgroup_iff A).mp hA |>.1
  rw [hJ] at hu
  have h01 := congrArg (fun X : Matrix (Fin 3) (Fin 3) E => X 0 1) hu
  have h21 := congrArg (fun X : Matrix (Fin 3) (Fin 3) E => X 2 1) hu
  have h02' := congrArg (fun X : Matrix (Fin 3) (Fin 3) E => X 0 2) hu
  have hac : J.conj (A.val 0 0) * A.val 2 2 = 1 := by
    simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
      h10, h20, h12, h02] using h02'
  have ha0 : J.conj (A.val 0 0) ≠ 0 := left_ne_zero_of_mul_eq_one hac
  have hc0 : A.val 2 2 ≠ 0 := right_ne_zero_of_mul_eq_one hac
  have h21' : A.val 2 1 = 0 := by
    have hh : J.conj (A.val 0 0) * A.val 2 1 = 0 := by
      simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
        h10, h20, h12, h02] using h01
    exact (mul_eq_zero.mp hh).resolve_left ha0
  have h01' : A.val 0 1 = 0 := by
    have hh : J.conj (A.val 2 2) * A.val 0 1 = 0 := by
      simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
        h10, h20, h12, h02] using h21
    exact (mul_eq_zero.mp hh).resolve_left ((map_ne_zero J.conj).2 hc0)
  have hac' : A.val 0 0 * J.conj (A.val 2 2) = 1 := by
    have hh := congrArg J.conj hac
    rw [map_mul, map_one, J.conj_involutive] at hh
    exact hh
  have haDiag : A.val 0 0 = (J.conj (A.val 2 2))⁻¹ :=
    eq_inv_of_mul_eq_one_left hac'
  have hd := congrArg Units.val ((J.mem_specialSubgroup_iff A).mp hA |>.2)
  have hd' : A.val 0 0 * A.val 1 1 * A.val 2 2 = 1 := by
    simpa [Matrix.det_fin_three, h10, h20, h12, h02, h21', h01'] using hd
  have hm : A.val 1 1 * A.val 2 2 = J.conj (A.val 2 2) := by
    have hh := congrArg (fun x : E => J.conj (A.val 2 2) * x) hd'
    rw [haDiag] at hh
    simpa [(map_ne_zero J.conj).2 hc0, mul_assoc] using hh
  have hmDiag : A.val 1 1 = J.conj (A.val 2 2) * (A.val 2 2)⁻¹ := by
    apply (mul_right_cancel₀ hc0)
    rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one]
    exact hm
  refine ⟨Units.mk0 (A.val 2 2) hc0, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusGL, hermitianTorusMatrix, h10, h20, h12, h02,
      h21', h01', haDiag, hmDiag]

private theorem normalizer_inf_le_rootTorus (hfirst : ∃ z : hermitianUnipotentCoord J, z.val.1 = 1) :
    Subgroup.normalizer (rootGroup J hJ) ⊓
      Subgroup.normalizer (oppositeRootGroup J hJ) ≤ rootTorus J hJ := by
  intro g hg
  obtain ⟨A, hA, hAg⟩ := g.property
  have hcol := normalizer_first_column J hJ hfirst g hg.1 A hAg
  have hcol' := opposite_normalizer_last_column J hJ hfirst g hg.2 A hAg
  obtain ⟨k, hk⟩ := torus_of_columns J hJ A hA hcol.1 hcol.2 hcol'.1 hcol'.2
  refine ⟨k, ?_⟩
  apply Subtype.ext
  simpa only [hermitianTorusPSU_val, ← hk] using hAg

private theorem weyl_conj_torus (k : Eˣ) :
    (MulAut.conj (weyl J hJ)) (hermitianTorusPSU J hJ k) =
      hermitianTorusPSU J hJ ((Units.map J.conj.toMonoidHom k)⁻¹) := by
  change weyl J hJ * hermitianTorusPSU J hJ k * (weyl J hJ)⁻¹ = _
  rw [weyl_inv]
  apply Subtype.ext
  change ProjGenLinGroup.mk hermitianWeylGL * ProjGenLinGroup.mk (hermitianTorusGL J k) *
    ProjGenLinGroup.mk hermitianWeylGL =
      ProjGenLinGroup.mk (hermitianTorusGL J ((Units.map J.conj.toMonoidHom k)⁻¹))
  rw [← map_mul, ← map_mul]
  apply congrArg ProjGenLinGroup.mk
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusGL, hermitianTorusMatrix, hermitianWeylGL,
      hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      J.conj_involutive (k : E), mul_comm]

private theorem torus_mem_root_normalizer [Finite E] (k : Eˣ) :
    hermitianTorusPSU J hJ k ∈ Subgroup.normalizer (rootGroup J hJ) := by
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨z, rfl⟩
  refine ⟨hermitianTorusAction J k z, ?_⟩
  rw [hermitianTorusPSU_mul_unipotent, mul_assoc, mul_inv_cancel, mul_one]

/-- The projective torus is the common normalizer of the two opposite roots. -/
public theorem rootTorus_eq_normalizer_inf [Finite E] (hfirst : ∃ z : hermitianUnipotentCoord J, z.val.1 = 1) :
    rootTorus J hJ = Subgroup.normalizer (rootGroup J hJ) ⊓
      Subgroup.normalizer (oppositeRootGroup J hJ) := by
  apply le_antisymm _ (normalizer_inf_le_rootTorus J hJ hfirst)
  rintro _ ⟨k, rfl⟩
  refine ⟨torus_mem_root_normalizer J hJ k, ?_⟩
  let f := (MulAut.conj (weyl J hJ)).toMonoidHom
  have hm : f (hermitianTorusPSU J hJ k) ∈ Subgroup.normalizer (rootGroup J hJ) := by
    rw [show f _ = _ from weyl_conj_torus J hJ k]
    exact torus_mem_root_normalizer J hJ _
  have hh := Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f hm)
  rw [← oppositeRootGroup_eq_map] at hh
  have hid : f (f (hermitianTorusPSU J hJ k)) = hermitianTorusPSU J hJ k := by
    change weyl J hJ * (weyl J hJ * _ * (weyl J hJ)⁻¹) * (weyl J hJ)⁻¹ = _
    rw [weyl_inv]
    calc
      _ = (weyl J hJ * weyl J hJ) * hermitianTorusPSU J hJ k *
        (weyl J hJ * weyl J hJ) := by group
      _ = _ := by rw [weyl_sq, one_mul, mul_one]
  exact hid ▸ hh

/-- Preserving both root subgroups preserves the actual projective torus. -/
public theorem rootTorus_map_eq [Finite E] (hfirst : ∃ z : hermitianUnipotentCoord J, z.val.1 = 1)
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hV : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ) :
    (rootTorus J hJ).map b.toMonoidHom = rootTorus J hJ := by
  rw [rootTorus_eq_normalizer_inf J hJ hfirst,
    Subgroup.map_inf _ _ _ b.injective, Subgroup.map_equiv_normalizer_eq,
    Subgroup.map_equiv_normalizer_eq, hU, hV]

private theorem conjugate_map_of_invariant {G : Type*} [Group G]
    (b : MulAut G) (H : Subgroup G) (hH : H.map b.toMonoidHom = H) (w : G) :
    H.map (MulAut.conj (b w)).toMonoidHom =
      (H.map (MulAut.conj w).toMonoidHom).map b.toMonoidHom := by
  have he : (MulAut.conj (b w)).toMonoidHom.comp b.toMonoidHom =
      b.toMonoidHom.comp (MulAut.conj w).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    simp [MulAut.conj_apply]
  calc
    _ = (H.map b.toMonoidHom).map (MulAut.conj (b w)).toMonoidHom := by rw [hH]
    _ = _ := by rw [Subgroup.map_map, he, ← Subgroup.map_map]

/-- The image of the Weyl element lies in its original torus coset. -/
public theorem exists_torus_mul_weyl_of_root_preserving [Finite E] (hfirst : ∃ z : hermitianUnipotentCoord J, z.val.1 = 1)
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hV : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ) :
    ∃ k : Eˣ, b (weyl J hJ) = hermitianTorusPSU J hJ k * weyl J hJ := by
  have hbU : (rootGroup J hJ).map (MulAut.conj (b (weyl J hJ))).toMonoidHom =
      oppositeRootGroup J hJ := by
    rw [conjugate_map_of_invariant b _ hU, ← oppositeRootGroup_eq_map, hV]
  have hbV : (oppositeRootGroup J hJ).map (MulAut.conj (b (weyl J hJ))).toMonoidHom =
      rootGroup J hJ := by
    rw [conjugate_map_of_invariant b _ hV, weyl_swaps_opposite, hU]
  have hf : (MulAut.conj (b (weyl J hJ) * (weyl J hJ)⁻¹)).toMonoidHom =
      (MulAut.conj (b (weyl J hJ))).toMonoidHom.comp
        (MulAut.conj (weyl J hJ)).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp only [_root_.mul_inv_rev, weyl_inv]
    group
  have hc : b (weyl J hJ) * (weyl J hJ)⁻¹ ∈ rootTorus J hJ := by
    rw [rootTorus_eq_normalizer_inf J hJ hfirst]
    constructor
    · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      change (rootGroup J hJ).map
        (MulAut.conj (b (weyl J hJ) * (weyl J hJ)⁻¹)).toMonoidHom = _
      rw [hf, ← Subgroup.map_map, ← oppositeRootGroup_eq_map, hbV]
    · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      change (oppositeRootGroup J hJ).map
        (MulAut.conj (b (weyl J hJ) * (weyl J hJ)⁻¹)).toMonoidHom = _
      rw [hf, ← Subgroup.map_map, weyl_swaps_opposite, hbU]
  obtain ⟨k, hk⟩ := hc
  refine ⟨k, ?_⟩
  rw [hk]
  group


end BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
