module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.ProjectiveTori
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.SU3.EvenSemilinear.Torus

/-!
# Inner normalization of unitary Sylow–involution pairs

The natural isotropic-point action sends the two points selected by a Sylow
normalizer and an outside involution to the standard opposite points. The
resulting actual group conjugator sends the involution into the torus–Weyl
coset. An odd-order power of its product with the Weyl involution corrects
the involution while preserving the standard Sylow and full torus.

The point-action calculation is adapted from the checked `Unitary.Normalization`
proof, retaining its inner conjugator rather than just the automorphism.
Source: GLS4, Chapter 4, Lemma 3.2(c),(i); Huppert II.10.12.
-/

open Matrix BenderSuzuki.External
open scoped LinearAlgebra.Projectivization
namespace BenderSuzuki.ZD.RankOneModelGeometry.PairNormalization
open PFAppendixIII PFchapter1section1 Subgroup
open _root_.BenderSuzuki.MatrixGroups _root_.BenderSuzuki.MatrixGroups.HermitianForm
open OddPrimeSylow.NormalizedOuter.Coverage

private abbrev isotropicPoints {E : Type*} [Field E] (J : HermitianForm 3 E) :=
  {x : ℙ E (Fin 3 → E) // ∃ (v : Fin 3 → E) (hv : v ≠ 0),
    x = Projectivization.mk E v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}

private theorem unitary_root_action {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    ∃ (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm (isotropicPoints J))
      (alpha : isotropicPoints J),
      (∀ u ∈ rootGroup J hJ, rho u alpha = alpha) ∧
      (∀ g, rho g alpha = alpha → g ∈ normalizer (rootGroup J hJ : Set _)) ∧
      (∀ x y, x ≠ alpha → y ≠ alpha →
        ∃! u : rootGroup J hJ, rho u.val x = y) ∧
      (∀ x y z t, x ≠ y → z ≠ t →
        ∃ g, rho g x = z ∧ rho g y = t) := by
  obtain ⟨_, rho, alpha, _, _, _, hroot, htwo, _⟩ :=
    huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R, _, hRfix, _, hRnorm, _, _, _, _, _, _, _, hregular,
    ⟨coord, hcoord⟩, _⟩ := hroot
  have hcoord_eq (z : hermitianUnipotentCoord J) :
      (coord z).val = root J hJ z := by
    obtain ⟨M, hM, heq⟩ := hcoord z
    have hM' : M = hermitianUnipotentGL J z := Units.ext hM
    apply Subtype.ext
    simpa only [hM', hermitianUnipotentPSU_val] using heq
  have hR : R = rootGroup J hJ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨z, hz⟩ := coord.surjective ⟨r, hr⟩
      exact ⟨z, (hcoord_eq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro r ⟨z, rfl⟩
      rw [← hcoord_eq z]
      exact (coord z).property
  subst R
  exact ⟨rho, alpha, hRfix, hRnorm, hregular, htwo⟩

private theorem unitary_weyl_sq {E : Type*} [Field E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    weyl J hJ * weyl J hJ = 1 := by
  have hw : (hermitianWeylGL : GL (Fin 3) E) * hermitianWeylGL = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianWeylGL, hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  apply Subtype.ext
  change ProjGenLinGroup.mk hermitianWeylGL * ProjGenLinGroup.mk hermitianWeylGL = 1
  rw [← map_mul, hw, map_one]

/-- Normalize both literal Borels and locate the outside involution in the
actual torus-Weyl coset by one ambient inner automorphism. -/
private theorem exists_inner_borel_pair
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hB : IsBorelSubgroup B)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : PFAppendixIII.IsInvolution t) (htB : t ∉ B) :
    ∃ g : ProjectiveSpecialUnitaryMatrixGroup J,
      let c := MulAut.conj g
      B.map c.toMonoidHom = normalizer (rootGroup J hJ : Set _) ∧
      (rightConjugate B t).map c.toMonoidHom =
        normalizer (oppositeRootGroup J hJ : Set _) ∧
      ∃ k : Eˣ, c t = hermitianTorusPSU J hJ k * weyl J hJ := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let U := rootGroup J hJ
  let V := oppositeRootGroup J hJ
  let w := weyl J hJ
  obtain ⟨rho, alpha, hfix, hnorm, hregular, htwo⟩ :=
    unitary_root_action J hJ (2 ^ n) hcard hfixed
  let : MulAction G (isotropicPoints J) := MulAction.compHom _ rho
  have hUV : U ≠ V := rootGroup_ne_oppositeRootGroup J hJ
    (one_lt_pow₀ (by decide : 1 < 2) (by omega : n ≠ 0)) hcard hfixed
  have hV : V = U.map (MulAut.conj w).toMonoidHom := oppositeRootGroup_eq_map J hJ
  have hUne : U ≠ ⊥ := by
    intro hu
    apply hUV
    rw [hV]
    rw [hu, Subgroup.map_bot]
  have hNU : normalizer (U : Set G) = MulAction.stabilizer G alpha :=
    normalizer_eq_stabilizer_of_regular_compl U alpha hfix hUne hregular hnorm
  have hNV : normalizer (V : Set G) = MulAction.stabilizer G (w • alpha) := by
    rw [hV]
    rw [← map_equiv_normalizer_eq, hNU, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have haw : alpha ≠ w • alpha := by
    intro he
    have hwN : w ∈ normalizer (U : Set G) := hnorm w he.symm
    exact hUV ((mem_normalizer_iff_map_conj_eq.mp hwN).symm.trans hV.symm)
  let P := EvenTwoRank.rootSylow J hJ hn hcard hfixed
  obtain ⟨beta, hBbeta⟩ := hB.eq_stabilizer_of_sylow_normalizer P alpha hNU
  have hbt : beta ≠ t • beta := by
    intro he
    apply htB
    rw [hBbeta, MulAction.mem_stabilizer_iff]
    exact he.symm
  obtain ⟨g, hg, hgt⟩ := htwo beta (t • beta) alpha (w • alpha) hbt haw
  change g • beta = alpha at hg
  change g • (t • beta) = w • alpha at hgt
  let c := MulAut.conj g
  have hcB : B.map c.toMonoidHom = normalizer (U : Set G) := by
    rw [hBbeta, hNU, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact congrArg (MulAction.stabilizer G) hg
  have hcBt : (rightConjugate B t).map c.toMonoidHom = normalizer (V : Set G) := by
    rw [hBbeta, rightConjugate_stabilizer, ht.inv_eq_self,
      hNV, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact congrArg (MulAction.stabilizer G) hgt
  have htt : t * t = 1 := by simpa only [pow_two] using ht.sq_eq_one
  have htalpha : c t • alpha = w • alpha := by
    rw [← hgt, ← hg]
    simp [c, MulAut.conj_apply, smul_smul, mul_assoc]
  have htwalpha : c t • (w • alpha) = alpha := by
    rw [← hgt, ← hg]
    simp [c, MulAut.conj_apply, smul_smul, mul_assoc, htt]
  have hwInv : w⁻¹ = w := inv_eq_of_mul_eq_one_left (unitary_weyl_sq J hJ)
  have hww : w • (w • alpha) = alpha := by
    rw [← mul_smul, unitary_weyl_sq, one_smul]
  have hd : c t * w⁻¹ ∈ rootTorus J hJ := by
    rw [EvenSemilinear.rootTorus_eq_normalizer_inf J hJ
      (EvenSemilinear.coord_first_surjective J hcard hfixed 1)]
    change c t * w⁻¹ ∈ normalizer (U : Set G) ⊓ normalizer (V : Set G)
    rw [mem_inf, hNU, hNV, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · rw [mul_smul, hwInv, htwalpha]
    · rw [mul_smul, hwInv, hww, htalpha]
  obtain ⟨k, hk⟩ := hd
  refine ⟨g, hcB, hcBt, k, ?_⟩
  rw [hk]
  change c t = c t * w⁻¹ * w
  group


private theorem odd_coset_conjugator {G : Type*} [Group G]
    (D : Subgroup G) (hodd : Odd (Nat.card D)) (a b : G)
    (haa : a * a = 1) (hbb : b * b = 1) (hab : a * b ∈ D) :
    ∃ g ∈ D, MulAut.conj g a = b := by
  have hai : a⁻¹ = a := inv_eq_iff_mul_eq_one.mpr haa
  have hbi : b⁻¹ = b := inv_eq_iff_mul_eq_one.mpr hbb
  let r : D := ⟨a * b, hab⟩
  have horder : Odd (orderOf r) := Odd.of_dvd_nat hodd (orderOf_dvd_natCard r)
  obtain ⟨k, hk⟩ := horder
  have hnum : k * 2 + 1 = orderOf (a * b) := by
    have hrorder : orderOf (a * b) = orderOf r := Subgroup.orderOf_coe r
    omega
  have haRot : MulAut.conj a (a * b) = (a * b)⁻¹ := by
    change a * (a * b) * a⁻¹ = (a * b)⁻¹
    rw [_root_.mul_inv_rev, hai, hbi, ← mul_assoc a a b, haa, one_mul]
  let g := (a * b) ^ k
  have haPow : MulAut.conj a g = g⁻¹ := by
    change MulAut.conj a ((a * b) ^ k) = ((a * b) ^ k)⁻¹
    rw [map_pow, haRot, inv_pow]
  have hsquare : g ^ 2 = (a * b)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    change ((a * b) ^ k) ^ 2 * (a * b) = 1
    rw [← pow_mul, ← pow_succ, hnum, pow_orderOf_eq_one]
  have hmove : a * g⁻¹ = g * a := by
    have hh : MulAut.conj a g⁻¹ = g := by rw [map_inv, haPow, inv_inv]
    exact mul_inv_eq_iff_eq_mul.mp hh
  refine ⟨g, D.pow_mem hab k, ?_⟩
  change g * a * g⁻¹ = b
  calc
    g * a * g⁻¹ = g * (a * g⁻¹) := by group
    _ = g * (g * a) := by rw [hmove]
    _ = g ^ 2 * a := by simp only [pow_two, mul_assoc]
    _ = (a * b)⁻¹ * a := by rw [hsquare]
    _ = b := by rw [_root_.mul_inv_rev, hai, hbi, mul_assoc, haa, mul_one]

private theorem sylow_eq_of_normalizer_eq {G : Type*} [Group G]
    (P Q : Sylow 2 G)
    (h : normalizer (P : Set G) = normalizer (Q : Set G)) :
    (P : Subgroup G) = Q := by
  have hle : (P : Subgroup G) ≤ normalizer (Q : Set G) := h ▸ P.le_normalizer
  have hi := P.isPGroup'.inf_normalizer_sylow Q
  rw [inf_eq_left.mpr hle] at hi
  exact (P.is_maximal' Q.isPGroup' (inf_eq_left.mp hi.symm)).symm

/-- A genuine projective group element simultaneously normalizes the Sylow,
outside involution and literal two-point torus. -/
public theorem projective_pair
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    ∃ g : ProjectiveSpecialUnitaryMatrixGroup J,
      (P : Subgroup _).map (MulAut.conj g).toMonoidHom = BorelTorus.projectiveRoot J hJ ∧
      MulAut.conj g t = hermitianWeylPSU J hJ ∧
      (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t).map
        (MulAut.conj g).toMonoidHom = BorelTorus.projectiveTorus J hJ := by
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let B := normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  let D := BorelTorus.projectiveTorus J hJ
  let w := weyl J hJ
  obtain ⟨g, hB, hBt, k, hk⟩ := exists_inner_borel_pair J hJ (by omega : 0 < n)
    hcard hfixed B (unitary_projective_borel J hn hcard hfixed hJ P) t ht htB
  let c := MulAut.conj g
  have hD : (twoPoint B t).map c.toMonoidHom = D := by
    rw [twoPoint, Subgroup.map_inf _ _ _ c.injective, hB, hBt,
      ← EvenSemilinear.rootTorus_eq_normalizer_inf J hJ
        (EvenSemilinear.coord_first_surjective J hcard hfixed 1)]
    rfl
  have hDodd : Odd (Nat.card D) := by
    have hmap : D = (BorelTorus.specialTorus J hJ).map J.specialToProjective := by
      change (hermitianTorusPSU J hJ).range =
        (hermitianTorusSU J hJ).range.map J.specialToProjective
      rw [← MonoidHom.range_comp]
      congr 1
      ext k
      simp only [MonoidHom.comp_apply, specialToProjective_apply_val, hermitianTorusPSU_val]
      rfl
    rw [hmap]
    apply Odd.of_dvd_nat _ (card_map_dvd _ _)
    rw [BorelTorus.special_card, hcard]
    exact Nat.Even.sub_odd (Nat.one_le_pow 2 (2 ^ n) (Nat.one_le_pow n 2 (by decide)))
      ((even_two.pow_of_ne_zero (by omega : n ≠ 0)).pow_of_ne_zero (by decide : 2 ≠ 0)) odd_one
  have hct : c t * c t = 1 := by
    rw [← map_mul, ← pow_two, ht.sq_eq_one, map_one]
  have hcw : c t * w ∈ D := by
    rw [hk, mul_assoc, unitary_weyl_sq, mul_one]
    exact ⟨k, rfl⟩
  obtain ⟨d, hd, hdt⟩ := odd_coset_conjugator D hDodd (c t) w hct
    (unitary_weyl_sq J hJ) hcw
  have hdN : d ∈ normalizer (rootGroup J hJ : Set _) := by
    have hh := hd
    change d ∈ rootTorus J hJ at hh
    rw [EvenSemilinear.rootTorus_eq_normalizer_inf J hJ
      (EvenSemilinear.coord_first_surjective J hcard hfixed 1)] at hh
    exact hh.1
  have hP : (P : Subgroup _).map c.toMonoidHom = BorelTorus.projectiveRoot J hJ := by
    let Q := P.mapSurjective (f := c.toMonoidHom) c.surjective
    let S := EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
    apply sylow_eq_of_normalizer_eq Q S
    change normalizer (↑((P : Subgroup _).map c.toMonoidHom) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = _
    rw [← map_equiv_normalizer_eq]
    exact hB
  have hconj : (MulAut.conj (d * g)).toMonoidHom =
      (MulAut.conj d).toMonoidHom.comp c.toMonoidHom := by
    ext x
    simp [c, MulAut.conj_apply, mul_assoc]
  refine ⟨d * g, ?_, ?_, ?_⟩
  · rw [hconj, ← Subgroup.map_map, hP]
    exact mem_normalizer_iff_map_conj_eq.mp hdN
  · change (MulAut.conj (d * g)).toMonoidHom t = _
    rw [hconj]
    exact hdt
  · rw [hconj, ← Subgroup.map_map, hD]
    exact mem_normalizer_iff_map_conj_eq.mp (D.le_normalizer hd)

end BenderSuzuki.ZD.RankOneModelGeometry.PairNormalization
