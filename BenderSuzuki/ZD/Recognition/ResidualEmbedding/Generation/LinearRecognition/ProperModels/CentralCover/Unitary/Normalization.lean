module

public import BenderSuzuki.SE.Borel
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.SU3.EvenSemilinear.Torus

/-!
# Normalization of the actual unitary Borel pair

The Hermitian root coordinates identify the root subgroup in Huppert's
isotropic-point action. Its regular action away from the fixed point identifies
its normalizer with the point stabilizer. The binary root Sylow theorem then
identifies every Borel with a point stabilizer. Double transitivity takes the
pair selected by the outside involution to the standard opposite pair.

The normalized involution lies in the diagonal-torus Weyl coset. This is enough
for the middle-line argument, since both factors preserve that line. No
normalization or invariant-line premise is imposed on the original involution.
The root-action identification follows the calculation in
`EvenSemilinear.Geometry`; the pair transport follows `SE.Proposition84Torus`.
Source: GLS4, Chapter 4, Lemma 3.2(a),(c),(h), and Huppert II.10.12.
-/

open Matrix BenderSuzuki.External
open scoped LinearAlgebra.Projectivization
namespace BenderSuzuki.ZD
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
public theorem exists_unitary_borel_pair_normalization
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hB : IsBorelSubgroup B)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : PFAppendixIII.IsInvolution t) (htB : t ∉ B) :
    ∃ c : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
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
  refine ⟨c, hcB, hcBt, k, ?_⟩
  rw [hk]
  change c t = c t * w⁻¹ * w
  group

end BenderSuzuki.ZD
