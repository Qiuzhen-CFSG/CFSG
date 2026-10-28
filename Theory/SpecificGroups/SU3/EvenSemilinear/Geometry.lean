module

public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Geometry

/-!
# Simultaneous normalization of binary unitary root groups

The explicit upper root group is Sylow by `EvenTwoRank.rootSylow`.
Sylow conjugacy and the doubly transitive action on isotropic points then
normalize the two image root groups simultaneously. This extends the
geometric part of the existing prime-field proof to every binary prime power.
No coordinate rigidity or automorphism classification is assumed.

Source: Huppert II.10.12 and the normalization argument for Steinberg's
unitary automorphism theorem, `refs/KGroup/GLS3/Chapter2St1.tex`, Theorem 36.
-/

open Matrix BenderSuzuki.External
open scoped LinearAlgebra.Projectivization
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
open OddPrimeSylow.NormalizedOuter.Coverage

private abbrev isotropicPoints {E : Type*} [Field E] (J : HermitianForm 3 E) :=
  {x : ℙ E (Fin 3 → E) // ∃ (v : Fin 3 → E) (hv : v ≠ 0),
    x = Projectivization.mk E v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}

private theorem root_action {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    ∃ (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm (isotropicPoints J))
      (alpha : isotropicPoints J),
      (∀ u ∈ rootGroup J hJ, rho u alpha = alpha) ∧
      (∀ g, rho g alpha = alpha →
        (rootGroup J hJ).map (MulAut.conj g).toMonoidHom = rootGroup J hJ) ∧
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
  refine ⟨rho, alpha, ?_, ?_, hregular, htwo⟩
  · exact fun u hu => hRfix hu
  · intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRnorm hg)

private theorem map_conj_mul {G : Type*} [Group G] (U : Subgroup G) (g h : G) :
    (U.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      U.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_aut_mul {G : Type*} [Group G] (U : Subgroup G) (a b : MulAut G) :
    (U.map b.toMonoidHom).map a.toMonoidHom = U.map (a * b).toMonoidHom :=
  Subgroup.map_map U _ _

private theorem conjugate_eq_of_point_eq {G X : Type*} [Group G]
    (rho : G →* Equiv.Perm X) (U : Subgroup G) (alpha : X)
    (hnorm : ∀ g, rho g alpha = alpha → U.map (MulAut.conj g).toMonoidHom = U)
    (g h : G) (hpoint : rho g alpha = rho h alpha) :
    U.map (MulAut.conj g).toMonoidHom = U.map (MulAut.conj h).toMonoidHom := by
  have hn : U.map (MulAut.conj (h⁻¹ * g)).toMonoidHom = U := by
    apply hnorm
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
    rw [hpoint]
    exact (rho h).symm_apply_apply alpha
  calc
    U.map (MulAut.conj g).toMonoidHom =
        (U.map (MulAut.conj (h⁻¹ * g)).toMonoidHom).map
          (MulAut.conj h).toMonoidHom := by rw [map_conj_mul]; simp
    _ = U.map (MulAut.conj h).toMonoidHom := by rw [hn]

private theorem exists_root_conjugate {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ g, (rootGroup J hJ).map (MulAut.conj g).toMonoidHom =
      (rootGroup J hJ).map a.toMonoidHom := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let P := EvenTwoRank.rootSylow J hJ hn hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J)
    P (P.mapSurjective (f := a.toMonoidHom) a.surjective)
  have heq : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
      (MulAut.conj g).toMonoidHom =
        (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map a.toMonoidHom :=
    congrArg Sylow.toSubgroup hg
  exact ⟨g, by simpa only [P, EvenTwoRank.rootSylow_coe] using heq⟩

/-- Every automorphism of the actual projective SU₃ image is an inner
automorphism followed by an automorphism preserving each of the two opposite
matrix root groups. Every positive binary fixed-field exponent is allowed. -/
public theorem exists_root_pair_normalization {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ (k : ProjectiveSpecialUnitaryMatrixGroup J)
      (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)),
      a = MulAut.conj k * b ∧
      (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ ∧
      (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ := by
  obtain ⟨rho, alpha, _, hnorm, _, htwo⟩ := root_action J hJ (2 ^ n) hcard hfixed
  let U := rootGroup J hJ
  let w := weyl J hJ
  have hUV := rootGroup_ne_oppositeRootGroup J hJ (one_lt_pow₀ (by decide : 1 < 2) (by omega : n ≠ 0)) hcard hfixed
  obtain ⟨g, hg⟩ := exists_root_conjugate J hJ hn hcard hfixed a
  obtain ⟨h, hh⟩ := exists_root_conjugate J hJ hn hcard hfixed (a * MulAut.conj w)
  have hh' : U.map (MulAut.conj h).toMonoidHom =
      (oppositeRootGroup J hJ).map a.toMonoidHom := by
    rw [oppositeRootGroup_eq_map, map_aut_mul]
    exact hh
  have hpoints : rho g alpha ≠ rho h alpha := by
    intro heq
    apply hUV
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    rw [← hg, ← hh']
    exact conjugate_eq_of_point_eq rho U alpha hnorm g h heq
  have hw : alpha ≠ rho w alpha := by
    intro heq
    apply hUV
    rw [oppositeRootGroup_eq_map]
    exact (hnorm w heq.symm).symm
  obtain ⟨k, hkU, hkV⟩ := htwo (rho g alpha) (rho h alpha) alpha (rho w alpha)
    hpoints hw
  let b := MulAut.conj k * a
  refine ⟨k⁻¹, b, ?_, ?_, ?_⟩
  · dsimp [b]
    rw [map_inv]
    group
  · change U.map (MulAut.conj k * a).toMonoidHom = U
    rw [← map_aut_mul, ← hg, map_conj_mul]
    apply hnorm
    simpa only [map_mul, Equiv.Perm.mul_apply] using hkU
  · change (oppositeRootGroup J hJ).map (MulAut.conj k * a).toMonoidHom = _
    rw [← map_aut_mul, ← hh', map_conj_mul, oppositeRootGroup_eq_map]
    apply conjugate_eq_of_point_eq rho U alpha hnorm (k * h) w
    simpa only [map_mul, Equiv.Perm.mul_apply] using hkV

end BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
