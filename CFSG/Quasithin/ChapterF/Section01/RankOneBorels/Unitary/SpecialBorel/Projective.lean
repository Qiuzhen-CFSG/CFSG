module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel.Basic
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.StandardAction

/-!
# Identifying the projective Borel's explicit matrix ranges

Huppert II.10.12 specifies its existential subgroups by matrix coordinates.
Those coordinates identify them with the projective images of the actual
SU₃ root and torus homomorphisms. The regular root action then identifies
the normalizer with the isotropic-point stabilizer, including q = 2.

Source: Huppert II.10.12; Aschbacher–Smith F.1.3(1), printed pp.259–260.
-/
noncomputable section
open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII External
open scoped LinearAlgebra.Projectivization
namespace CFSG.Quasithin.ChapterF.Source.Unitary
variable {F : Type*} [Field F] [Finite F]

/-- Isotropic projective points for the stored Hermitian form. -/
public abbrev unitaryIsotropicPoints (J : HermitianForm 3 F) :=
  let P := ℙ F (Fin 3 → F)
  let A : Set P := {x | ∃ (v : Fin 3 → F) (hv : v ≠ 0),
    x = Projectivization.mk F v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  {x : P // x ∈ A}

/-- Huppert's natural action, with the root and torus identified as matrix ranges. -/
public theorem standard_projective_matrix_borel
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    let G := ProjectiveSpecialUnitaryMatrixGroup J
    let R := (hermitianUnipotentPSU J hstandard).range
    let D := (hermitianTorusPSU J hstandard).range
    ∃ (rho : G →* Equiv.Perm (unitaryIsotropicPoints J))
      (pinf : unitaryIsotropicPoints J),
      Function.Injective rho ∧
      (∀ (g : G) (z : unitaryIsotropicPoints J) (M : J.specialSubgroup),
        Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) F) =
            (g : Matrix.ProjGenLinGroup (Fin 3) F) →
        ((rho g z : unitaryIsotropicPoints J) : ℙ F (Fin 3 → F)) =
          (Matrix.GeneralLinearGroup.toLin (M : GL (Fin 3) F)).toLinearEquiv •
            (z : ℙ F (Fin 3 → F))) ∧
      Nat.card (hermitianUnipotentCoord J) = (2 ^ n) ^ 3 ∧
      Nat.card R = (2 ^ n) ^ 3 ∧
      R ⊔ D = (MulAction.stabilizer (Equiv.Perm (unitaryIsotropicPoints J)) pinf).comap rho ∧
      Subgroup.normalizer (R : Set G) =
        (MulAction.stabilizer (Equiv.Perm (unitaryIsotropicPoints J)) pinf).comap rho ∧
      (MulAction.stabilizer (Equiv.Perm (unitaryIsotropicPoints J)) pinf).comap rho < ⊤ := by
  classical
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let Omega := unitaryIsotropicPoints J
  rcases huppert_II_10_12 J (2 ^ n) hcard (fixed_card J n hn hcard hconj) hstandard with
    ⟨hOmega, rho, pinf, hrho, hnatural, _hUcard,
      ⟨R, D, hRU, hDU, hUN, _hdisj, hsup, _hcyc, hRcard,
        _hcomm, _hcommcard, _hDcard, hregular,
        ⟨coord, hcoord⟩, hDcoord, hDsurj⟩,
      htwo, _hGcard, _hthree⟩
  have hroot (z : hermitianUnipotentCoord J) :
      (coord z : G) = hermitianUnipotentPSU J hstandard z := by
    obtain ⟨M, hM, hproj⟩ := hcoord z
    apply Subtype.ext
    rw [hproj, hermitianUnipotentPSU_val]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (congrFun hM i) j
  have hR : R = (hermitianUnipotentPSU J hstandard).range := by
    ext g
    constructor
    · intro hg
      obtain ⟨z, hz⟩ := coord.surjective ⟨g, hg⟩
      refine ⟨z, ?_⟩
      rw [← hroot, hz]
    · rintro ⟨z, rfl⟩
      rw [← hroot]
      exact (coord z).property
  have hD : D = (hermitianTorusPSU J hstandard).range := by
    ext g
    constructor
    · intro hg
      obtain ⟨k, M, hM, hproj⟩ := hDcoord ⟨g, hg⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      rw [hproj, hermitianTorusPSU_val]
      congr 1
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      exact (congrFun (congrFun hM i) j).symm
    · rintro ⟨k, rfl⟩
      obtain ⟨h, M, hM, hproj⟩ := hDsurj k
      have he : (h : G) = hermitianTorusPSU J hstandard k := by
        apply Subtype.ext
        rw [hproj, hermitianTorusPSU_val]
        congr 1
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        exact congrFun (congrFun hM i) j
      rw [← he]
      exact h.property
  have hcoordcard : Nat.card (hermitianUnipotentCoord J) = (2 ^ n) ^ 3 :=
    (Nat.card_congr coord).trans hRcard
  let : MulAction G Omega := MulAction.compHom Omega rho
  have hRne : R ≠ ⊥ := by
    intro he
    have hc : Nat.card R = 1 := by rw [he]; simp
    have hq : 1 < 2 ^ n := one_lt_pow₀ (by norm_num) (by omega)
    have hp : 1 < (2 ^ n) ^ 3 := one_lt_pow₀ hq (by decide)
    omega
  have hnormalizer : Subgroup.normalizer (R : Set G) =
      (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho :=
    normalizer_eq_stabilizer_of_regular_compl R pinf hRU hRne hregular hUN
  have hproper : (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho < ⊤ := by
    have hc : 1 < Nat.card Omega := by
      rw [hOmega]
      have hp : 0 < (2 ^ n) ^ 3 := by positivity
      omega
    have : Nontrivial Omega := Finite.one_lt_card_iff_nontrivial.mp hc
    obtain ⟨a, ha⟩ := exists_ne pinf
    obtain ⟨g, hg, _⟩ := htwo pinf a a pinf ha.symm ha
    apply lt_top_iff_ne_top.mpr
    intro he
    have hm : g ∈ (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho :=
      he ▸ Subgroup.mem_top g
    exact ha (hg.symm.trans hm)
  refine ⟨rho, pinf, hrho, hnatural, hcoordcard, ?_, ?_, ?_, hproper⟩
  · rw [← hR]; exact hRcard
  · rw [← hR, ← hD]; exact hsup
  · rw [← hR]; exact hnormalizer

end CFSG.Quasithin.ChapterF.Source.Unitary
