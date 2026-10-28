module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.UnitaryLocal.BorelCubic.ScalarCorrection
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting.Transport
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.RootNormalizer
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.TorusAction
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Cubic unitary conjugations preserving the standard PSU Borel

The concrete Borel has root two-core and order
q³ (q² − 1) / gcd(q + 1, 3). For q congruent to −1 modulo three,
three-divisibility of this order implies nine-divisibility of q + 1.
A Borel-preserving unitary action preserves the root two-core, so its
matrix is upper triangular. Scalar correction then proves it is inner.

Source: Aschbacher--Smith, 15.3.37, printed p.1135; the concrete root and
torus calculation is Huppert II.10.12. All groups are the actual matrix
images, and the cube hypothesis concerns the automorphism.
-/

open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open CFSG.Quasithin.ChapterF.Source CFSG.Quasithin.ChapterF.Source.Unitary
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.UnitaryLocal.BorelCubic
variable {F : Type*} [Field F] [Finite F]

private theorem nine_dvd_of_borel_order {q : ℕ} (hq : q % 3 = 2)
    (h3 : 3 ∣ q ^ 3 * ((q ^ 2 - 1) / Nat.gcd (q + 1) 3)) : 9 ∣ q + 1 := by
  have hg : Nat.gcd (q + 1) 3 = 3 := Nat.gcd_eq_right (by omega)
  rw [hg] at h3
  have hq3 : ¬3 ∣ q ^ 3 := by
    intro h
    have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h
    omega
  have hd : 3 ∣ (q ^ 2 - 1) / 3 :=
    ((by decide : Nat.Prime 3).dvd_mul.mp h3).resolve_left hq3
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq q 1
  have h3' : 3 ∣ q ^ 2 - 1 := by
    rw [hfactor]
    exact dvd_mul_of_dvd_right (by omega : 3 ∣ q + 1) _
  have h9 : 9 ∣ (q - 1) * (q + 1) := by
    rw [← hfactor, ← Nat.mul_div_cancel' h3']
    exact Nat.mul_dvd_mul_left 3 hd
  have hcop : Nat.Coprime 9 (q - 1) := by
    have h : Nat.Coprime 3 (q - 1) :=
      (by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr (by omega)
    exact h.pow_left 2
  exact hcop.dvd_of_dvd_mul_left h9

/-- The explicit PSU Borel has its root range as two-core and the expected order. -/
private theorem standard_borel_core_card
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    twoCore (BorelTorus.projectiveBorel J hJ) = BorelTorus.projectiveRoot J hJ ∧
    Nat.card (BorelTorus.projectiveBorel J hJ) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) / Nat.gcd (2 ^ n + 1) 3) := by
  obtain ⟨_, _, _, _, _, hRcard, hsup, hN, _⟩ :=
    standard_projective_matrix_borel J n hn hcard hconj hJ
  have hNB : normalizer (BorelTorus.projectiveRoot J hJ : Set _) =
      BorelTorus.projectiveBorel J hJ := hN.trans hsup.symm
  obtain ⟨_, _, S, hS, _⟩ := standard_su_borel_data J n hn hcard hconj hJ
  let T := S.mapSurjective (suProjection_surjective J)
  have hT : (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      BorelTorus.projectiveRoot J hJ := by
    change (S : Subgroup J.specialSubgroup).map (suProjection J) = _
    rw [hS, suRoot_map_projection]
    rfl
  constructor
  · rw [← hNB, ← hT]
    exact twoCore_sylow_normalizer T
  · rw [BorelTorus.projectiveBorel, card_sup_eq_mul_of_normalizes_of_disjoint]
    · rw [BorelTorus.projective_card J hJ hcard hconj]
      exact congrArg (fun k => k * _) hRcard
    · rw [hNB]
      exact le_sup_right
    · exact BorelTorus.SemilinearActors.projective_root_disjoint_torus J hJ

/-- Three-divisibility of the PSU Borel forces nine in the norm-one torus. -/
private theorem standard_borel_nine_dvd
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n) (hq : 2 ^ n % 3 = 2)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (h3 : 3 ∣ Nat.card (BorelTorus.projectiveBorel J hJ)) : 9 ∣ 2 ^ n + 1 := by
  rw [(standard_borel_core_card J n hn hcard hconj hJ).2] at h3
  exact nine_dvd_of_borel_order hq h3

/-- Preserving the Borel preserves its characteristic two-core, forcing the
actual unitary representative to be upper triangular. -/
private theorem standard_borel_upper
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (u : J.unitarySubgroup)
    (hB : (BorelTorus.projectiveBorel J hJ).map (J.unitaryConjHom u).toMonoidHom =
      BorelTorus.projectiveBorel J hJ) :
    u.val.val 1 0 = 0 ∧ u.val.val 2 0 = 0 ∧ u.val.val 2 1 = 0 := by
  have hroot : (BorelTorus.projectiveRoot J hJ).map (J.unitaryConjHom u).toMonoidHom =
      BorelTorus.projectiveRoot J hJ := by
    rw [← (standard_borel_core_card J n hn hcard hconj hJ).1,
      ← twoCore_map_injective _ _ (J.unitaryConjHom u).injective, hB]
  apply BorelTorus.SemilinearActors.projective_semilinear_upper J hJ hcard
    (fixed_card J n hn hcard hconj) (J.unitaryConjHom u) 1 u _ hroot
  intro x
  rw [J.unitaryConjHom_apply, J.unitaryConj_apply_val]
  change _ = ProjGenLinGroup.mk u.val *
    ProjGenLinGroup.map (RingHom.id F) x.val * (ProjGenLinGroup.mk u.val)⁻¹
  simp only [ProjGenLinGroup.map_id, MonoidHom.id_apply]

/-- The cubic Borel assertion for the antidiagonal form and its explicit Borel. -/
public theorem standard_cubic_borel_action
    (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n) (hq : 2 ^ n % 3 = 2)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (u : J.unitarySubgroup)
    (h3 : 3 ∣ Nat.card (BorelTorus.projectiveBorel J hJ))
    (hu : (J.unitaryConjHom u) ^ 3 = 1)
    (hB : (BorelTorus.projectiveBorel J hJ).map (J.unitaryConjHom u).toMonoidHom =
      BorelTorus.projectiveBorel J hJ) :
    J.unitaryConjHom u ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨h10, h20, h21⟩ := standard_borel_upper J n hn hcard hconj hJ u hB
  exact triangular_projective_cubic_is_inner J n hn hcard hconj hJ
    (standard_borel_nine_dvd J n hn hq hcard hconj hJ h3) u h10 h20 h21 hu

end CFSG.Quasithin.Chapter15.Section03.Candidates.UnitaryLocal.BorelCubic
