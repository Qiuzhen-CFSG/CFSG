module

public import Theory.Representation.SU3.BinaryDegree.Perfectness
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Quasisimplicity of the special and projective unitary groups in dimension three

For fixed-field order q > 2, Huppert II.10.13 gives simplicity of the
projective group for every nondegenerate Hermitian form. Its root subgroup
of order q³ rules out an abelian simple group. The scalar kernel consists
of commutators, so perfectness lifts to SU₃. The projective kernel is then
exactly the center, proving quasisimplicity of both actual matrix carriers.

Only the q³ root subgroup is used; no full order formula is needed.
Source: Huppert, *Endliche Gruppen I*, II.10.12–13; Aschbacher–Smith,
*The Classification of Quasithin Groups*, F.6.18(10)–(11), pp.309–310.
-/

public section
open Matrix Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {q : ℕ}

/-- The actual unipotent root subgroup supplies a cube dividing the projective order. -/
theorem cube_dvd_card_projective (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    q ^ 3 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J q hcard hfixed
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨_, _, _, _, _, _, hroot, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12
      (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J) q hcard hfixed rfl
  obtain ⟨R, _, _, _, _, _, _, _, hR, _⟩ := hroot
  rw [← hR]
  exact card_subgroup_dvd_card _

/-- PSU₃(q) is perfect for q > 2, independently of the chosen Hermitian basis. -/
theorem projective_isPerfect_of_fixed_card (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J q hq hcard hfixed
  rcases (inferInstance : (commutator (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
      with hb | ht
  · let : IsMulCommutative (ProjectiveSpecialUnitaryMatrixGroup J) :=
      (commutator_eq_bot_iff _).mp hb
    have hp : (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)).Prime := IsSimpleGroup.prime_card
    rcases (Nat.dvd_prime hp).mp (J.cube_dvd_card_projective hcard hfixed) with h1 | he
    · have : 1 < q ^ 3 := one_lt_pow₀ (by omega) (by decide)
      omega
    · exact (Nat.Prime.not_prime_pow (by decide : 2 ≤ 3) (he ▸ hp)).elim
  · exact ⟨ht⟩

/-- The scalar kernel is already in the derived subgroup, so SU₃(q) is perfect. -/
theorem special_isPerfect_of_fixed_card (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    Group.IsPerfect J.specialSubgroup := by
  let := J.projective_isPerfect_of_fixed_card hq hcard hfixed
  have hk := Representation.SU3.BinaryDegree.specialToProjective_ker_le_commutator
    J hcard hfixed
  have hm : (commutator J.specialSubgroup).map J.specialToProjective = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr J.specialToProjective_surjective]
    exact Group.IsPerfect.commutator_eq_top
  have hc := congrArg (Subgroup.comap J.specialToProjective) hm
  rw [Subgroup.comap_map_eq, comap_top, sup_eq_left.mpr hk] at hc
  exact ⟨hc⟩

/-- Quasisimplicity of the literal special-unitary subgroup of GL₃. -/
theorem special_isQuasisimple_of_fixed_card (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    IsQuasisimple J.specialSubgroup := by
  let := J.projective_isPerfect_of_fixed_card hq hcard hfixed
  let := J.special_isPerfect_of_fixed_card hq hcard hfixed
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J q hq hcard hfixed
  have hz : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
        with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  refine { simple := ?_ }
  exact ((QuotientGroup.quotientMulEquivOfEq
    (J.specialToProjective_ker_eq_center hz).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
      J.specialToProjective_surjective)).isSimpleGroup

/-- Quasisimplicity of the literal projective image, transported through its surjection. -/
theorem projective_isQuasisimple_of_fixed_card (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let := J.special_isQuasisimple_of_fixed_card hq hcard hfixed
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J q hq hcard hfixed
  exact IsQuasisimple.of_surjective J.specialToProjective J.specialToProjective_surjective

end BenderSuzuki.MatrixGroups.HermitianForm
