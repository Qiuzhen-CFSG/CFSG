module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Maximality.Coordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Maximality.Transport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Maximality.OrthogonalDisplacement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Maximality.OrthogonalGeneration
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Reduction

/-!
# Intrinsic PSU₃ involution-centralizer maximality

An overgroup moving the nonisotropic positive eigenline of the standard
involution is reduced to a pair of orthogonal lines. The finite-field
displacement and two-stabilizer generation calculations prove maximality in the
identity-form model. The arbitrary-form comparison, actual central cubic
quotient, involution conjugacy, and restriction to the literal ambient subgroup
carry this conclusion to the obstruction used in E.1.14(7).

Source: Aschbacher--Smith, E.1.14(7), printed p.214; A.2.3(2), printed p.33;
A.3.21(a), printed p.55; Aschbacher (1982), Lemma 4.11.
-/

public section

set_option linter.style.haveILetI false

open Matrix Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry
open Maximality

variable {p : ℕ} (hp : p.Prime) (hodd : Odd p)

include hp hodd

omit hp hodd in
private theorem finite_projective {F : Type*} [Field F] [Finite F]
    {d : ℕ} (J : HermitianForm d F) :
    Finite (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let p : J.specialSubgroup → ProjectiveSpecialUnitaryMatrixGroup J :=
    fun A => ⟨ProjGenLinGroup.mk A.val, ⟨A.val, A.property, rfl⟩⟩
  apply Finite.of_surjective p
  rintro ⟨x, A, hA, rfl⟩
  exact ⟨⟨A, hA⟩, rfl⟩

/-- Arbitrary forms and arbitrary projective involutions reduce to the two
identity-form geometric assertions, including at the prime three. -/
theorem centralizer_isCoatom_of_matrix_geometry {H : Type*} [Group H]
    [Finite H] (hmodel : ClassicalGroup.IsPSU H 3 p) (t : H) (ht : orderOf t = 2) :
    IsCoatom (centralizer ({t} : Set H)) := by
  obtain ⟨F, _, _, J, hJ, hcard, hc, ⟨e⟩⟩ := exists_identity_model hp hmodel
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hp2 : p ≠ 2 := fun h => hodd.not_two_dvd_nat (h ▸ dvd_rfl)
  have h2 : (2 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp2
  apply (isCoatom_centralizer_equiv_iff e t).mp
  exact projective_centralizer_isCoatom_of_standard hp2 hcard J hJ hc
    (standard_centralizer_isCoatom_of_orthogonal_geometry J hJ h2
      (orthogonalDisplacement_of_prime_frobenius p hp2 hcard J hJ hc)
      (orthogonalGeneration hp2 hcard J hJ hc))
    (e t) ((orderOf_injective e.toMonoidHom e.injective t).trans ht)

/-- The maximality is inside the actual subgroup L. No ambient maximality is
asserted, and no normality of L is needed for this restriction. -/
theorem ambient_centralizer_isCoatom_of_matrix_geometry {G : Type*} [Group G]
    (L : Subgroup G) (hmodel : ClassicalGroup.IsPSU L 3 p)
    (z : G) (hzL : z ∈ L) (hz : orderOf z = 2) :
    IsCoatom ((centralizer ({z} : Set G)).subgroupOf L) := by
  haveI : Finite L := by
    rcases hmodel with ⟨F, _, _, J, _, _, ⟨e⟩⟩
    haveI : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := finite_projective J
    exact Finite.of_injective e e.injective
  apply ambient_centralizer_isCoatom_of_intrinsic L z hzL hz
  intro t ht
  exact centralizer_isCoatom_of_matrix_geometry hp hodd hmodel t ht

/-- Actual application to the obstruction: the finite-field geometry discharges
precisely the intrinsic centralizer maximality assumption. The family, tau,
quotient conventions, and arbitrary ambient two-extension are unchanged. -/
theorem constraints_of_matrix_geometry {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup (generalizedFitting G)]
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T)
    (hi : ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧
      A ≤ generalizedFitting G)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCM : centralizer ({z} : Set G) ≤ d.overgroup) :
    normalizer (weakClosure (T : Subgroup G) d.family : Set G) ≤
        centralizer ({z} : Set G) ∧
      (∀ H : Subgroup G, (T : Subgroup G) ≤ H → Group.IsSolvable H →
        H ≤ centralizer ({z} : Set G)) ∧
      ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≤ generalizedFitting G ∧
        Nat.card A = 4 ∧ z ∈ A ∧
        ∀ (r : ℕ), r.Prime → Odd r → ∀ X : Subgroup G, IsPGroup r X →
          (T : Subgroup G) ⊓ centralizer (A : Set G) ≤ normalizer (X : Set G) →
          ⁅X, A⁆ ≤ centralizer ({z} : Set G) := by
  exact constraints_of_intrinsic_coatom hp hodd hmodel hLT d hi hz hzL hTz hCM
    (ambient_centralizer_isCoatom_of_matrix_geometry hp hodd
      (generalizedFitting G) hmodel z hzL hz)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry
