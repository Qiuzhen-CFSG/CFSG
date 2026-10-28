module

public import Theory.SpecificGroups.PSU3.UniversalCover.ThreeCentralDescent
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.ThreeResidual

/-!
# The unitary covering step in the full F.6 source argument

The original source quotient G ≃ Ghat/O_{3'}(Ghat) has trivial O_{3'}.
This passes to every actual component L, whose center is consequently a
three-group. Applying the prime-parameter SU₃ descent to the original map
L → L/Z(L) → PSU₃ gives the specified scalar-cover map, and an isomorphism
when the component center is nontrivial.

The only retained multiplier input excludes nine from the universal kernel
when the prime parameter is two modulo three. Its producer is
`qt-i01-a2-unitary-odd-cross-odd`. No bound at another prime or at a square
parameter is required. These theorems supply the group-cover step of rows
(10) and (11); the full component catalogue, graph action, local groups and
universal F.6.18 assembly remain with `qt-f-06`.

Source: Aschbacher–Smith, Remark F.6.15 and Theorem F.6.18, printed
pp.308–310, with the covering convention I.1.1–I.1.4, pp.407–408.
-/

public section
noncomputable section

open Subgroup Theory.GroupTheory PerfectCentralCovering
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.UnitarySourceCover

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private theorem component_center_isThreeGroup
    {G Ghat : Type*} [Group G] [Finite G] [Group Ghat] [Finite Ghat]
    (eG : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (L : Subgroup G) (hL : IsComponent G L) : IsPGroup 3 (center L) := by
  let : IsQuasisimple L := hL.2
  have hG := Noncyclic.primeToThreeCore_eq_bot_of_quotient eG
  have hLcore := Subgroup.IsSubnormal.pPrimeCore_eq_bot hG L hL.1
  rw [IsQuasisimple.center_eq_pCore hLcore]
  exact pCore_isPGroup

universe u v w
variable {G : Type u} [Group G] [Finite G]
variable {Ghat : Type v} [Group Ghat] [Finite Ghat]
variable {F : Type w} [Field F] [Finite F]

/-- The actual F.6 component projection lifts from SU₃. The three-group
kernel is proved from the original prime-to-three quotient, not assumed. -/
theorem component_cover_prime
    (eG : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (L : Subgroup G) (hL : IsComponent G L)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (hnine : p % 3 = 2 →
      ¬ 9 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (eL : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      (eL.toMonoidHom.comp (QuotientGroup.mk' (center L))).comp k =
        J.specialToProjective := by
  let : IsQuasisimple L := hL.2
  exact HermitianForm.UniversalCover.ThreeCentralDescent.exists_lift_prime
    J hp hodd hcard hconj hnine (centralQuotientCover eL).toMonoidHom
    (centralQuotientCover eL).surjective (by
      rw [centralQuotientCover_ker]
      exact component_center_isThreeGroup eG L hL)

/-- A nontrivial component center gives the actual SU₃ isomorphism with
the original quotient marking retained, as required in the F.6 cover cases. -/
theorem component_equiv_prime_of_nontrivial_center
    (eG : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (L : Subgroup G) (hL : IsComponent G L)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (hnine : p % 3 = 2 →
      ¬ 9 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    (eL : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hne : center L ≠ ⊥) :
    ∃ e : J.specialSubgroup ≃* L,
      (eL.toMonoidHom.comp (QuotientGroup.mk' (center L))).comp e.toMonoidHom =
        J.specialToProjective := by
  let : IsQuasisimple L := hL.2
  exact HermitianForm.UniversalCover.ThreeCentralDescent.exists_equiv_prime_of_nontrivial_kernel
    J hp hodd hcard hconj hnine (centralQuotientCover eL).toMonoidHom
    (centralQuotientCover eL).surjective (by
      rw [centralQuotientCover_ker]
      exact component_center_isThreeGroup eG L hL)
    (by simpa only [centralQuotientCover_ker] using hne)

end CFSG.Quasithin.ChapterF.UnitarySourceCover
