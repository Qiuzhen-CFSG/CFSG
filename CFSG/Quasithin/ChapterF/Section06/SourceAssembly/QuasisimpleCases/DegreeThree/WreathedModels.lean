module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.Parameters
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.SylowSign

/-!
# Actual covers and signs in the wreathed source branch

When the component quotient retains the full ambient wreathed two-part,
the genuine section maps identify its Sylow subgroup with C₄ wreath C₂.
The matrix Sylow calculation fixes the sign; the order and scalar-cover
calculations then produce the exact prime congruence and component model.
If the component is already the whole group, its odd center proves the
required two-part equality directly through the actual quotient map.

Source: Aschbacher--Smith F.6.18(10), printed pp.309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Field F] [Finite F] {K : Subgroup G}

/-- A component equal to the whole source group retains its exact Sylow
order after its original central quotient. -/
theorem component_quotient_sylow_card_of_top
    (eG : G ≃* (H ⧸ pPrimeCore 3 H)) (hK : IsComponent G K) (htop : K = ⊤)
    (T : Sylow 2 G) (P : Sylow 2 (K ⧸ center K)) : Nat.card P = Nat.card T := by
  let j : K ≃* G := (MulEquiv.subgroupCongr htop).trans topEquiv
  let R := T.mapSurjective (f := j.symm.toMonoidHom) j.symm.surjective
  let eTR : T ≃* R := (T : Subgroup G).equivMapOfInjective
    j.symm.toMonoidHom j.symm.injective
  have hk : Nat.Coprime 2 (Nat.card (QuotientGroup.mk' (center K)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact (component_center_odd_of_primeToThree_quotient eG hK).coprime_two_left
  let eRP := Sylow.equivOfSurjectiveCoprime (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _) hk R P
  exact (Nat.card_congr (eTR.trans eRP).toEquiv).symm

private def fullWreathedModel (T : Sylow 2 G) (eT : T ≃* WreathedThirtyTwo)
    (K : Subgroup G) (P : Sylow 2 (K ⧸ center K)) (hP : Nat.card P = 32) :
    P ≃* WreathedThirtyTwo :=
  (Classical.choice (sylow_equiv_of_section_card_eq T K (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _) P (hP.trans
      ((Nat.card_congr eT.toEquiv).trans wreathedThirtyTwo_card).symm))).symm.trans eT

/-- Both linear sign and scalar-cover alternatives are proved from the
literal wreathed section, rather than retained as independent inputs. -/
theorem component_linear_three_wreathed_models
    (hK : IsComponent G K) (T : Sylow 2 G) (eT : T ≃* WreathedThirtyTwo)
    (P : Sylow 2 (K ⧸ center K)) (hP : Nat.card P = 32)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hcard : Nat.card F = p)
    (eK : K ⧸ center K ≃* PSL(3,F)) :
    p % 8 = 5 ∧ (Nonempty (K ≃* SL(3,F)) ∨ Nonempty (K ≃* PSL(3,F))) := by
  let Q := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
  let ePQ : P ≃* Q := (P : Subgroup _).equivMapOfInjective eK.toMonoidHom eK.injective
  have hs := psl3_sign_of_wreathed_sylow hp ho hcard Q
    (ePQ.symm.trans (fullWreathedModel T eT K P hP))
  have hT : Nat.card T ≤ 64 := by
    rw [Nat.card_congr eT.toEquiv, wreathedThirtyTwo_card]
    decide
  exact component_linear_three_small_sylow_models hK T hT hp hcard hs eK

/-- The unitary analogue retains the source Frobenius form and discharges
the sign, prime congruence and odd-center cover step. -/
theorem component_unitary_three_wreathed_models
    (eG : G ≃* (H ⧸ pPrimeCore 3 H)) (hK : IsComponent G K)
    (T : Sylow 2 G) (eT : T ≃* WreathedThirtyTwo)
    (P : Sylow 2 (K ⧸ center K)) (hP : Nat.card P = 32)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (eK : K ⧸ center K ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    p % 8 = 3 ∧ (Nonempty (K ≃* J.specialSubgroup) ∨
      Nonempty (K ≃* ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let Q := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
  let ePQ : P ≃* Q := (P : Subgroup _).equivMapOfInjective eK.toMonoidHom eK.injective
  have hs := psu3_sign_of_wreathed_sylow J hp ho hcard hconj Q
    (ePQ.symm.trans (fullWreathedModel T eT K P hP))
  have hT : Nat.card T ≤ 64 := by
    rw [Nat.card_congr eT.toEquiv, wreathedThirtyTwo_card]
    decide
  exact component_unitary_three_small_sylow_models eG hK T hT J hp hcard hconj hs eK

end CFSG.Quasithin.ChapterF.SourceAssembly
