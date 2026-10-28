module

public import CFSG.Quasithin.ChapterF.Section06.UnitarySourceCover
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.SpecificGroups.PSU3.PrimeOddCenterCover

/-!
# Actual degree-three component covers in F.6.18

The original quotient by O_{3'} forces each component center to be a
three-group. The genuine scalar-cover theorems consequently identify the
component as SL₃ or SU₃, or as its projective quotient. In the nontrivial
center case the isomorphism preserves the supplied projective marking.
No multiplier bound is retained as an input.

Source: Aschbacher--Smith F.6.15 and F.6.18(10)--(11), pp.308--310,
and the scalar-cover convention I.1.1--I.1.4, pp.407--408.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Field F] [Finite F] {K : Subgroup G}

/-- The center of the actual source component has odd order. -/
theorem component_center_odd_of_primeToThree_quotient
    (eG : G ≃* (H ⧸ pPrimeCore 3 H)) (hK : IsComponent G K) :
    Odd (Nat.card (center K)) := by
  let : IsQuasisimple K := hK.2
  have hc := Subgroup.IsSubnormal.pPrimeCore_eq_bot
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient eG) K hK.1
  have hp : IsPGroup 3 (center K) := by
    rw [IsQuasisimple.center_eq_pCore hc]
    exact pCore_isPGroup
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn]
  exact (by decide : Odd 3).pow

private def centerFreeEquiv {L M : Type*} [Group L] [Group M]
    [Group.IsPerfect L] (e : L ⧸ center L ≃* M) (hz : center L = ⊥) : L ≃* M :=
  MulEquiv.ofBijective (centralQuotientCover e).toMonoidHom
    ⟨(centralQuotientCover e).toMonoidHom.ker_eq_bot_iff.mp
      (by simpa only [centralQuotientCover_ker] using hz),
      (centralQuotientCover e).surjective⟩

/-- The actual linear component, including its scalar projection square. -/
theorem component_linear_three_cover
    (hK : IsComponent G K) (ho : Odd (Nat.card F))
    (eK : K ⧸ center K ≃* PSL(3,F)) :
    (center K = ⊥ ∧ ∃ j : K ≃* PSL(3,F),
      j.toMonoidHom = eK.toMonoidHom.comp (QuotientGroup.mk' (center K))) ∨
    (Nat.card (center K) = 3 ∧ Nat.card F % 3 = 1 ∧
      ∃ j : SL(3,F) ≃* K,
        (eK.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp j.toMonoidHom =
          Matrix.PSL3.projection F) := by
  let : IsQuasisimple K := hK.2
  by_cases hz : center K = ⊥
  · exact .inl ⟨hz, centerFreeEquiv eK hz, rfl⟩
  · have h2 : Nat.card F ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ ho)
    have h4 : Nat.card F ≠ 4 := fun h => (by decide : ¬ Odd 4) (h ▸ ho)
    obtain ⟨h3, hm, _, j, hj⟩ :=
      Matrix.PSL3.OrdinaryCenterRecognition.nontrivial_center_recognition h2 h4 eK hz
    exact .inr ⟨h3, hm, j, hj⟩

/-- The actual unitary component, with every scalar-cover premise discharged
from the original source quotient and prime parameter. -/
theorem component_unitary_three_cover
    (eG : G ≃* (H ⧸ pPrimeCore 3 H)) (hK : IsComponent G K)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (eK : K ⧸ center K ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (center K = ⊥ ∧ ∃ j : K ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      j.toMonoidHom = eK.toMonoidHom.comp (QuotientGroup.mk' (center K))) ∨
    (Nat.card (center K) = 3 ∧ p % 3 = 2 ∧
      ∃ j : J.specialSubgroup ≃* K,
        (eK.toMonoidHom.comp (QuotientGroup.mk' (center K))).comp j.toMonoidHom =
          J.specialToProjective) := by
  let : IsQuasisimple K := hK.2
  by_cases hz : center K = ⊥
  · exact .inl ⟨hz, centerFreeEquiv eK hz, rfl⟩
  · obtain ⟨hm, h3, _, j, hj⟩ :=
      HermitianForm.PrimeOddCenterCover.nontrivial_center_recognition
        J hp hp2 hcard hconj eK (component_center_odd_of_primeToThree_quotient eG hK) hz
    exact .inr ⟨h3, hm, j, hj⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
