module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineSubgroup
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryDerived

/-!
# The original quadratic unitary factors and the source subgroup X

The original PSL2 and SU3/PSU3 quotient markings give the quadratic field
ratio, regularity and actual unitary root model. They therefore construct
the source subgroup X of order 2^(9b), whose commutator contains the middle
root's Frattini group of order 2^b. The full cubic fixed radical lies in X.
The theory-level product theorem identifies both end factors with their
intrinsic centers. Both endpoint orientations, the full Borel, the original
quotient and both inclusion squares are unchanged, including b=1.

Source: Fong--Seitz I (6F), printed p.47, the subgroup X and its initial
order and commutator assertions. The following invariant-subgroup exclusion
and lower-central contradiction remain required for (6F).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

/-- The original factor marks supply the source's subgroup X of order
2^(9b), its middle Frattini commutator of order 2^b, and the inclusion of
the full cubic fixed radical, with both scalar conventions and b=1. -/
theorem original_linear_unitary_nine_subgroup
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    let X₉ := unitaryNineSubgroup Q split i j
    let C := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
    Nat.card X₉=2^(9*b) ∧ Nat.card C=2^b ∧ C ≤ ⁅X₉,X₉⁆ ∧
      simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤ X₉ := by
  have hfixed := (original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj).2
  have hC := unitary_cubic_radical_le_nine Q split hm i j hij
    (fun w => (hfixed w).1) (fun w => (hfixed w).2.1)
  obtain ⟨_,hab⟩ := original_linear_unitary_all_quadratic_degree Q e h split hm i j hij ha hb hi hj
  obtain ⟨E,hEfield,hEfin,hEcard,⟨ν⟩⟩ := hi
  let : Field E := hEfield
  let : Finite E := hEfin
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hEcard)
  have hE2 : 2 < Nat.card E := by
    rw [hEcard,hab]
    exact (by decide : 2 < 2^2).trans_le
      (Nat.pow_le_pow_right (by decide) (show 2 ≤ 2*b by omega))
  have hregular := marked_octagon_regularity_of_linear_quotient Q e h split hE2 hm i ν
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hri : Nat.card (simpleRoot Q split i)=2^(2*b) := by
    rw [simpleRoot_card_linear Q e h split i Ti hTi ν,hEcard,hab]
  have applyModel {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
      (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
      (hmodel : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) :
      let X₉ := unitaryNineSubgroup Q split i j
      let C := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
      Nat.card X₉=2^(9*b) ∧ Nat.card C=2^b ∧ C ≤ ⁅X₉,X₉⁆ ∧
        simpleRemainder Q split j ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤ X₉ := by
    obtain ⟨μ,σ,hσ,_⟩ := regular_unitary_cover_of_factor Q e h split J hb hcard hconj
      j (hregular j).1 hmodel.symm
    have hrj : Nat.card (simpleRoot Q split j)=(2^b)^3 := by
      rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
      · exact projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj μ
      · exact specialUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj μ
    exact ⟨unitaryNineSubgroup_card Q split J hb hcard hconj hm i j hij (hregular j).1 μ hri hrj,
      unitary_rootFrattini_card Q split J hb hcard hconj j (hregular j).1 μ _,
      unitaryNineSubgroup_commutator_contains Q split J hb hcard hconj i j (hregular j).1 μ,hC⟩
  rcases hj with ⟨F,hF,hfin,J,hcard,hconj,μ⟩ | ⟨F,hF,hfin,J,hcard,hconj,μ⟩
  · exact applyModel J hcard hconj (Or.inl μ)
  · exact applyModel J hcard hconj (Or.inr μ)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
