module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonLinearFactor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryInitialEscape

/-!
# Exhaustive recognition of the original binary hexagon

The original F.1.1 quotient catalogue is exhausted at both endpoints.
Suzuki and dihedral factors, both degree-one unitary scalar conventions,
and all regular unitary combinations are excluded on the actual marked
quotient. Each original factor is therefore a concrete PSL₂ quotient.
The complete linear hexagon theorem gives the G₂ or triality amalgam,
retaining the full Borel and both endpoint inclusion squares.

No selected local model, factor-perfectness assumption, field relation,
structural row, coordinate relation or presentation is an extra premise.
Binary fields and both orientations are included. The earlier marked
split quotient, rotation-six and literal source square profile remain
explicit; this module recognizes the hexagon branch of the full source
case split.

Source: Fong–Seitz I (1J), (6C)–(6E), printed pp.39–45; II §9,
printed pp.211–220; DGS Theorem D, printed p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonRecognition
open HexagonStructure
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include mark h split in
private theorem regular_unitary_excluded
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  cases h.quotient i with
  | linear a ha hmodel =>
    obtain ⟨E,hE,hfin,hcardE,⟨μi⟩⟩ := hmodel
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcardE)
    exact original_mixed_linear_unitary_excluded Q mark h split J hn hcard hconj
      hm i j hij μi hcardE hj
  | suzuki m hmodel =>
    exact original_suzuki_excluded Q mark h split hm j i hij.symm hmodel.some
      (by simpa only [mul_comm] using hsquare)
  | projective_unitary m hmpos hmodel =>
    obtain ⟨E,hE,hfin,I,hcardE,hconjE,⟨μi⟩⟩ := hmodel
    by_cases hm2 : 2 ≤ m
    · exact original_unitary_pair_excluded Q mark h split J hn hcard hconj I hm2 hcardE hconjE hm i j hij (Or.inl ⟨μi⟩) hj
    · have hm1 : m=1 := by omega
      subst m
      exact original_unitary_degree_one_opposite_exclusion Q mark h split J hn hcard hconj
        I (by simpa using hcardE) (by simpa using hconjE) hm i j hij (Or.inl ⟨μi⟩) hj
  | special_unitary m hmpos hmodel =>
    obtain ⟨E,hE,hfin,I,hcardE,hconjE,⟨μi⟩⟩ := hmodel
    by_cases hm2 : 2 ≤ m
    · exact original_unitary_pair_excluded Q mark h split J hn hcard hconj I hm2 hcardE hconjE hm i j hij (Or.inr ⟨μi⟩) hj
    · have hm1 : m=1 := by omega
      subst m
      exact original_unitary_degree_one_opposite_exclusion Q mark h split J hn hcard hconj
        I (by simpa using hcardE) (by simpa using hconjE) hm i j hij (Or.inr ⟨μi⟩) hj
  | dihedral hmodel =>
    exact original_dihedral_excluded Q mark h split hm j i hij.symm hmodel.some
      (by simpa only [mul_comm] using hsquare)

include mark h split in
/-- Every endpoint of the original marked hexagon is a genuine linear quotient. -/
theorem marked_hexagon_linear_factor
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) :
    ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^n) := by
  obtain ⟨n,hn,hmj⟩ := original_hexagon_linear_or_unitary Q mark h split hm i j hij hsquare
  rcases hmj with hlin | hprojective | hspecial
  · exact ⟨n,hn,hlin⟩
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μj⟩⟩ := hprojective
    by_cases hn2 : 2 ≤ n
    · exact (regular_unitary_excluded Q mark h split J hn2 hcard hconj
        hm i j hij (Or.inl ⟨μj⟩) hsquare).elim
    · have hn1 : n=1 := by omega
      subst n
      exact (original_small_projective_unitary_excluded Q mark h split J
        (by simpa using hcard) (by simpa using hconj) hm i j hij μj hsquare).elim
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μj⟩⟩ := hspecial
    by_cases hn2 : 2 ≤ n
    · exact (regular_unitary_excluded Q mark h split J hn2 hcard hconj
        hm i j hij (Or.inr ⟨μj⟩) hsquare).elim
    · have hn1 : n=1 := by omega
      subst n
      exact (original_small_special_unitary_excluded Q mark h split J
        (by simpa using hcard) (by simpa using hconj) hm i j hij μj hsquare).elim

include mark h split in
/-- Exhaustive source hexagon comparison, with both original factor markings
constructed from F.1.1 and the source square profile. -/
theorem marked_hexagon_catalogue
    (hm : rotationOrder Q = 6)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1))) :
    Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  obtain ⟨a,ha,h₀⟩ := marked_hexagon_linear_factor Q mark h split hm 1 0
    (by decide) (by simpa only [mul_comm] using hsquare)
  obtain ⟨b,hb,h₁⟩ := marked_hexagon_linear_factor Q mark h split hm 0 1
    (by decide) hsquare
  exact LinearHexagon.marked_linear_hexagon_of_factor_types Q mark h split hm ha hb h₀ h₁

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonRecognition

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonRecognition
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Every original factor of the actual finite source quotient is linear. -/
theorem quotient_hexagon_linear_factor
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) :
    ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^n) :=
  marked_hexagon_linear_factor Q (originalMarkedIso Q) h split hm i j hij hsquare

/-- The complete marked G₂/triality comparison for the literal original source quotient. -/
theorem quotient_hexagon_catalogue
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1))) :
    Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) :=
  marked_hexagon_catalogue Q (originalMarkedIso Q) h split hm hsquare

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonRecognition

