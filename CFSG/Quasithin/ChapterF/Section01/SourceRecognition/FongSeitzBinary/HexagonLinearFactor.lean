module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearHexagonRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SmallSpecialUnitary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.MixedUnitaryExclusion

/-!
# Hexagon comparison from one original linear factor

The full original F.1.1 catalogue is considered at the opposite endpoint.
The Suzuki and dihedral exclusions, both degree-one unitary exclusions,
and the regular mixed linear–unitary contradiction leave an actual PSL₂
quotient. The existing linear hexagon recognition then gives the complete
G₂ or triality amalgam comparison, with the full Borel and both endpoint
inclusion squares. Binary fields and both orientations are included;
no perfectness of the original factors is assumed.

The marked quotient, split structure, rotation-six hypothesis and literal
square profile retain their earlier source producers. No unitary-pair
exclusion is needed because one endpoint is already linear.

Source: Fong–Seitz I (6C)–(6E), printed pp.39–45; II §9, pp.211–220;
DGS Theorem D, printed p.224.
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
/-- One original linear factor forces the opposite factor to be linear. -/
theorem marked_hexagon_opposite_linear_factor
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    {a : ℕ} (ha : 0 < a)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) :
    ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^n) := by
  obtain ⟨E,hE,hfinE,hcardE,⟨μi⟩⟩ := hi
  let : Fintype E := Fintype.ofFinite E
  let : NeZero a := ⟨ha.ne'⟩
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardE)
  obtain ⟨n,hn,hmj⟩ := original_hexagon_linear_or_unitary Q mark h split hm i j hij hsquare
  rcases hmj with hlin | hprojective | hspecial
  · exact ⟨n,hn,hlin⟩
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μj⟩⟩ := hprojective
    by_cases hn2 : 2 ≤ n
    · exact (original_mixed_linear_unitary_excluded Q mark h split J hn2 hcard hconj
        hm i j hij μi hcardE (Or.inl ⟨μj⟩)).elim
    · have hn1 : n=1 := by omega
      subst n
      exact (original_small_projective_unitary_linear_excluded Q mark h split J
        (by simpa using hcard) (by simpa using hconj) hm i j hij μi μj hsquare).elim
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μj⟩⟩ := hspecial
    by_cases hn2 : 2 ≤ n
    · exact (original_mixed_linear_unitary_excluded Q mark h split J hn2 hcard hconj
        hm i j hij μi hcardE (Or.inr ⟨μj⟩)).elim
    · have hn1 : n=1 := by omega
      subst n
      exact (original_small_special_unitary_linear_excluded Q mark h split J
        (by simpa using hcard) (by simpa using hconj) hm i j hij μi μj hsquare).elim

include mark h split in
/-- A hexagon with one original linear endpoint has a full G₂ or triality
amalgam comparison. The other factor is selected from the full F.1.1 catalogue. -/
theorem marked_hexagon_of_linear_factor
    (hm : rotationOrder Q = 6) (i : Fin 2)
    {a : ℕ} (ha : 0 < a)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hsquare : IsSquare (Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1))) :
    Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  fin_cases i
  · obtain ⟨b,hb,h₁⟩ := marked_hexagon_opposite_linear_factor Q mark h split hm 0 1
      (by decide) ha hi hsquare
    exact LinearHexagon.marked_linear_hexagon_of_factor_types Q mark h split hm ha hb hi h₁
  · obtain ⟨b,hb,h₀⟩ := marked_hexagon_opposite_linear_factor Q mark h split hm 1 0
      (by decide) ha hi (by simpa only [mul_comm] using hsquare)
    exact LinearHexagon.marked_linear_hexagon_of_factor_types Q mark h split hm hb ha h₀ hi

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonRecognition
