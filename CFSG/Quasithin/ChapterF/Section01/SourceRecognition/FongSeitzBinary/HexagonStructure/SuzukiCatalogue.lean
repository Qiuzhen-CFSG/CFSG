module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSuzukiClassTwo
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SmallSuzuki
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.UnitaryLayers

/-!
# The full Suzuki and dihedral exclusions in an original binary hexagon

For each original Sz(2) or D₁₀ endpoint, the proved local identification
supplies the actual Sz(2) root actor, its cyclic order-four canonical root,
and the literal radical-kernel inclusion. The class-two radical theorem
and the opposite root's nonzero cubic displacement exclude every pair of
these small endpoints. Combining this with the regular Suzuki contradiction
excludes all pairs of Suzuki parameters, including zero.

The complete original F.1.1 catalogue is then considered at the opposite
endpoint. The already proved mixed linear and unitary exclusions, with the
actual source square profile, eliminate its linear and both unitary
constructors. Thus no original Suzuki or D₁₀ quotient survives, and each
endpoint is explicitly linear, projective unitary, or special unitary.
These are actual model isomorphisms, including every small field and both
unitary scalar-center conventions.

The arbitrary marked amalgam isomorphism includes the geometric application.
The class-two theorem is also applied to the literal original Sylow image
under Q.q, using the source right-conjugation convention. No endpoint
perfectness is assumed. The split structure, rotation-six and square-profile
premises retain their earlier producers and final discharge in source
assembly. The remaining unitary exclusions and the full oriented (6E)
structural assembly are not asserted here.

Source: Fong--Seitz I (5H), printed p.30, and (6C), printed pp.39--41.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
private theorem small_classTwo_inputs (j : Fin 2)
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
    Nonempty (rankOne Q split j ≃* SuzukiMatrixGroup 0) ∧
    Nonempty (simpleRoot Q split j ≃* SuzukiRootSubgroup 0) := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hj with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · exact ⟨suzuki_remainder_le_kernel_all Q e h split j T hT μ,
      ⟨suzukiAllRankOneEquiv Q e h split j T hT μ⟩,
      ⟨originalSuzukiAllRootEquiv Q e h split j T hT μ⟩⟩
  · exact ⟨dihedral_remainder_le_kernel Q e h split j T hT μ,
      ⟨dihedralSuzukiRankOneEquiv Q e h split j T hT μ⟩,
      ⟨originalDihedralRootEquiv Q e h split j T hT μ⟩⟩

include e h in
/-- The source class-two conclusion on the original or geometric small pair. -/
theorem original_smallSuzuki_pair_classTwo (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)) :
    ⁅simpleRemainder Q split j,⁅simpleRemainder Q split j,simpleRemainder Q split j⁆⁆ = ⊥ := by
  obtain ⟨hKi,_,⟨νi⟩⟩ := small_classTwo_inputs Q e h split i hi
  obtain ⟨hKj,⟨μj⟩,⟨νj⟩⟩ := small_classTwo_inputs Q e h split j hj
  exact smallSuzuki_pair_classTwo Q split hm i j hij hKi hKj μj νi νj

include e h split in
/-- All four pairs of original Sz(2)/D₁₀ constructors are excluded. -/
theorem original_smallSuzuki_pair_excluded (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)) : False := by
  obtain ⟨hKi,⟨μi⟩,⟨νi⟩⟩ := small_classTwo_inputs Q e h split i hi
  obtain ⟨hKj,⟨μj⟩,⟨νj⟩⟩ := small_classTwo_inputs Q e h split j hj
  exact smallSuzuki_pair_excluded Q split hm i j hij hKi hKj μi μj νi νj

include e h split in
/-- The complete original Suzuki/Suzuki exclusion, including both zero parameters. -/
theorem original_suzuki_pair_excluded (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ}
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup n) : False := by
  obtain ⟨rfl,rfl⟩ := original_suzuki_pair_parameters_zero Q e h split hm i j hij μi μj
  exact original_smallSuzuki_pair_excluded Q e h split hm i j hij (Or.inl ⟨μi⟩) (Or.inl ⟨μj⟩)

include e h split in
/-- Every original Suzuki parameter is excluded opposite the D₁₀ constructor. -/
theorem original_suzuki_dihedral_excluded (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m : ℕ}
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5) : False := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · exact original_smallSuzuki_pair_excluded Q e h split hm i j hij (Or.inl ⟨μi⟩) (Or.inr ⟨μj⟩)
  · exact original_regular_suzuki_small_exclusion Q e h split hm j i hij.symm (Or.inr ⟨μj⟩) hmpos μi

include e h split in
/-- Fong--Seitz (6C) on the full original F.1.1 catalogue: no Suzuki endpoint,
including the solvable parameter, under the earlier source square profile. -/
theorem original_suzuki_excluded (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m : ℕ}
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  cases h.quotient i with
  | linear n hn hmodel =>
    obtain ⟨F,hF,hfin,hcard,⟨μi⟩⟩ := hmodel
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact original_mixed_linear_suzuki_all_exclusion Q e h split hm i j hij μi μj hsquare
  | suzuki n hmodel =>
    exact original_suzuki_pair_excluded Q e h split hm i j hij hmodel.some μj
  | projective_unitary n hn hmodel =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μi⟩⟩ := hmodel
    exact original_unitary_suzuki_all_parameters_exclusion Q e h split J hcard hconj hn
      hm j i hij.symm μj (Or.inl ⟨μi⟩) (by simpa only [mul_comm] using hsquare)
  | special_unitary n hn hmodel =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μi⟩⟩ := hmodel
    exact original_unitary_suzuki_all_parameters_exclusion Q e h split J hcard hconj hn
      hm j i hij.symm μj (Or.inr ⟨μi⟩) (by simpa only [mul_comm] using hsquare)
  | dihedral hmodel =>
    exact original_suzuki_dihedral_excluded Q e h split hm j i hij.symm μj hmodel.some

include e h split in
/-- The original dihedral constructor is excluded against every original local model. -/
theorem original_dihedral_excluded (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  cases h.quotient i with
  | linear n hn hmodel =>
    obtain ⟨F,hF,hfin,hcard,⟨μi⟩⟩ := hmodel
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact original_mixed_linear_dihedral_exclusion Q e h split hm i j hij μi μj hsquare
  | suzuki n hmodel =>
    exact original_suzuki_dihedral_excluded Q e h split hm i j hij hmodel.some μj
  | projective_unitary n hn hmodel =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μi⟩⟩ := hmodel
    exact original_unitary_dihedral_all_parameters_exclusion Q e h split J hcard hconj hn
      hm j i hij.symm μj (Or.inl ⟨μi⟩) (by simpa only [mul_comm] using hsquare)
  | special_unitary n hn hmodel =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μi⟩⟩ := hmodel
    exact original_unitary_dihedral_all_parameters_exclusion Q e h split J hcard hconj hn
      hm j i hij.symm μj (Or.inr ⟨μi⟩) (by simpa only [mul_comm] using hsquare)
  | dihedral hmodel =>
    exact original_smallSuzuki_pair_excluded Q e h split hm i j hij
      (Or.inr hmodel) (Or.inr ⟨μj⟩)

include e h split in
/-- The remaining actual original endpoint is linear or one of the two unitary covers.
The unitary exclusions and the final oriented structural dichotomy remain separate duties. -/
theorem original_hexagon_linear_or_unitary (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) :
    ∃ n : ℕ, 0 < n ∧
      (ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^n) ∨
       ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n) ∨
       IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n)) := by
  cases h.quotient j with
  | linear n hn hmodel => exact ⟨n,hn,Or.inl hmodel⟩
  | suzuki m hmodel => exact (original_suzuki_excluded Q e h split hm i j hij hmodel.some hsquare).elim
  | projective_unitary n hn hmodel => exact ⟨n,hn,Or.inr (Or.inl hmodel)⟩
  | special_unitary n hn hmodel => exact ⟨n,hn,Or.inr (Or.inr hmodel)⟩
  | dihedral hmodel => exact (original_dihedral_excluded Q e h split hm i j hij hmodel.some hsquare).elim

include e h split in
/-- The source class-two conclusion on the literal original/geometric Sylow image. -/
theorem marked_smallSuzuki_pair_classTwo (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5))
    (s : Q.tits.N)
    (hs : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) s = Q.simple j) :
    let V := (sylowMap Q e h).range ⊓ rightConjugate (sylowMap Q e h).range (s : X ⧸ Q.D)
    ⁅V,⁅V,V⁆⁆ = ⊥ := by
  dsimp only
  rw [←marked_radical_eq h Q e split j s hs]
  exact original_smallSuzuki_pair_classTwo Q e h split hm i j hij hi hj

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
open MarkedLocal
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal Q.q image and the source right-conjugation convention are preserved. -/
theorem quotient_smallSuzuki_pair_classTwo
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup 0) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5))
    (s : Q.tits.N)
    (hs : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) s = Q.simple j) :
    let V := ((S.subgroupOf (generated L S)).map Q.q) ⊓
      rightConjugate ((S.subgroupOf (generated L S)).map Q.q) (s : (generated L S) ⧸ Q.D)
    ⁅V,⁅V,V⁆⁆ = ⊥ := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split,
    ←sylow_range Q (originalMarkedIso Q) h split]
  exact marked_smallSuzuki_pair_classTwo Q (originalMarkedIso Q) h split hm i j hij hi hj s hs

/-- The completed Suzuki exclusion on the original source quotient. -/
theorem quotient_suzuki_excluded
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) {m : ℕ}
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  original_suzuki_excluded Q (originalMarkedIso Q) h split hm i j hij μj hsquare

/-- The completed D₁₀ exclusion on the original source quotient. -/
theorem quotient_dihedral_excluded
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* DihedralGroup 5)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  original_dihedral_excluded Q (originalMarkedIso Q) h split hm i j hij μj hsquare

/-- Only linear and the two unitary covers remain in each original endpoint. -/
theorem quotient_hexagon_linear_or_unitary
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) :
    ∃ n : ℕ, 0 < n ∧
      (ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^n) ∨
       ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n) ∨
       IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n)) :=
  original_hexagon_linear_or_unitary Q (originalMarkedIso Q) h split hm i j hij hsquare

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
