module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSpecialUnitary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SmallProjectiveUnitary

/-!
# Excluding the small special-unitary endpoint

Hexagon regularity and the actual original quotient-Sylow order identify
R_i with the marked SU3(2), without a perfectness assumption. Its scalar
center is the actual H intersection R_i. When both endpoints are special,
the two reflections fix H, so N normalizes the scalar center. The literal
scalar centralizer in U_si then has two Frattini layers of order at least
256, contradicting the order 2^15 of the containing radical.

The retained PSU3(2) exclusion handles the other three choices of scalar
conventions. For a linear opposite, the original square profile and the
linear two-layer bound force field order two or eight. Its Borel has order
prime to three, proving normality of the same scalar subgroup and giving
the same contradiction. The earlier regular-unitary, Suzuki, and dihedral
exclusions complete the original catalogue.

Thus SU3(2) is excluded in both orientations, on the original or geometric
marking and on the literal SourceQuotient, without endpoint perfectness.
Full B is retained. The marked quotient, split, rotation six and square
profile still require their earlier source producers. Regular unitary
exclusions and the complete oriented (6E) assembly remain.

Source: Fong--Seitz I (6D), printed pp.41--42.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
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
  {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x=x^2)

include e h split hc hconj in
private theorem small_special_inputs (hm : rotationOrder Q = 6) (j : Fin 2)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
      Nat.card (simpleRoot Q split j) = 8 ∧
      Nonempty (rankOne Q split j ≃* J.specialSubgroup) := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  have hK := (marked_hexagon_regularity Q e h split hm j).1
  have hcard := specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J
    (n := 1) (by decide) (by simpa using hc) (by simpa using hconj) μj
  refine ⟨hK,?_,⟨(regularFactorRootEquiv Q e h split j T hT hK hcard).trans μj⟩⟩
  simpa only [Nat.reducePow] using specialUnitary_simpleRoot_card Q e h split j T hT J
    (n := 1) (by decide) (by simpa using hc) (by simpa using hconj) μj

include e h split hc hconj in
/-- Both literal original special-unitary degree-one actors are excluded.
Scalar normality and both section bounds are discharged internally. -/
theorem original_small_special_unitary_pair_excluded
    {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
    (hcE : Nat.card E = 4) (hconjE : ∀ x, I.conj x=x^2)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) : False := by
  obtain ⟨hKi,hi,⟨ai⟩⟩ := small_special_inputs Q e h split I hcE hconjE hm i μi
  obtain ⟨hKj,hj,⟨aj⟩⟩ := small_special_inputs Q e h split J hc hconj hm j μj
  exact small_special_pair_excluded Q split j J I hc hconj hcE hconjE hm i hij hKi hKj ai aj hi hj

include e h split hc hconj in
/-- All four scalar conventions for a degree-one unitary pair are excluded,
with both orientations and no square-profile or perfectness assumptions. -/
theorem original_small_unitary_pair_excluded
    {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
    (hcE : Nat.card E = 4) (hconjE : ∀ x, I.conj x=x^2)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False := by
  rcases hj with ⟨⟨μj⟩⟩ | ⟨⟨μj⟩⟩
  · exact original_small_projective_unitary_pair_excluded Q e h split J hc hconj I hcE hconjE
      hm i j hij μj hi
  · rcases hi with ⟨⟨μi⟩⟩ | ⟨⟨μi⟩⟩
    · exact original_small_projective_unitary_pair_excluded Q e h split I hcE hconjE J hc hconj
        hm j i hij.symm μi (Or.inr ⟨μj⟩)
    · exact original_small_special_unitary_pair_excluded Q e h split J hc hconj I hcE hconjE
        hm i j hij μi μj

include e h split hc hconj in
/-- The literal small special-unitary actor is excluded opposite every
binary linear field, with the original square profile. -/
theorem original_small_special_unitary_linear_excluded
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hKi := (marked_hexagon_regularity Q e h split hm i).1
  have hcard : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T) := by
    rw [simpleRoot_card_linear Q e h split i T hT μi]
    exact ((Nat.card_congr (linearSylowEquiv i T μi).toEquiv).trans
      ((Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive
        (linearModelSylow i T μi)).symm.toEquiv).trans
          (Nat.card_congr Multiplicative.toAdd))).symm
  have hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh := MulEquivClass.apply_mem_center μi hz
    change μi z ∈ center PSL(2,E) at hh
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact μi.injective (hh.trans μi.map_one.symm)
  let μlocal := (regularFactorLocalEquiv Q e h split i T hT hKi hcard hz).trans μi
  obtain ⟨hKj,hroot,⟨a⟩⟩ := small_special_inputs Q e h split J hc hconj hm j μj
  exact small_special_linear_excluded Q split j J hc hconj hKj a hroot hm i hij hKi μlocal hsquare

include e h split hc hconj in
/-- SU3(2) is excluded against the full original F.1.1 catalogue.
The scalar section normality is proved, with no perfectness strengthening. -/
theorem original_small_special_unitary_excluded
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  cases h.quotient i with
  | linear n hn hmodel =>
    obtain ⟨E,hE,hfin,hcard,⟨μi⟩⟩ := hmodel
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact original_small_special_unitary_linear_excluded Q e h split J hc hconj hm i j hij μi μj hsquare
  | suzuki n hmodel =>
    exact original_suzuki_excluded Q e h split hm j i hij.symm hmodel.some
      (by simpa only [mul_comm] using hsquare)
  | projective_unitary n hn hmodel =>
    obtain ⟨E,hE,hfin,I,hcard,hconjE,⟨μi⟩⟩ := hmodel
    by_cases hn2 : 2≤n
    · exact original_unitary_degree_one_opposite_exclusion Q e h split I hn2 hcard hconjE
        J hc hconj hm j i hij.symm (Or.inr ⟨μj⟩) (Or.inl ⟨μi⟩)
    · have hn1 : n=1 := by omega
      subst n
      exact original_small_unitary_pair_excluded Q e h split J hc hconj I
        (by simpa using hcard) (by simpa using hconjE) hm i j hij (Or.inl ⟨μi⟩) (Or.inr ⟨μj⟩)
  | special_unitary n hn hmodel =>
    obtain ⟨E,hE,hfin,I,hcard,hconjE,⟨μi⟩⟩ := hmodel
    by_cases hn2 : 2≤n
    · exact original_unitary_degree_one_opposite_exclusion Q e h split I hn2 hcard hconjE
        J hc hconj hm j i hij.symm (Or.inr ⟨μj⟩) (Or.inr ⟨μi⟩)
    · have hn1 : n=1 := by omega
      subst n
      exact original_small_special_unitary_pair_excluded Q e h split J hc hconj I
        (by simpa using hcard) (by simpa using hconjE) hm i j hij μi μj
  | dihedral hmodel =>
    exact original_dihedral_excluded Q e h split hm j i hij.symm hmodel.some
      (by simpa only [mul_comm] using hsquare)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The special-unitary pair contradiction on the original literal quotient. -/
theorem quotient_small_special_unitary_pair_excluded
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F E : Type*} [Field F] [Finite F] [Field E] [Finite E]
    (J : HermitianForm 3 F) (I : HermitianForm 3 E)
    (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x=x^2)
    (hcE : Nat.card E = 4) (hconjE : ∀ x, I.conj x=x^2)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) : False :=
  original_small_special_unitary_pair_excluded Q (originalMarkedIso Q) h split J hc hconj I hcE hconjE
    hm i j hij μi μj

/-- Every degree-one unitary pair is excluded on the same SourceQuotient. -/
theorem quotient_small_unitary_pair_excluded
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F E : Type*} [Field F] [Finite F] [Field E] [Finite E]
    (J : HermitianForm 3 F) (I : HermitianForm 3 E)
    (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x=x^2)
    (hcE : Nat.card E = 4) (hconjE : ∀ x, I.conj x=x^2)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup))
    (hj : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)) : False :=
  original_small_unitary_pair_excluded Q (originalMarkedIso Q) h split J hc hconj I hcE hconjE
    hm i j hij hi hj

/-- SU3(2) is excluded against the full catalogue on the original quotient. -/
theorem quotient_small_special_unitary_excluded
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x=x^2)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  original_small_special_unitary_excluded Q (originalMarkedIso Q) h split J hc hconj hm i j hij μj hsquare

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
