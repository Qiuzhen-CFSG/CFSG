module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallProjectiveUnitary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffineHexagonExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiCatalogue

/-!
# Excluding the small projective-unitary endpoint of an original hexagon

Hexagon regularity supplies (2B) without endpoint perfectness. The literal
original PSU3(2) marking then identifies the root-generated actor with
the solvable order-72 model and the canonical root with an order-eight
Sylow. The two moving Frattini layers have order at least 256 each. This
contradicts the five-root order whenever the opposite root has order at
most eight, including both degree-one unitary scalar conventions.

For a linear opposite, its own two-layer estimate and the source square
profile force that same upper bound on the root order. A regular unitary
opposite is excluded by the previously proved unitary two-layer estimate.
The Suzuki and dihedral exclusions complete the original F.1.1 catalogue.
Thus no projective-unitary degree-one constructor survives at either
orientation. The SU3(2) constructor is kept distinct and is not excluded
at the selected endpoint by this result.

Every action is on the original or geometric marked quotient. The final
applications use the literal Q.q image of S and right conjugation by the
same reflection. The full Borel is retained; the quotient, split, rotation
six and square-profile inputs still require their earlier source producers.
Regular unitary exclusions and exhaustive oriented (6E) assembly remain.

Source: Fong--Seitz I (6D), printed pp.41--43, using (3G), (4D) and (5D).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
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
  (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x = x^2)

include e h split hc hconj in
private theorem small_projective_inputs (hm : rotationOrder Q = 6) (j : Fin 2)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    simpleRemainder Q split j ≤ localKernel Q j ∧
      Nat.card (simpleRoot Q split j) = 8 ∧
      Nat.card (rankOne Q split j) = 72 ∧ Group.IsSolvable (rankOne Q split j) := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  have hK := (marked_hexagon_regularity Q e h split hm j).1
  have hcard := projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split j T hT J
    (n := 1) (by decide) (by simpa using hc) (by simpa using hconj) μj
  let a := (regularFactorRootEquiv Q e h split j T hT hK hcard).trans μj
  let := HermitianForm.FixedFieldTwo.projective_isSolvable J hc hconj
  refine ⟨hK,?_,(Nat.card_congr a.toEquiv).trans
    (HermitianForm.FixedFieldTwo.card_projective J hc hconj),
    Group.isSolvable_of_surjective (f := a.symm.toMonoidHom) a.symm.surjective⟩
  simpa only [Nat.reducePow] using projectiveUnitary_simpleRoot_card Q e h split j T hT J
    (n := 1) (by decide) (by simpa using hc) (by simpa using hconj) μj

include e h split hc hconj in
/-- The two small projective-unitary Frattini bounds on the literal original
or geometric Sylow radical. -/
theorem original_small_projective_unitary_two_layers
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    let V := (sylowMap Q e h).range ⊓ rightConjugate (sylowMap Q e h).range
      ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)
    256 ≤ Nat.card (V ⧸ frattini V) ∧
      256 ≤ Nat.card (frattini V ⧸ frattini (frattini V)) ∧ 65536 ≤ Nat.card V := by
  obtain ⟨hK,hroot,hR,hsol⟩ := small_projective_inputs Q e h split J hc hconj hm j μj
  let := hsol
  dsimp only
  rw [←marked_radical_eq h Q e split j (UnitarySource.actorReflection Q split j).val
    (UnitarySource.actorReflection Q split j).class_eq]
  exact nine_actor_radical_two_layers Q split j hR hroot hm i hij
    (UnitarySource.actorReflection Q split j) hK

include e h split hc hconj in
/-- The small projective unitary endpoint is excluded opposite any root of
order at most eight, with no perfectness assumptions. -/
theorem original_small_projective_unitary_small_opposite_excluded
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hi : Nat.card (simpleRoot Q split i) ≤ 8) : False := by
  obtain ⟨hK,hroot,hR,hsol⟩ := small_projective_inputs Q e h split J hc hconj hm j μj
  let := hsol
  exact nine_actor_small_opposite_excluded Q split j hR hroot hm i hij
    (UnitarySource.actorReflection Q split j) hK hi

include e h split hc hconj in
/-- Source (6D)'s first degree-one contradiction includes both scalar
conventions at the opposite unitary endpoint. -/
theorem original_small_projective_unitary_pair_excluded
    {E : Type*} [Field E] [Finite E] (I : HermitianForm 3 E)
    (hcE : Nat.card E = 4) (hconjE : ∀ x, I.conj x = x^2)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup I) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* I.specialSubgroup)) : False := by
  apply original_small_projective_unitary_small_opposite_excluded Q e h split J hc hconj hm i j hij μj
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hroot : Nat.card (simpleRoot Q split i) = 8 := by
    rcases hi with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
    · simpa only [Nat.reducePow] using projectiveUnitary_simpleRoot_card Q e h split i T hT I
        (n := 1) (by decide) (by simpa using hcE) (by simpa using hconjE) μ
    · simpa only [Nat.reducePow] using specialUnitary_simpleRoot_card Q e h split i T hT I
        (n := 1) (by decide) (by simpa using hcE) (by simpa using hconjE) μ
  exact hroot.le

include e h split hc hconj in
/-- Every binary linear field is excluded opposite PSU3(2), using the
actual source square profile and the literal linear local action. -/
theorem original_small_projective_unitary_linear_excluded
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,E))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
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
  obtain ⟨hKj,hroot,hR,hsol⟩ := small_projective_inputs Q e h split J hc hconj hm j μj
  let := hsol
  exact nine_actor_linear_opposite_excluded Q split j hR hroot hm i hij
    (UnitarySource.actorReflection Q split i) (UnitarySource.actorReflection Q split j)
    hKi hKj μlocal hsquare

include e h split hc hconj in
/-- PSU3(2) is excluded against the full original catalogue, including
both unitary scalar conventions and every nonperfect parameter. -/
theorem original_small_projective_unitary_excluded
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False := by
  cases h.quotient i with
  | linear n hn hmodel =>
    obtain ⟨E,hE,hfin,hcard,⟨μi⟩⟩ := hmodel
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact original_small_projective_unitary_linear_excluded Q e h split J hc hconj hm i j hij μi μj hsquare
  | suzuki n hmodel =>
    exact original_suzuki_excluded Q e h split hm j i hij.symm hmodel.some
      (by simpa only [mul_comm] using hsquare)
  | projective_unitary n hn hmodel =>
    obtain ⟨E,hE,hfin,I,hcard,hconjE,⟨μi⟩⟩ := hmodel
    by_cases hn2 : 2 ≤ n
    · exact original_unitary_degree_one_opposite_exclusion Q e h split I hn2 hcard hconjE
        J hc hconj hm j i hij.symm (Or.inl ⟨μj⟩) (Or.inl ⟨μi⟩)
    · have hn1 : n = 1 := by omega
      subst n
      exact original_small_projective_unitary_pair_excluded Q e h split J hc hconj I
        (by simpa using hcard) (by simpa using hconjE) hm i j hij μj (Or.inl ⟨μi⟩)
  | special_unitary n hn hmodel =>
    obtain ⟨E,hE,hfin,I,hcard,hconjE,⟨μi⟩⟩ := hmodel
    by_cases hn2 : 2 ≤ n
    · exact original_unitary_degree_one_opposite_exclusion Q e h split I hn2 hcard hconjE
        J hc hconj hm j i hij.symm (Or.inl ⟨μj⟩) (Or.inr ⟨μi⟩)
    · have hn1 : n = 1 := by omega
      subst n
      exact original_small_projective_unitary_pair_excluded Q e h split J hc hconj I
        (by simpa using hcard) (by simpa using hconjE) hm i j hij μj (Or.inr ⟨μi⟩)
  | dihedral hmodel =>
    exact original_dihedral_excluded Q e h split hm j i hij.symm hmodel.some
      (by simpa only [mul_comm] using hsquare)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
open MarkedLocal
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The lower bounds use the literal original Sylow image under Q.q and
right conjugation by the same source reflection. -/
theorem quotient_small_projective_unitary_two_layers
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x = x^2)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    let V := ((S.subgroupOf (generated L S)).map Q.q) ⊓
      rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
        ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)
    256 ≤ Nat.card (V ⧸ frattini V) ∧
      256 ≤ Nat.card (frattini V ⧸ frattini (frattini V)) ∧ 65536 ≤ Nat.card V := by
  dsimp only
  rw [quotient_sourceS_image_eq_unipotent h Q split,
    ←sylow_range Q (originalMarkedIso Q) h split]
  exact original_small_projective_unitary_two_layers Q (originalMarkedIso Q) h split J hc hconj
    hm i j hij μj

/-- The complete small projective-unitary exclusion on the original finite quotient. -/
theorem quotient_small_projective_unitary_excluded
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 4) (hconj : ∀ x, J.conj x = x^2)
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))) : False :=
  original_small_projective_unitary_excluded Q (originalMarkedIso Q) h split J hc hconj hm i j hij μj hsquare

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
