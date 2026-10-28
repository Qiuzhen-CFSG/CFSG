module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.BinaryDegreeParity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.DihedralLocal

/-!
# Original unitary parameters in the marked octagon

The original quotient markings give the exact canonical root orders,
including SU3(2) and PSU3(2), before any regularity assumption. The finite
octagon square theorem therefore excludes two unitary endpoints of the
same degree parity. It also forces opposite parity for a linear/unitary
pair and odd unitary degree opposite Suzuki or the original dihedral row.

Every application uses the same original endpoint and full Borel amalgam
marking. The degree-one unitary pair is excluded, but a single degree-one
unitary endpoint is not excluded here. The remaining Cartan, effective
section and lower-central arguments of (6F) remain necessary.

Source: Fong--Seitz I (1J), (6F), printed pp.45--49; AS F.1.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h split in
private theorem unitary_root_card (i : Fin 2) {n : ℕ} (hn : 0 < n)
    (hu : ClassicalGroup.IsPSU ((L i) ⧸ pCore 2 (L i)) 3 (2^n) ∨
      IsSU ((L i) ⧸ pCore 2 (L i)) 3 (2^n)) :
    Nat.card (simpleRoot Q split i) = (2^n)^3 := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  rcases hu with hpsu | hsu
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hpsu
    exact projectiveUnitary_simpleRoot_card Q e h split i T hT J hn hcard hconj μ
  · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hsu
    exact specialUnitary_simpleRoot_card Q e h split i T hT J hn hcard hconj μ

include e h split in
/-- Both original unitary quotients force opposite field-degree parity,
for every combination of special and projective covers. -/
theorem original_unitary_pair_degree_parity
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSU ((L i) ⧸ pCore 2 (L i)) 3 (2^a) ∨
      IsSU ((L i) ⧸ pCore 2 (L i)) 3 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) : a % 2 ≠ b % 2 :=
  octagon_unitary_degree_parity Q split hm i j hij
    (unitary_root_card Q e h split i ha hi) (unitary_root_card Q e h split j hb hj)

include e h split in
/-- The same-parity unitary branches are impossible on the actual marked octagon. -/
theorem original_unitary_pair_excluded_of_same_parity
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a % 2 = b % 2)
    (hi : ClassicalGroup.IsPSU ((L i) ⧸ pCore 2 (L i)) 3 (2^a) ∨
      IsSU ((L i) ⧸ pCore 2 (L i)) 3 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) : False :=
  original_unitary_pair_degree_parity Q e h split hm i j hij ha hb hi hj hab

include e h split in
/-- Both degree-one endpoints are excluded without assuming regularity or perfectness. -/
theorem original_small_unitary_pair_excluded
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hi : ClassicalGroup.IsPSU ((L i) ⧸ pCore 2 (L i)) 3 2 ∨
      IsSU ((L i) ⧸ pCore 2 (L i)) 3 2)
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 2 ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 2) : False :=
  original_unitary_pair_excluded_of_same_parity Q e h split hm i j hij
    (a := 1) (b := 1) (by decide) (by decide) rfl hi hj

include e h split in
/-- The original linear and unitary quotient degrees have opposite parity. -/
theorem original_linear_unitary_degree_parity
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (_ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) : a % 2 ≠ b % 2 := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact octagon_linear_unitary_degree_parity Q split hm i j hij
    ((simpleRoot_card_linear Q e h split i T hT μ).trans hcard)
    (unitary_root_card Q e h split j hb hj)

include e h split in
/-- A unitary quotient opposite any Suzuki parameter has odd field degree. -/
theorem original_suzuki_unitary_degree_odd
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {m n : ℕ} (hn : 0 < n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n)) : Odd n := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  exact octagon_unitary_degree_odd_of_square_root Q split hm j i hij.symm
    (unitary_root_card Q e h split j hn hj)
    (suzuki_simpleRoot_card Q e h split i T hT hi.some)

include e h split in
/-- The original dihedral quotient has root order four, so the opposite
unitary quotient has odd field degree. -/
theorem original_dihedral_unitary_degree_odd
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {n : ℕ} (hn : 0 < n)
    (hi : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* DihedralGroup 5))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n)) : Odd n := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  apply octagon_unitary_degree_odd_of_square_root Q split hm j i hij.symm
    (unitary_root_card Q e h split j hn hj) (b := 1)
  exact dihedral_simpleRoot_card Q e h split i T hT hi.some

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
