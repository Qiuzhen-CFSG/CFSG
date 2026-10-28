module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryParameters
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.OctagonBounds

/-!
# Original linear/unitary octagon parameter bounds

The exact source root orders are 2^a and 2^(3b). Apply the finite octagon
multiplicity bound in both orientations and retain the original degree
parity. These are parameter restrictions at the genuine source marking;
the unitary exclusion still needs its Cartan and root-section arguments.

Source: Fong--Seitz I (1J)--(1K) and (6F), pp.6--7,46--47.
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
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

/-- The source linear and unitary degrees obey both multiplicity bounds,
with the cubic unitary root degree and the literal endpoint orientation. -/
theorem original_linear_unitary_degree_bounds
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    a % 2 ≠ b % 2 ∧ a ≤ 6*b ∧ 3*b ≤ 2*a := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hci : Nat.card (simpleRoot Q split i) = 2^a := by
    obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact (simpleRoot_card_linear Q e h split i Ti hTi μ).trans hcard
  have hcj : Nat.card (simpleRoot Q split j) = 2^(3*b) := by
    have hroot : Nat.card (simpleRoot Q split j) = (2^b)^3 := by
      rcases hj with hpsu | hsu
      · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hpsu
        exact projectiveUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj μ
      · obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hsu
        exact specialUnitary_simpleRoot_card Q e h split j Tj hTj J hb hcard hconj μ
    simpa only [← pow_mul,Nat.mul_comm] using hroot
  have hr := octagon_binary_degree_bounds Q split hm i j hij hci hcj
  exact ⟨original_linear_unitary_degree_parity Q e h split hm i j hij ha hb hi hj,
    by omega,hr.2⟩

/-- A binary linear endpoint cannot face a unitary endpoint of any degree.
The unitary root has degree at least three, violating the octagon bound. -/
theorem original_binary_linear_unitary_excluded
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {b : ℕ} (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) : False := by
  have hbnd := original_linear_unitary_degree_bounds Q e h split hm i j hij
    (a := 1) (by decide) hb hi hj
  omega

/-- Opposite a degree-one unitary factor, the original linear degree is
two, four or six. This retains the possible affine unitary exception. -/
theorem original_linear_small_unitary_degrees
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a : ℕ} (ha : 0 < a)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 2 ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 2) : a = 2 ∨ a = 4 ∨ a = 6 := by
  have hbnd := original_linear_unitary_degree_bounds Q e h split hm i j hij
    (b := 1) ha (by decide) hi hj
  omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
