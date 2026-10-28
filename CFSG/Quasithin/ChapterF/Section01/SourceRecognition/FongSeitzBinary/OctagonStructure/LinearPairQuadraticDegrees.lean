module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.OctagonBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairDegrees
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearPanelCompletion

/-!
# Quadratic degree ratio for the original linear octagon pair

The full original factor markings are transported to the marked octagon.
The marked octagon gives opposite parity, the perpendicular Cartan gives
divisibility of the odd degree, and the (1K) parameter bound leaves only the
factor two.  This is the numerical front end of Fong--Seitz I (6G); the
centralizer and terminal exclusions are separate consumers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal
open LinearPanel
open ReeSource

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

private theorem binary_linear_marking {Y : Type*} [Group Y] {a : ℕ}
    (ha : 0 < a) (hlinear : ClassicalGroup.IsPSL Y 2 (2^a)) :
    Nonempty (Y ≃* PSL2BinaryMatrixGroup a) := by
  obtain ⟨F, hF, hfin, hcard, ⟨μ⟩⟩ := hlinear
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 2 a) := Fintype.ofFinite _
  let θ : F ≃+* GaloisField 2 a := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using
      hcard.trans (GaloisField.card 2 a ha.ne').symm)
  exact ⟨μ.trans (Atlas.fieldEquivPSL 2 θ)⟩

private theorem quadratic_of_oriented_bound {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hoa : Odd a) (heb : Even b) (hdiv : a ∣ b) (hbound : b ≤ 2*a) :
    b = 2*a := by
  obtain ⟨k, rfl⟩ := hdiv
  have hkbound : k ≤ 2 := Nat.le_of_mul_le_mul_left (by
    simpa only [Nat.mul_comm] using hbound) ha
  interval_cases k
  · simp at hb
  · exact ((Nat.not_even_iff_odd.mpr hoa) (by simpa using heb)).elim
  · exact Nat.mul_comm a 2

private theorem quadratic_of_oriented_bound_symm {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hea : Even a) (hob : Odd b) (hdiv : b ∣ a) (hbound : a ≤ 2*b) :
    a = 2*b := quadratic_of_oriented_bound hb ha hob hea hdiv hbound

/-- The original linear factors in an octagon have degrees in a quadratic
ratio, with the odd endpoint retained in either orientation. -/
theorem original_linear_factor_quadratic_degrees
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
        inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^b)) :
    (Odd a ∧ b = 2*a) ∨ (Odd b ∧ a = 2*b) := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨μi⟩ := binary_linear_marking ha hi
  obtain ⟨μj⟩ := binary_linear_marking hb hj
  obtain ⟨σi, Ui, νi, hσi, hCi, _, _, _⟩ := LinearPanel.original_panel Q e h split i μi
  obtain ⟨σj, Uj, νj, hσj, hCj, _, _, _⟩ := LinearPanel.original_panel Q e h split j μj
  have hor := original_linear_pair_oriented_degrees (Q := Q) (split := split) (hm := hm)
    (i := i) (j := j) (hij := hij) (a := a) (b := b) (ha := ha) (hb := hb)
    e h νi Ui hCi νj Uj hCj
  have hci : Nat.card (simpleRoot Q split i) = 2^a := by
    simpa only [HexagonStructure.rootAt_one] using linear_rootAt_card Q split i a σi Ui hσi ha 1
  have hcj : Nat.card (simpleRoot Q split j) = 2^b := by
    simpa only [HexagonStructure.rootAt_one] using linear_rootAt_card Q split j b σj Uj hσj hb 1
  have hbound : b ≤ 2*a := octagon_binary_degree_le_twice Q split hm i j hij hci hcj
  have hbound' : a ≤ 2*b := octagon_binary_degree_le_twice Q split hm j i hij.symm hcj hci
  rcases hor with ⟨hoa, heb, hdiv⟩ | ⟨hea, hob, hdiv⟩
  · exact Or.inl ⟨hoa, quadratic_of_oriented_bound ha hb hoa heb hdiv hbound⟩
  · exact Or.inr ⟨hob, quadratic_of_oriented_bound_symm ha hb hea hob hdiv hbound'⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
