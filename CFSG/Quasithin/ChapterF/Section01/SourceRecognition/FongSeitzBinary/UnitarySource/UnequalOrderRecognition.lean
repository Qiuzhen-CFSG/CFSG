module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.LinearCartanDivisibility
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.UnequalFactorRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearPanelCompletion

/-!
# The full unequal linear quadrangle row from the original factor orders

The strictly larger original linear factor forces an elementary radical
and commuting crossed roots of the smaller type. Full faithful panel
completion transports both original factor markings, including their
entire Borels, to the actual Cartan maps. The crossed-root centralization
then forces the smaller Cartan image order to divide the larger. Hence
the smaller binary field degree divides the larger one.

The previously proved bound |k| < |F| <= |k|² now forces |F| = |k|².
Thus every unequal linear quadrangle gives the full U₄ comparison, with
no assumed field ratio, core structure or endpoint perfectness. Both
orientations, the smaller binary field, the full Borel, both endpoint
squares and the literal original quotient representatives are retained.
The field-order trichotomy also exhausts the numerical possibilities for
all original linear quadrangles; recognition of the equal branch still
uses its independent source structure.

Only the original F.1.1, marked split quotient of rotation four, and
actual linear factor markings with unequal orders are needed for this
selected U₄ row. Earlier source producers retain quotient/profile and
Weyl selection; the other rows and exhaustive seven-row assembly remain
separate obligations. UnequalOrderApplications supplies the literal
Chapter 12 consumer with its proper-K/full KnownSimple hypotheses.

Source: DGS, Groups and Graphs (1985), (11.6)--(11.7), pp.173--175,
and Theorem D, p.224; Fong--Seitz I (6A)(b), II (8.1)--(8.2), (8B).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include mark h split in
/-- The original factor markings and commuting crossed roots force divisibility of their binary field degrees. -/
theorem marked_linear_commuting_factor_degree_dvd
    {F k : Type*} [Field F] [Finite F] [CharP F 2]
    [Field k] [Finite k] [CharP k 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k))
    (hc : ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥)
    {m n : ℕ} (hmpos : 0 < m) (hnpos : 0 < n)
    (hk : Nat.card k = 2^m) (hF : Nat.card F = 2^n) : m ∣ n := by
  let := Fintype.ofFinite F
  let := Fintype.ofFinite k
  let := Fintype.ofFinite (GaloisField 2 n)
  let := Fintype.ofFinite (GaloisField 2 m)
  let θi : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card] using hF.trans (GaloisField.card 2 n hnpos.ne').symm)
  let θj : k ≃+* GaloisField 2 m := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card] using hk.trans (GaloisField.card 2 m hmpos.ne').symm)
  obtain ⟨σi,Ti,hBi,_,_⟩ := LinearPanel.marked_panel_factor_compatible Q mark h split i
    (μi.trans (Atlas.fieldEquivPSL 2 θi))
  obtain ⟨σj,Tj,hBj,_,_⟩ := LinearPanel.marked_panel_factor_compatible Q mark h split j
    (μj.trans (Atlas.fieldEquivPSL 2 θj))
  exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.linear_commuting_field_degree_dvd
    Q split hm j i hij.symm m n hmpos hnpos σj Tj hBj σi Ti hBi hc
    (LinearThreePresentation.borel_core_eq_bot Q mark h)

include mark h split in
/-- Unequal original linear factors force the exact quadratic field ratio, including a binary smaller field. -/
theorem unequal_linear_factor_orders
    {F k : Type*} [Field F] [Finite F] [CharP F 2]
    [Field k] [Finite k] [CharP k 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k))
    (hlt : Nat.card k < Nat.card F) : Nat.card F = Nat.card k ^ 2 := by
  obtain ⟨_,_,hc,_,hbound,_⟩ := QuadrangleStructure.marked_unequal_linear_structure
    Q mark h split hm i j hij μi μj hlt
  let := Fintype.ofFinite F
  let := Fintype.ofFinite k
  obtain ⟨n,_,hn⟩ := FiniteField.card F 2
  obtain ⟨m,_,hm'⟩ := FiniteField.card k 2
  have hF : Nat.card F = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hk : Nat.card k = 2^(m : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hm'
  have hd := marked_linear_commuting_factor_degree_dvd Q mark h split hm i j hij
    μi μj hc m.pos n.pos hk hF
  have hlt' : (m : ℕ) < (n : ℕ) := by
    rw [hk,hF] at hlt
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  have hle : (n : ℕ) ≤ (m : ℕ)*2 := by
    rw [hk,hF,←pow_mul] at hbound
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound
  have hdegree : (n : ℕ) = (m : ℕ)*2 := by
    obtain ⟨a,ha⟩ := hd
    have hmpos := m.pos
    have ha2 : 2 ≤ a := by nlinarith
    nlinarith
  rw [hF,hk,hdegree,pow_mul]

include mark h split in
/-- Every original linear quadrangle has equal field orders or a quadratic ratio, with either endpoint larger. -/
theorem marked_linear_quadrangle_factor_orders
    {F k : Type*} [Field F] [Finite F] [CharP F 2]
    [Field k] [Finite k] [CharP k 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k)) :
    Nat.card F = Nat.card k ∨ Nat.card F = Nat.card k ^ 2 ∨
      Nat.card k = Nat.card F ^ 2 := by
  rcases lt_trichotomy (Nat.card F) (Nat.card k) with hh | hh | hh
  · exact Or.inr (Or.inr (unequal_linear_factor_orders Q mark h split hm j i hij.symm μj μi hh))
  · exact Or.inl hh
  · exact Or.inr (Or.inl (unequal_linear_factor_orders Q mark h split hm i j hij μi μj hh))

include mark h split in
/-- The full U₄ comparison follows from the original unequal linear factors without a field-ratio or core-structure hypothesis. -/
theorem marked_unequal_linear_unitaryFour_catalogue
    {F k : Type*} [Field F] [Finite F] [CharP F 2]
    [Field k] [Finite k] [CharP k 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k))
    (hlt : Nat.card k < Nat.card F) :
    Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) :=
  marked_quadratic_factor_order_unitaryFour_catalogue Q mark h split hm i j hij μi μj
    (unequal_linear_factor_orders Q mark h split hm i j hij μi μj hlt)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X F k : Type*} [Group G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
  (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k))
  (hlt : Nat.card k < Nat.card F)

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Representation.OrthogonalFourMinus.FiniteModel
open UnitaryPresentation

include mark h split hm hij μi μj hlt in
/-- The model equivalence induces both endpoint maps and the entire overlap
on the same source quotient, without a quadratic field-ratio or core-structure premise. -/
theorem marked_unequal_linear_unitaryFour_comparison
    (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n) :
    ∃ (e : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)) ≃* (X ⧸ Q.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag
          ((pointParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))))
          ((planeParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)))) j)),
      (∀ a : parabolic L S 0, (c.left a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (mark.left a : X ⧸ Q.D)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
          e.symm (mark.middle a : X ⧸ Q.D)) ∧
      (∀ a : parabolic L S 1, (c.right a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (mark.right a : X ⧸ Q.D)) :=
  marked_quadratic_factor_order_unitaryFour_comparison Q mark h split hm i j hij μi μj
    (unequal_linear_factor_orders Q mark h split hm i j hij μi μj hlt) n hk

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Representation.OrthogonalFourMinus.FiniteModel
open UnitaryPresentation
variable {G F k : Type*} [Group G]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
  (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k))
  (hlt : Nat.card k < Nat.card F)
  (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n)

include h split hm hij μi μj hlt hk in
/-- The complete comparison evaluates on the literal original quotient map
at both endpoints and at every element of the whole overlap. -/
theorem original_unequal_linear_unitaryFour_comparison :
    ∃ (e : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)) ≃* ((generated L S) ⧸ Q.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag
          ((pointParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))))
          ((planeParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)))) j)),
      (∀ a : parabolic L S 0, (c.left a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (Q.q ⟨a,parabolic_le_generated 0 a.property⟩)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
          e.symm (Q.q ⟨a,parabolic_le_generated 0 a.property.1⟩)) ∧
      (∀ a : parabolic L S 1, (c.right a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (Q.q ⟨a,parabolic_le_generated 1 a.property⟩)) :=
  original_quadratic_factor_order_unitaryFour_comparison Q h split hm i j hij μi μj
    (unequal_linear_factor_orders Q (originalMarkedIso Q) h split hm i j hij μi μj hlt) n hk

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
