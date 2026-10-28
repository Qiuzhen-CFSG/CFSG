module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Markings
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointOrbitCardinality

/-!
# Selecting the two L₅(2) module rows

The actual simple quotient L/O₂(L) has order 9,999,360. The seven-case
source theorem therefore leaves only the five-dimensional natural action
or the irreducible ten-dimensional action. The latter is marked on the
full original V, including its dual by the complementary-wedge map.
The natural action gives the full original ambient natural marking.

This uses ModuleAlternatives1222 only at the specified G,T,L,V. Its
producer is qt-d-1222-modules; final discharge of earlier-source inputs
belongs to qt-d-1332-source. The remaining exterior exclusion stays with
qt-d-1251-source.
Source: Aschbacher--Smith, 12.2.2(3) and 12.5.1, printed pp.795,816--817.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private def linearFiveQuotientEquiv {A : Type*} [Group A]
    (h : ClassicalGroup.IsPSL A 5 2) : A ≃* SL(5,ZMod 2) := Classical.choice (by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  exact ⟨(e.trans (Atlas.fieldEquivPSL 5 (FiniteField.ringEquivOfCardEq hc))).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 5))⟩)

/-- The seven-case theorem selects actual natural or exterior coordinates,
without passing the exterior exclusion as an input. -/
theorem natural_or_exterior_of_moduleAlternatives (D : ChosenModule T L V)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 5 2)
    (rows : ModuleAlternatives1222 D) :
    Section09.NaturalModule D 5 ∨ Nonempty (ExteriorMarking D) := by
  let e := linearFiveQuotientEquiv hL
  have hcard : Nat.card (L ⧸ pCore 2 L) = 9999360 :=
    (Nat.card_congr e.toEquiv).trans SL5ExteriorSquare.card_specialLinearFive
  have hs : IsSimpleGroup (L ⧸ pCore 2 L) := by
    let := Atlas.psl_simple_high_rank (F := ZMod 2) 5 (by decide)
    exact (e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 5)).symm).isSimpleGroup
  let := D.actionCentralizer_normal
  have halt (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 8)
      (f : (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin n)) : False := by
    have hc := (Nat.card_congr ((D.coreToFaithfulEquiv hs).trans f).toEquiv).symm.trans hcard
    let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc
    have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl | rfl <;> norm_num at hc
  cases rows with
  | linear n hn a =>
    have hc := (Nat.card_congr a.groupEquiv.toEquiv).symm.trans hcard
    rcases hn with rfl | rfl | rfl
    · rw [Atlas.Comparisons.Exceptional.sl3Two_card] at hc
      contradiction
    · rw [Atlas.Order20160A8.sl4Two_card] at hc
      contradiction
    · exact Or.inl (naturalModule_of_actionEquiv D 5 a)
  | linearThreeExtension f _ _ =>
    have hc := (Nat.card_congr f.toEquiv).symm.trans hcard
    rw [Atlas.Comparisons.Exceptional.sl3Two_card] at hc
    contradiction
  | linearFiveExterior f hd hi =>
    exact Or.inr (exteriorMarking_of_irreducible_ten D f hd hi)
  | alternating n hlo hhi a => exact (halt n hlo hhi a.groupEquiv).elim
  | alternatingSevenFour f _ => exact (halt 7 (by decide) (by decide) f).elim
  | g2 a =>
    have hc := (Nat.card_congr a.groupEquiv.toEquiv).symm.trans hcard
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hc
    contradiction
  | tripleSix f _ _ _ =>
    have hc := (Nat.card_congr f.toEquiv).symm.trans hcard
    rw [Atlas.Codes.hexEven_card] at hc
    contradiction

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
