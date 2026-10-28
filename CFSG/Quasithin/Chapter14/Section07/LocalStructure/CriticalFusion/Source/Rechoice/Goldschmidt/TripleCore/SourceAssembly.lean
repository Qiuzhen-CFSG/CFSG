module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.FiveChiefFactors
public import Theory.GroupTheory.NoncentralChiefRefinement.OrderBound

/-!
# The first Goldschmidt stage of 14.7.70

A noncentral binary chief factor has order at least four, so the checked five
factors of the original L₁ give |L₁| ≥ 1024. Its literal embedding into the
left vertex gives the same lower bound there. If O₂(I) were trivial, the
universal vertex-order consequence of F.6.5 would give |left| ≤ 384. This
contradiction supplies the remaining nontrivial-core field of `CoreFacts`.
The existing source geometry then makes V_I elementary and identifies the
core with its exact centralizer; centralization itself is unconditional.

The F.6.5 premise is universal over all finite groups and genuine Goldschmidt
triples, not a premise about this I. Its producer is qt-f06-amalgams: it must
be deduced from the actual eleven marked amalgams, including q = 2 in the
relevant F.1.12 cases. No family label or assumed model cardinality establishes
that implication. The original upper marking and commutator identity retain
their source producers. The final source owner qt-14-07-rechoice-goldschmidt
must discharge these inputs together with Structural1222 and Uniqueness127.
This module completes the conditional CoreFacts constructor, not all of
14.7.70 or the later rank-three recognition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.70, printed p.1074 (PDF p.1091); F.6.5, printed p.305;
F.1.12(1),(2),(3),(8),(12),(13), printed pp.262–263.
-/

public section
noncomputable section
open Subgroup NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.SourceAssembly
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- The five literal original chief factors force the original L₁ order. -/
theorem original_order_ge_1024 (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    1024 ≤ Nat.card (F.Li L 1) := by
  obtain ⟨s, hs0, hs1⟩ := exists_chiefSeries (⊥ : NormalNode (F.Li L 1)) ⊤ bot_le
  have hcount := LeftChiefFactors.originalChief_count_of_upperMarking
    d c structural uniqueness mark duality hcomm s hs0 hs1
  calc
    1024 = (4 : ℕ) ^ 5 := by norm_num
    _ ≤ 4 ^ s.noncentralTwoCount := Nat.pow_le_pow_right (by decide) hcount
    _ ≤ Nat.card (F.Li L 1) := s.four_pow_noncentralTwoCount_le_card hs0 hs1

/-- The original L₁ embeds in L₁T and hence in the literal left vertex in I. -/
theorem left_order_ge_1024 (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    1024 ≤ Nat.card (left c) := by
  calc
    1024 ≤ Nat.card (F.Li L 1) :=
      original_order_ge_1024 d c structural uniqueness mark duality hcomm
    _ ≤ Nat.card (group F L) := card_le_of_le (show F.Li L 1 ≤ group F L from le_sup_left)
    _ = Nat.card (left c) := Nat.card_congr (LeftChiefFactors.sourceToLeftEquiv c).toEquiv

/-- Apply the universal earlier amalgam bound to the constructed source triple. -/
theorem core_nontrivial (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (geometry : Geometry d c)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
      ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384) :
    pCore 2 (I c) ≠ ⊥ := by
  intro hcore
  have hsmall := amalgams (I c) (left c) (right c)
    (LeftChiefFactors.triple d c geometry structural) hcore
  have hlarge := left_order_ge_1024 d c structural uniqueness mark duality hcomm
  omega

/-- Construct every CoreFacts field from the original source inputs and the
universal F.6.5 consequence. No local count or nontrivial-core premise remains. -/
theorem coreFacts (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (geometry : Geometry d c)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
      ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384) :
    CoreFacts c := by
  have hcore := core_nontrivial d c geometry structural uniqueness mark duality hcomm amalgams
  exact ⟨LeftChiefFactors.triple d c geometry structural, hcore,
    VI_elementary d c hcore, core_centralizes_VI d c⟩

/-- The existing source kernel constructs the duality. This final adapter
also records the exact centralizer equality from the original geometry. -/
theorem coreFacts_of_source (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (geometry : Geometry d c)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
      ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384) :
    CoreFacts c ∧ pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) := by
  have hc := d.sectionCentralizer_of_earlier_setup structural uniqueness
  obtain ⟨X, aX, mX, hs⟩ := CriticalIntersections.exists_sourceDuality d hc
  let := aX
  let := mX
  obtain ⟨duality⟩ := hs
  exact ⟨coreFacts d c geometry structural uniqueness mark duality hcomm amalgams,
    geometry.core_identification⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.SourceAssembly
