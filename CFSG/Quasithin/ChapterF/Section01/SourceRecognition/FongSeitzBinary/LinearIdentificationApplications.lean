module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.LinearStructure
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericRootCoordinates

/-!
# Original linear local recognition in the structural consumers

The original perfect linear factor now supplies the concrete PSL₂ marking
of the actual Fong--Seitz local permutation group. Substitution removes
both the separate local-model witness and (2B) containment from the initial
hexagon commutator bound. With two linear factors it also supplies the
binary radical-quotient structure used by the subsequent representation.
The actual Weyl order and root-reflection witnesses remain explicit.

For the literal Chapter12 pair ![L,R], original membership of L in the
component family supplies perfectness. Its original PSL₂ quotient then
identifies both the lifted first root group and its full permutation image
with L/O₂(L), and the SAME projection commutes with these equivalences.
In particular its original panel kernel is trivial on that root group.
No perfectness or local model is added at the selected second endpoint.

Source: Fong--Seitz I (5C)(b), pp.25--26, and (6E), pp.43--45;
Aschbacher--Smith Chapter12, p.795. The independent marked split quotient
retains producer qt-dgs85-apartment-exchange. Nonlinear regularity, remaining
local recognition and seven-row marked assembly remain with source
recognition; the original Chapter12 and DGS owners retain final discharge.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- The literal original linear quotient discharges the local-model and kernel premises. -/
theorem linear_hexagon_structure_of_original_factor
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hp : Group.IsPerfect (L i))
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (s : RootReflection Q split i) :
    IsElementaryAbelian 2 (simpleRoot Q split i) ∧
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ≠ ⊥ ∧
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ≤ middleRoots Q split i j := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  let a := linearLocalEquiv Q e h split i hp T hT μ
  exact ⟨simpleRoot_elementary_of_linear Q split i a,
    radical_commutator_ne_bot Q split hm i j hij s,
    radical_commutator_le_middle_of_linear Q split hm i j hij
      (linear_remainder_le_kernel Q e h split i T hT μ) a⟩

include e h in
/-- Both original linear factors supply the actual binary radical quotient. -/
theorem linear_radicalQuotient_elementary_of_original_factors
    {F : Fin 2 → Type*} [∀ i, Field (F i)] [∀ i, Finite (F i)]
    [∀ i, CharP (F i) 2] (hm : rotationOrder Q = 6)
    (hp : ∀ i, Group.IsPerfect (L i))
    (μ : ∀ i, ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F i)) (j : Fin 2) :
    IsElementaryAbelian 2 (RadicalQuotient Q split j) := by
  apply radicalQuotient_elementary Q split hm
  intro i
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  exact simpleRoot_elementary_of_linear Q split i
    (linearLocalEquiv Q e h split i (hp i) T hT (μ i))

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- On the original generated carrier the lift uses the SAME quotient map Q.q. -/
theorem quotient_rankOneLift_apply (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)
    (hp : Group.IsPerfect (L i)) (r : rankOne Q split i) :
    Q.q ⟨MarkedLocal.rankOneLift Q (originalMarkedIso Q) h split i hp r,
      local_le_generated i
        (MarkedLocal.rankOneLift Q (originalMarkedIso Q) h split i hp r).property⟩ =
      (r : (generated L S) ⧸ Q.D) := by
  rw [← original_factorMap_apply]
  exact MarkedLocal.factorMap_rankOneLift Q (originalMarkedIso Q) h split i hp r

open Chapter6.Source.RankOneGeneric
variable {X : Type*} [Group X] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- Recognition of the first local group on the unchanged selected pair. -/
theorem prepared_first_local_identification
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ a : MarkedLocal.originalRankOne Q e split 0 ≃* L ⧸ pCore 2 L,
      ∃ b : localGroup Q split 0 ≃* L ⧸ pCore 2 L,
        ∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 0 r) :=
  MarkedLocal.linear_original_local_identification_of_model Q e (d.hypothesisF11 h hTH)
    split 0 (Chapter1.mem_L_isPerfect h.local_mem.1.1) h.linear

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- Compatible original and permutation-group identifications in the literal Chapter12 input. -/
theorem rankOne_global_first_local_identification
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ a : MarkedLocal.originalRankOne Q e split 0 ≃* L ⧸ pCore 2 L,
      ∃ b : localGroup Q split 0 ≃* L ⧸ pCore 2 L,
        ∀ r, a r = b (MarkedLocal.originalRootProjection Q e split 0 r) :=
  prepared_first_local_identification d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH Q e split

/-- The original full panel kernel meets the first root-generated group trivially. -/
theorem rankOne_global_first_root_kernel_trivial
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    (MarkedLocal.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 0).subgroupOf
      (MarkedLocal.originalRankOne Q e split 0) = ⊥ := by
  let hin := D.rankOne_generic_input_of_many h hmany hn hpsl
  let hf := d.hypothesisF11 hin hTH
  rw [← MarkedLocal.originalRootProjection_ker Q e hf split 0]
  exact (MonoidHom.ker_eq_bot_iff _).mpr
    (MarkedLocal.linear_originalRootProjection_bijective Q e hf split 0
      (Chapter1.mem_L_isPerfect hin.local_mem.1.1) hpsl).1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
