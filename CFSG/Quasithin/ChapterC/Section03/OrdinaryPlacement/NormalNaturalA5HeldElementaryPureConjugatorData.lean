module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryNative
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.NodeMembers
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.FiniteFusion.Tables

/-!
# Actual conjugators for the six pure Held elementary rows

The six literal subgroups outside the marked rank-six rows are carried into
the published rank-four rows 9 and 11 by explicit words already used in the
involution fusion forest. Each element is checked on the faithful four-point
base and identified with a certified member of the unchanged target row.
No normalizer, Sylow-normality or abstract subgroup recognition is assumed.
-/

public section
namespace Held.OrdinaryElementary.PureConjugators
open Subgroup Held.InvolutionFixedData.Coverage
open Held.InvolutionFixedData.Coverage.FiniteFusion
open Held.LocalPairs.SylowGeometry.Calculations
open Held.TwoLocalCandidates Held.TwoLocalCandidates.Cores
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks

/-- The six original pure maximal elementary rows. -/
@[expose] def sourceRow : Fin 6 → Fin 34 := ![13,14,24,25,26,27]

/-- Their literal targets in the original normalizer catalogue. -/
@[expose] def targetRow : Fin 6 → Fin 22 := ![9,9,11,11,11,9]

/-- Actual Held elements, retaining the certified forest conjugator words. -/
@[expose] def move : Fin 6 → He
  | 0 => rootConjugator 16 * (rootConjugator 20)⁻¹
  | 1 => rootConjugator 24 * (rootConjugator 20)⁻¹
  | 2 => 1
  | 3 => rootConjugator 24 * (rootConjugator 23)⁻¹
  | 4 => rootConjugator 24 * (generator 0 * rootConjugator 23)⁻¹
  | _ => 1

private def shiftPerm (j : Fin 25) : Equiv.Perm (Fin 2058) :=
  ((rootShiftWord j).map (fun k =>
    if k.natAbs = 1 then Tables0.p0 ^ k else bTable ^ (if k < 0 then (-1 : ℤ) else 1))).prod

private theorem shiftPerm_eq (j : Fin 25) : representation (rootShift j) = shiftPerm j := by
  simp only [rootShift,shiftPerm,map_list_prod,List.map_map,Function.comp_def,
    apply_ite representation,map_zpow,aTable_eq,bTable_eq]
  rfl

private def refPerm (j : Fin 25) : Equiv.Perm (Fin 2058) :=
  if rootClass j = 0 then Tables0.p0 else Tables2.p2

private theorem refPerm_eq (j : Fin 25) : representation (rootRepresentative j) = refPerm j := by
  simp only [rootRepresentative,refPerm,apply_ite representation,zTable_eq,aTable_eq]
  rfl

private def conjPerm (j : Fin 25) : Equiv.Perm (Fin 2058) :=
  (normalPerm (rootIndex j) * (shiftPerm j * refPerm j * (shiftPerm j)⁻¹)) ^
    (rootHalf j).val * shiftPerm j

private theorem conjPerm_eq (j : Fin 25) : representation (rootConjugator j) = conjPerm j := by
  simp only [rootConjugator,conjPerm,MulAut.conj_apply,map_mul,map_inv,
    map_pow,normalForm_representation,shiftPerm_eq,refPerm_eq]

private def movePerm : Fin 6 → Equiv.Perm (Fin 2058)
  | 0 => conjPerm 16 * (conjPerm 20)⁻¹
  | 1 => conjPerm 24 * (conjPerm 20)⁻¹
  | 2 => 1
  | 3 => conjPerm 24 * (conjPerm 23)⁻¹
  | 4 => conjPerm 24 * (generatorAction 0 * conjPerm 23)⁻¹
  | _ => 1

private theorem movePerm_eq (k : Fin 6) : representation (move k) = movePerm k := by
  fin_cases k <;> simp [move,movePerm,map_mul,map_inv,map_one,
    conjPerm_eq,generatorAction_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem moved_checked : ∀ k : Fin 6, ∀ v : Fin 192,
    (NativeCoverage.candidateMask (sourceRow k)).testBit v.val = true →
      (members (some (targetRow k))).any (fun m => sameAction
        (movePerm k * normalPerm (NativeCoverage.vertexIndex v) * (movePerm k)⁻¹)
        (normalFormAction m)) = true := by
  decide +kernel

/-- Every element of each original pure row lands in the actual published
rank-four subgroup under its specified Held conjugator. -/
theorem moved_native_mem (k : Fin 6) (v : Fin 192)
    (hv : (NativeCoverage.candidateMask (sourceRow k)).testBit v.val = true) :
    (MulAut.conj (move k)) (NativeCoverage.native v).val ∈ ambient (targetRow k) := by
  obtain ⟨m,hm,he⟩ := List.any_eq_true.mp (moved_checked k v hv)
  have heq : (MulAut.conj (move k)) (NativeCoverage.native v).val = (normalForm m).val := by
    apply Held.eq_of_four_point_images
    simp only [MulAut.conj_apply,map_mul,map_inv,movePerm_eq,NativeCoverage.native,
      normalForm_representation]
    have hh := of_decide_eq_true he
    simpa only [← normalForm_representation,← normalFormAction_eq] using hh
  rw [heq]
  exact ⟨normalForm m,(certified_members (some (targetRow k)) _).mpr ⟨m,hm,rfl⟩,rfl⟩

end Held.OrdinaryElementary.PureConjugators
