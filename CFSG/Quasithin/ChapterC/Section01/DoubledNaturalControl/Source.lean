module

public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.SourceReduction
public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.CoreRigidity
public import CFSG.Quasithin.ChapterC.Section01.BlockDefs

/-!
# The doubled-natural specialization of C.1.37

The proved source reduction gives the literal characteristic Baumann
obstruction or a genuine binary MS group on L joined with Baum(O₂(P)).
Its original doubled module is central in the two-core and has order 64.
The specialized core rigidity theorem identifies it with the commutator
core. Transport through the actual component inclusion returns precisely
[O₂(L),L] in the original ambient group.

Thus the doubled-natural source has no remaining pushing-up or MS
classification premise. The full C.1.37 alternatives for other modules
are separate statements.

Source: Aschbacher--Smith C.1.37(1),(3), printed pp.141--143.
-/

public section
namespace CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
open Subgroup Theory.GroupTheory
universe u
variable {K : Type u} [Group K] [Finite K]
    {κ : GroupClass.{u}} {L P U : Subgroup K} [L.Normal] [U.Normal] {T : Sylow 2 K}

/-- The original characteristic obstruction or the literal doubled
commutator-core equality, with no additional source premises. -/
theorem SourceData.control (d : SourceData κ L P U T) :
    (∃ C : Subgroup (B P), C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map (B P).subtype).Normal) ∨ U = (blockU L).map L.subtype := by
  classical
  rcases d.reduce with hchar | hr
  · exact Or.inl hchar
  · right
    let r : ReductionData d := Classical.choice hr
    let _ := r.module_elementary
    have hc := r.ms.commutatorCore_eq_of_central_sixtyFour (UJ L P U)
      r.module_le_core r.module_centralizes_core r.module_commutator r.module_card
    rw [r.ms.commutatorCore_eq_internal] at hc
    have hm := congrArg (fun A : Subgroup (J L P) => A.map (J L P).subtype) hc
    rw [r.module_map] at hm
    let e : LJ L P ≃* L := SourceData.eLJ
    have he : (blockU (LJ L P)).map e.toMonoidHom = blockU L := by
      rw [blockU, map_commutator, pCore_map_iso 2 e,
        map_top_of_surjective _ e.surjective, blockU]
    have htransport : ((blockU (LJ L P)).map (LJ L P).subtype).map (J L P).subtype =
        (blockU L).map L.subtype := by
      rw [← he, map_map, map_map]
      rfl
    exact hm.symm.trans htransport

end CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
