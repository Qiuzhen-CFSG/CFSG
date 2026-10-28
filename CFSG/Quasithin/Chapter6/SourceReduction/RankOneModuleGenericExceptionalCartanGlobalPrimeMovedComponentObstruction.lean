module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySmallModels
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeMovedComponentJanko

/-!
# The actual simple-model obstruction in the changed-Sylow branch

The original LocalData residual identity supplies movement of the right
factor. A larger changed Sylow supplies a normalized strict overcomponent
in the original common overgroup. Quotienting that overcomponent by its
solvable radical gives an actual nonabelian simple Theorem C model in which
a full-Sylow overgroup has more than one C-component. The proved small-model
exclusions remove the Bender, A₅/A₆ and odd PSL₂ rows from this quotient.

The remaining model exclusions must remove this alternative before local
maximality, and hence `changedSylow_eq_of_right_maximal`, is discharged.
Source: Aschbacher--Smith 1.2.8(1--3), pp.506--507, and the changed-Sylow
argument of 5.2.2, pp.648--649.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- A larger changed Sylow produces a concrete failure of component
uniqueness in a full-Sylow overgroup of a nonabelian simple source model. -/
theorem LocalData.changedSylow_simple_overgroup_obstruction
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hR : R ∈ Chapter1.L G (T : Subgroup G))
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    let X := normalizer (normalizingSylow T R : Set G) ⊔ H
    (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype =
        normalizingSylow T R ∨
      ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
        (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        (let C := I.subgroupOf (I ⊔ (T : Subgroup G))
         let Q := C ⧸ solvableRadical C
         IsSimpleGroup Q ∧ ¬ IsMulCommutative Q ∧
           Chapter1.Section02.MovedMaximality.RemainingSimpleModel Q ∧
           ¬ SylowOvergroupComponentUnique Q) := by
  rcases d.changedSylow_normalized_overcomponent h hH c hd hz hR hnot P hTP with
    he | ⟨I,hRI,hIX,hI,hn⟩
  · exact Or.inl he
  · right
    refine ⟨I,hRI,hIX,hI,hn,?_⟩
    let X := normalizer (normalizingSylow T R : Set G) ⊔ H
    have hX := d.common_normal_overgroup h hH c hd hz
    have hTX : (T : Subgroup G) ≤ X :=
      (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
    have hIl : I ∈ Chapter1.L G (T : Subgroup G) :=
      Chapter1.mem_L_of_cComponent hX.1
        ⟨T.subtype hTX,map_subgroupOf_eq_of_le hTX⟩ hIX hI
    have hm : R < conjugateSpanBy R (T : Subgroup G) := by
      rw [←d.residual_eq_conjugateSpan]
      exact d.right_lt_residual hH.1.1.2 c hd hz
    exact Chapter1.Section02.MovedMaximality.moved_normalized_remaining_simple_quotient
      h.qtke T hR hIl hRI.le hn hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
