module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.TypeASLRootSubgroups

/-!
# The standard upper and lower root curves in SL2

The two elementary transvection morphisms from the additive algebraic group
give the standard upper and lower unipotent curves in `SL2`.  Their point
images generate the full special linear group: Mathlib's transvection
induction reduces an arbitrary determinant-one matrix to these two curves.

This small wrapper fixes the curve names and orientation used by the local
opposite-root recognition theorem.  The coordinate construction itself is the
rank-two specialization of `TypeASLRootSubgroups`; no root-system recognition
or numbered algebraic-group theorem is used here.  These are the standard
matrix root curves underlying GLS3, Theorem 1.9.5(d).
-/

universe u

namespace Theory.AlgebraicGroup

open StandardRootSystem

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The ordered coordinate pair for the standard upper root of `SL2`. -/
@[expose]
public def standardSL2UpperRootIndex : TypeARootIndex 1 :=
  ⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩

/-- The ordered coordinate pair for the standard lower root of `SL2`. -/
@[expose]
public def standardSL2LowerRootIndex : TypeARootIndex 1 :=
  ⟨((1 : Fin 2), (0 : Fin 2)), by decide⟩

/-- The standard upper unipotent curve `t |-> [[1,t],[0,1]]`. -/
public abbrev standardSL2UpperMorphism :
    AlgebraicGroup.Morphism (KPlus k) (slVariety k 2) :=
  typeASLRootMorphism 1 standardSL2UpperRootIndex

/-- The standard lower unipotent curve `t |-> [[1,0],[t,1]]`. -/
public abbrev standardSL2LowerMorphism :
    AlgebraicGroup.Morphism (KPlus k) (slVariety k 2) :=
  typeASLRootMorphism 1 standardSL2LowerRootIndex

@[simp]
public lemma standardSL2UpperMorphism_kPlusPoint (t : k) :
    (standardSL2UpperMorphism (k := k)).onPoints (kPlusPoint t) =
      typeASLRootPoint 1 standardSL2UpperRootIndex t :=
  rfl

@[simp]
public lemma standardSL2LowerMorphism_kPlusPoint (t : k) :
    (standardSL2LowerMorphism (k := k)).onPoints (kPlusPoint t) =
      typeASLRootPoint 1 standardSL2LowerRootIndex t :=
  rfl

/-- The standard upper and lower unipotent curves generate all `SL2` points. -/
public theorem standardSL2_upper_lower_generate :
    Subgroup.closure
        (Set.range (standardSL2UpperMorphism (k := k)).onPoints ∪
          Set.range (standardSL2LowerMorphism (k := k)).onPoints) = ⊤ := by
  let S : Subgroup (Variety.Point (slVariety k 2)) :=
    Subgroup.closure
      (Set.range (standardSL2UpperMorphism (k := k)).onPoints ∪
        Set.range (standardSL2LowerMorphism (k := k)).onPoints)
  change S = ⊤
  apply top_unique
  intro g _hg
  have hmem : ∀ A : Matrix.SpecialLinearGroup (Fin 2) k,
      (slPointEquiv 2).symm A ∈ S := by
    intro A
    refine Matrix.SL2.transvection_induction
      (fun B => (slPointEquiv 2).symm B ∈ S) ?_ ?_ A
    · intro i j hij c
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · apply Subgroup.subset_closure
        exact Set.mem_union_left _ ⟨kPlusPoint c, by rfl⟩
      · apply Subgroup.subset_closure
        exact Set.mem_union_right _ ⟨kPlusPoint c, by rfl⟩
      · exact (hij rfl).elim
    · intro A B hA hB
      exact S.mul_mem hA hB
  simpa using hmem (slPointEquiv 2 g)

end Theory.AlgebraicGroup
