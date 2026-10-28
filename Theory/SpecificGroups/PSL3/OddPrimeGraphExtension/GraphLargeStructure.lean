module

public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# The simple socle of the literal PSL₃ graph extension

The preimage of Inn(PSL₃(F)) inside the inner-and-graph join is isomorphic
to PSL₃(F). It has trivial centralizer, and its quotient is a two-group,
since the graph automorphism squares to one. Thus the solvable radical and
two-core vanish and the intrinsic generalized Fitting subgroup is precisely
this inner subgroup. Every Sylow two-subgroup supplements it.

These facts supply the whole-group component case in the odd-prime graph
branch of Aschbacher--Smith E.1.14(7), printed p.214, with E.1.2 on p.210.
Simplicity is inherited from the source. No odd-field restriction or separate
simplicity certification is needed for these structural conclusions.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- The actual inner automorphism subgroup, intrinsic to the graph extension. -/
@[expose] def innerPart : Subgroup (graphExtension F) :=
  (MulAut.innerSubgroup PSL(3,F)).subgroupOf (graphExtension F)

instance innerPart_normal : (innerPart F).Normal := inferInstanceAs
  ((MulAut.innerSubgroup PSL(3,F)).subgroupOf (graphExtension F)).Normal

omit [Finite F] in
private theorem center_PSL_eq_bot : center PSL(3,F) = ⊥ := by
  let _ : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center PSL(3,F)) inferInstance).resolve_right
    (fun h => Group.IsPerfect.not_isMulCommutative PSL(3,F) (center_eq_top_iff.mp h))

/-- Conjugation identifies PSL₃ with the marked inner subgroup. -/
noncomputable def innerPartEquiv : PSL(3,F) ≃* innerPart F :=
  (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot (center_PSL_eq_bot F))).trans
    (subgroupOfEquivOfLe (show MulAut.innerSubgroup PSL(3,F) ≤ graphExtension F from
      le_sup_left)).symm

instance innerPart_simple : IsSimpleGroup (innerPart F) := (innerPartEquiv F).symm.isSimpleGroup

instance innerPart_perfect : Group.IsPerfect (innerPart F) := by
  let _ : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  exact Group.IsPerfect.ofSurjective (f := (innerPartEquiv F).toMonoidHom) (innerPartEquiv F).surjective

omit [Finite F] in
/-- The inner subgroup acts faithfully inside the graph extension. -/
theorem innerPart_centralizer : centralizer (innerPart F : Set (graphExtension F)) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hc : (x : MulAut PSL(3,F)) ∈ centralizer (MulAut.innerSubgroup PSL(3,F) : Set _) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h := mem_centralizer_iff.mp hx (⟨y, (show MulAut.innerSubgroup PSL(3,F) ≤ graphExtension F from le_sup_left) hy⟩ : graphExtension F) hy
    exact congrArg Subtype.val h
  rw [MulAut.centralizer_innerSubgroup_eq_bot (center_PSL_eq_bot F), mem_bot] at hc
  exact Subtype.ext hc

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
/-- The quotient above the actual inner subgroup is a two-group. -/
theorem innerPart_quotient : IsPGroup 2 (graphExtension F ⧸ innerPart F) := by
  let C := (zpowers (OuterSolvable.graph F)).subgroupOf (graphExtension F)
  have hC : IsPGroup 2 C := by
    apply IsPGroup.comap_subtype
    apply IsPGroup.of_card_dvd_pow (n := 1)
    simpa only [Nat.card_zpowers, pow_one] using
      orderOf_dvd_of_pow_eq_one (OuterSolvable.graph_sq F)
  apply isPGroup_quotient_of_sup_eq_top (innerPart F) C hC
  apply (Subgroup.map_injective (graphExtension F).subtype_injective)
  change ((MulAut.innerSubgroup PSL(3,F)).subgroupOf (graphExtension F) ⊔
    (zpowers (OuterSolvable.graph F)).subgroupOf (graphExtension F)).map _ = _
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show MulAut.innerSubgroup PSL(3,F) ≤ graphExtension F from le_sup_left),
    map_subgroupOf_eq_of_le (show zpowers (OuterSolvable.graph F) ≤ graphExtension F from le_sup_right)]
  rw [← MonoidHom.range_eq_map, range_subtype]
  rfl

/-- There is no nontrivial solvable normal subgroup in this model. -/
theorem radical_eq_bot : solvableRadical (graphExtension F) = ⊥ :=
  SimpleSocle.radical_eq_bot (innerPart F) (innerPart_centralizer F)

/-- The intrinsic two-core of the graph extension is trivial. -/
theorem twoCore_eq_bot : pCore 2 (graphExtension F) = ⊥ :=
  SimpleSocle.pCore_eq_bot (radical_eq_bot F) 2

/-- The intrinsic generalized Fitting subgroup is the marked inner subgroup. -/
theorem generalizedFitting_eq_innerPart : generalizedFitting (graphExtension F) = innerPart F :=
  (simple_two_quotient_structure (innerPart F)
    (Group.IsPerfect.not_isMulCommutative (innerPart F)) (innerPart_quotient F) (twoCore_eq_bot F)).1

omit [IsSimpleGroup PSL(3,F)] in
/-- Every Sylow two-subgroup supplements the inner subgroup. -/
theorem innerPart_sup_sylow (T : Sylow 2 (graphExtension F)) : innerPart F ⊔ (T : Subgroup _) = ⊤ := by
  simpa only [sup_comm] using T.sup_eq_top_of_quotient_isPGroup (innerPart F) (innerPart_quotient F)
/-- The actual model identification on the generalized Fitting subgroup. -/
noncomputable def generalizedFittingEquiv :
    generalizedFitting (graphExtension F) ≃* PSL(3,F) :=
  (MulEquiv.subgroupCongr (generalizedFitting_eq_innerPart F)).trans (innerPartEquiv F).symm

instance generalizedFitting_simple : IsSimpleGroup (generalizedFitting (graphExtension F)) :=
  (generalizedFittingEquiv F).isSimpleGroup

instance generalizedFitting_perfect : Group.IsPerfect (generalizedFitting (graphExtension F)) := by
  let _ : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  exact Group.IsPerfect.ofSurjective (f := (generalizedFittingEquiv F).symm.toMonoidHom)
    (generalizedFittingEquiv F).symm.surjective

/-- The literal Sylow-supplement hypothesis required by the E2 constructor. -/
theorem generalizedFitting_sup_sylow (T : Sylow 2 (graphExtension F)) :
    generalizedFitting (graphExtension F) ⊔ (T : Subgroup _) = ⊤ := by
  rw [generalizedFitting_eq_innerPart]
  exact innerPart_sup_sylow F T

end Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
