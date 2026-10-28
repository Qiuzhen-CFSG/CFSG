module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.GroupTheory.PresentedGroup

/-!
# Binary degree-five Steinberg generators

The generators are the twenty elementary matrices `1 + Eᵢⱼ` with `i ≠ j`.
The relations are their squares, commuting pairs with `j ≠ k` and `l ≠ i`,
and `[xᵢⱼ,xⱼₖ] = xᵢₖ` for three distinct indices. This module constructs
the presented group and its surjection onto the actual matrix group PSL₅(2).
Injectivity of that surjection is a separate theorem, not part of the definition.

These are the type A₄ Steinberg relations over the field with two elements,
used for the central-extension calculation underlying Aschbacher–Smith I.1.3,
printed p.407, and its reference to GLS98 §6.1.
-/

@[expose] public section

namespace Theory.SpecificGroups.PSL5Two.UniversalCover

open scoped MatrixGroups commutatorElement
open Matrix.SpecialLinearGroup

abbrev G := Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)
abbrev SL := Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
abbrev Root := {p : Fin 5 × Fin 5 // p.1 ≠ p.2}

def root (i j : Fin 5) (hij : i ≠ j) : Root := ⟨(i, j), hij⟩

def matrixRoot (r : Root) : SL := transvection r.property 1

def projectiveRoot (r : Root) : G := QuotientGroup.mk (matrixRoot r)

noncomputable def projectiveEquivSL : G ≃* SL :=
  BinaryLinear.OuterCyclic.projectiveEquivSL (by decide)

@[simp] theorem projectiveEquivSL_root (r : Root) :
    projectiveEquivSL (projectiveRoot r) = matrixRoot r :=
  projectiveEquivSL.apply_symm_apply _

inductive Relator : FreeGroup Root → Prop
  | square (r : Root) : Relator (FreeGroup.of r ^ 2)
  | distant (r s : Root) (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) :
      Relator ⁅FreeGroup.of r, FreeGroup.of s⁆
  | chain (i j k : Fin 5) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
      Relator (⁅FreeGroup.of (root i j hij), FreeGroup.of (root j k hjk)⁆ *
        (FreeGroup.of (root i k hik))⁻¹)

abbrev SteinbergGroup := PresentedGroup {w | Relator w}

def generator (r : Root) : SteinbergGroup := PresentedGroup.of r

/-- The literal equations to be checked in a target group. -/
structure Relations {E : Type*} [Group E] (x : Root → E) : Prop where
  square : ∀ r, x r ^ 2 = 1
  distant : ∀ r s, r.val.2 ≠ s.val.1 → s.val.2 ≠ r.val.1 → ⁅x r, x s⁆ = 1
  chain : ∀ (i j k : Fin 5) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
    ⁅x (root i j hij), x (root j k hjk)⁆ = x (root i k hik)

theorem generator_relations : Relations generator where
  square r := by
    simpa only [map_pow, generator, PresentedGroup.of] using
      (PresentedGroup.one_of_mem (rels := {w | Relator w}) (Relator.square r))
  distant r s hrs hsr := by
    simpa only [map_commutatorElement, generator, PresentedGroup.of] using
      (PresentedGroup.one_of_mem (rels := {w | Relator w}) (Relator.distant r s hrs hsr))
  chain i j k hij hjk hik := by
    apply mul_inv_eq_one.mp
    simpa only [map_mul, map_inv, map_commutatorElement, generator, PresentedGroup.of] using
      (PresentedGroup.one_of_mem (rels := {w | Relator w}) (Relator.chain i j k hij hjk hik))

theorem Relations.eval_relator {E : Type*} [Group E] {x : Root → E}
    (h : Relations x) {w : FreeGroup Root} (hw : Relator w) : FreeGroup.lift x w = 1 := by
  cases hw with
  | square r => simpa using h.square r
  | distant r s hrs hsr => simpa using h.distant r s hrs hsr
  | chain i j k hij hjk hik => simp [h.chain i j k hij hjk hik]

def lift {E : Type*} [Group E] {x : Root → E} (h : Relations x) : SteinbergGroup →* E :=
  PresentedGroup.toGroup (fun _ hw => h.eval_relator hw)

@[simp] theorem lift_generator {E : Type*} [Group E] {x : Root → E}
    (h : Relations x) (r : Root) : lift h (generator r) = x r := PresentedGroup.toGroup.of _

theorem closure_range_generator : Subgroup.closure (Set.range generator) = ⊤ :=
  PresentedGroup.closure_range_of _

theorem matrixRoot_relations : Relations matrixRoot where
  square r := by
    rw [pow_two, matrixRoot, ← transvection_add]
    exact transvection_coeff_zero r.property
  distant r s hrs hsr := by
    apply Commute.commutator_eq
    change matrixRoot r * matrixRoot s = matrixRoot s * matrixRoot r
    apply Subtype.ext
    simp only [matrixRoot, coe_mul, transvection_coe, mul_add, add_mul, one_mul,
      mul_one, Matrix.single_mul_single_of_ne _ _ _ _ hrs,
      Matrix.single_mul_single_of_ne _ _ _ _ hsr, add_zero]
    abel
  chain i j k hij hjk hik := by
    simpa only [matrixRoot, root, mul_one] using
      Atlas.elementary_commutator hik hij hjk (1 : ZMod 2) 1

theorem Relations.map {E H : Type*} [Group E] [Group H] {x : Root → E}
    (h : Relations x) (f : E →* H) : Relations (fun r => f (x r)) where
  square r := by rw [← map_pow, h.square, map_one]
  distant r s hrs hsr := by rw [← map_commutatorElement, h.distant r s hrs hsr, map_one]
  chain i j k hij hjk hik := by rw [← map_commutatorElement, h.chain i j k hij hjk hik]

theorem projectiveRoot_relations : Relations projectiveRoot :=
  matrixRoot_relations.map (QuotientGroup.mk' (Subgroup.center SL))

def matrixMap : SteinbergGroup →* SL := lift matrixRoot_relations
def projectiveMap : SteinbergGroup →* G := lift projectiveRoot_relations

@[simp] theorem matrixMap_generator (r : Root) : matrixMap (generator r) = matrixRoot r :=
  lift_generator _ _

@[simp] theorem projectiveMap_generator (r : Root) :
    projectiveMap (generator r) = projectiveRoot r := lift_generator _ _

theorem matrixMap_surjective : Function.Surjective matrixMap := by
  intro g
  change g ∈ matrixMap.range
  apply Atlas.sl_elementary_induction (fun g => g ∈ matrixMap.range) _
    (fun _ _ => Subgroup.mul_mem _) g
  intro i j hij a
  have ha : a = 0 ∨ a = 1 := by exact (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
  rcases ha with rfl | rfl
  · rw [transvection_coeff_zero]
    exact matrixMap.range.one_mem
  · exact ⟨generator (root i j hij), matrixMap_generator _⟩

theorem projectiveMap_eq :
    projectiveMap = (QuotientGroup.mk' (Subgroup.center SL)).comp matrixMap := by
  apply PresentedGroup.ext
  intro r
  change projectiveMap (generator r) = QuotientGroup.mk (matrixMap (generator r))
  rw [projectiveMap_generator, matrixMap_generator]
  rfl

theorem projectiveMap_surjective : Function.Surjective projectiveMap := by
  rw [projectiveMap_eq]
  exact (QuotientGroup.mk'_surjective _).comp matrixMap_surjective

theorem closure_range_projectiveRoot : Subgroup.closure (Set.range projectiveRoot) = ⊤ := by
  have hr : Set.range projectiveRoot = projectiveMap '' Set.range generator := by
    rw [← Set.range_comp]
    congr 1
    funext r
    exact (projectiveMap_generator r).symm
  rw [hr, ← MonoidHom.map_closure, closure_range_generator,
    Subgroup.map_top_of_surjective _ projectiveMap_surjective]

/-- Every Steinberg generator is a commutator, already in the presented group. -/
instance steinbergGroup_isPerfect : Group.IsPerfect SteinbergGroup := by
  constructor
  apply top_unique
  rw [← closure_range_generator, Subgroup.closure_le]
  rintro _ ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide : 2 < 5)
  change generator (root i j hij) ∈ commutator SteinbergGroup
  rw [← generator_relations.chain i k j hki.symm hkj hij]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end Theory.SpecificGroups.PSL5Two.UniversalCover
