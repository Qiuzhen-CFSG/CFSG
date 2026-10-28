module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.GroupTheory.PresentedGroup

/-!
# The elementary presentation mapping onto SL

The generators are the actual roots `1 + a Eᵢⱼ`. Additivity, distant
commutation and the three-index commutator relation define a presented
group, with a proved surjection onto SL and its projective quotient.
Faithfulness of the matrix map is a separate theorem. In particular this
construction alone asserts neither a presentation theorem nor universality.

Source: Steinberg, *Lectures on Chevalley Groups*, Section 6, Theorem 9
and its explicit SL example; local transcription
`refs/KGroup/GLS3/Chapter2St1.tex`, printed p.74. These are the relations
used for the linear covering calculation of GLS3, Section 6.1.
-/

@[expose] public section

namespace Theory.SpecificGroups.LinearHigher

open scoped MatrixGroups commutatorElement
open Matrix.SpecialLinearGroup

universe u v
variable {n : ℕ} {F : Type u} [Field F]

abbrev Root (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

def root (i j : Fin n) (hij : i ≠ j) : Root n := ⟨(i, j), hij⟩

def matrixRoot (r : Root n) (a : F) : SL(n, F) := transvection r.property a

def projectiveRoot (r : Root n) (a : F) : PSL(n, F) :=
  QuotientGroup.mk (matrixRoot r a)

/-- The elementary Steinberg relations, with their coefficient field retained. -/
structure Relations {E : Type v} [Group E] (x : Root n → F → E) : Prop where
  add : ∀ r a b, x r a * x r b = x r (a + b)
  distant : ∀ r s a b, r.val.2 ≠ s.val.1 → s.val.2 ≠ r.val.1 →
    ⁅x r a, x s b⁆ = 1
  chain : ∀ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) a b,
    ⁅x (root i j hij) a, x (root j k hjk) b⁆ = x (root i k hik) (a * b)

inductive Relator : FreeGroup (Root n × F) → Prop
  | add (r : Root n) (a b : F) : Relator
      (FreeGroup.of (r, a) * FreeGroup.of (r, b) * (FreeGroup.of (r, a + b))⁻¹)
  | distant (r s : Root n) (a b : F)
      (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) :
      Relator ⁅FreeGroup.of (r, a), FreeGroup.of (s, b)⁆
  | chain (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F) :
      Relator (⁅FreeGroup.of (root i j hij, a), FreeGroup.of (root j k hjk, b)⁆ *
        (FreeGroup.of (root i k hik, a * b))⁻¹)

abbrev SteinbergGroup (n : ℕ) (F : Type u) [Field F] :=
  PresentedGroup {w : FreeGroup (Root n × F) | Relator w}

def generator (r : Root n) (a : F) : SteinbergGroup n F := PresentedGroup.of (r, a)

theorem generator_relations : Relations (generator (n := n) (F := F)) where
  add r a b := by
    apply mul_inv_eq_one.mp
    simpa only [map_mul, map_inv, generator, PresentedGroup.of] using
      (PresentedGroup.one_of_mem (rels := {w | Relator w}) (Relator.add r a b))
  distant r s a b hrs hsr := by
    simpa only [map_commutatorElement, generator, PresentedGroup.of] using
      (PresentedGroup.one_of_mem (rels := {w | Relator w}) (Relator.distant r s a b hrs hsr))
  chain i j k hij hjk hik a b := by
    apply mul_inv_eq_one.mp
    simpa only [map_mul, map_inv, map_commutatorElement, generator, PresentedGroup.of] using
      (PresentedGroup.one_of_mem (rels := {w | Relator w})
        (Relator.chain i j k hij hjk hik a b))

theorem Relations.eval_relator {E : Type v} [Group E] {x : Root n → F → E}
    (h : Relations x) {w : FreeGroup (Root n × F)} (hw : Relator w) :
    FreeGroup.lift (fun p => x p.1 p.2) w = 1 := by
  cases hw with
  | add r a b => simp [h.add r a b]
  | distant r s a b hrs hsr => simpa using h.distant r s a b hrs hsr
  | chain i j k hij hjk hik a b => simp [h.chain i j k hij hjk hik a b]

def lift {E : Type v} [Group E] {x : Root n → F → E} (h : Relations x) :
    SteinbergGroup n F →* E := PresentedGroup.toGroup (fun _ hw => h.eval_relator hw)

@[simp] theorem lift_generator {E : Type v} [Group E] {x : Root n → F → E}
    (h : Relations x) (r : Root n) (a : F) : lift h (generator r a) = x r a :=
  PresentedGroup.toGroup.of _

theorem matrixRoot_relations : Relations (matrixRoot (n := n) (F := F)) where
  add r a b := (transvection_add r.property a b).symm
  distant r s a b hrs hsr := by
    apply Commute.commutator_eq
    change matrixRoot r a * matrixRoot s b = matrixRoot s b * matrixRoot r a
    apply Subtype.ext
    simp only [matrixRoot, coe_mul, transvection_coe, mul_add, add_mul, one_mul,
      mul_one, Matrix.single_mul_single_of_ne _ _ _ _ hrs,
      Matrix.single_mul_single_of_ne _ _ _ _ hsr, add_zero]
    abel
  chain i j k hij hjk hik a b := Atlas.elementary_commutator hik hij hjk a b

theorem Relations.map {E H : Type*} [Group E] [Group H] {x : Root n → F → E}
    (h : Relations x) (f : E →* H) : Relations (fun r a => f (x r a)) where
  add r a b := by rw [← map_mul, h.add]
  distant r s a b hrs hsr := by
    rw [← map_commutatorElement, h.distant r s a b hrs hsr, map_one]
  chain i j k hij hjk hik a b := by
    rw [← map_commutatorElement, h.chain i j k hij hjk hik a b]

theorem projectiveRoot_relations : Relations (projectiveRoot (n := n) (F := F)) :=
  matrixRoot_relations.map (QuotientGroup.mk' (Subgroup.center SL(n, F)))

def matrixMap : SteinbergGroup n F →* SL(n, F) := lift matrixRoot_relations

def projectiveMap : SteinbergGroup n F →* PSL(n, F) := lift projectiveRoot_relations

@[simp] theorem matrixMap_generator (r : Root n) (a : F) :
    matrixMap (generator r a) = matrixRoot r a := lift_generator _ _ _

@[simp] theorem projectiveMap_generator (r : Root n) (a : F) :
    projectiveMap (generator r a) = projectiveRoot r a := lift_generator _ _ _

theorem matrixMap_surjective (hn : 2 ≤ n) :
    Function.Surjective (matrixMap (n := n) (F := F)) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  intro g
  change g ∈ matrixMap.range
  apply Atlas.sl_elementary_induction (fun g => g ∈ matrixMap.range) _
    (fun _ _ => Subgroup.mul_mem _) g
  intro i j hij a
  exact ⟨generator (root i j hij) a, matrixMap_generator _ _⟩

theorem projectiveMap_eq : projectiveMap (n := n) (F := F) =
    (QuotientGroup.mk' (Subgroup.center SL(n, F))).comp matrixMap := by
  apply PresentedGroup.ext
  rintro ⟨r, a⟩
  change projectiveMap (generator r a) = QuotientGroup.mk (matrixMap (generator r a))
  rw [projectiveMap_generator, matrixMap_generator]
  rfl

theorem projectiveMap_surjective (hn : 2 ≤ n) :
    Function.Surjective (projectiveMap (n := n) (F := F)) := by
  rw [projectiveMap_eq]
  exact (QuotientGroup.mk'_surjective _).comp (matrixMap_surjective hn)

end Theory.SpecificGroups.LinearHigher
