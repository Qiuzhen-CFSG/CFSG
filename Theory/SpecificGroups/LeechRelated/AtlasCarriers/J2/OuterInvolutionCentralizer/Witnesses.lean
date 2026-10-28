module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Seed
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.Model
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.TableSupport
import Mathlib.Tactic.FinCases

/-!
# Explicit elements and the fixed-point action of the outer centralizer

The ATLAS involution fixes the first generator and a displayed word of order
eight. Their actions on its fourteen fixed points are the two permutations
in `Model`. Every element of the entire fixed subgroup acts on those points,
so the generated model is contained in the range of this action. Faithfulness
and exhaustive coverage are established separately by cardinality bounds.

Source: retained ATLAS `J2G1-p100B0`; GLS3 Table 5.3g, class 2C, and
Aschbacher--Smith 16.1.5(8), printed p.1172. The word was discovered in the
retained `Scratch/J2Outer/short_generators.py`; its identities are checked here.
-/

public section
namespace Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
open Theory.GroupTheory GeneratorPair ExceptionalParabolics
open GeneratorPair.SecondOrbitCertificate

@[expose] def eightWord : List (Fin 3) :=
  [1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1]

@[expose] def eight : Carrier := Seed.localWord eightWord

private def eightTable : Equiv.Perm (Fin 100) where
  toFun := ![92, 67, 29, 45, 37, 70, 4, 15, 41, 10, 0, 54, 80, 88, 65, 39, 34, 49, 89, 72, 78, 74, 99, 8, 81, 12, 26, 48, 23, 1, 5, 36, 82, 84, 31, 50, 61, 95, 60, 77, 75, 62, 71, 7, 86, 35, 58, 94, 22, 17, 24, 19, 66, 3, 85, 91, 28, 53, 14, 59, 38, 97, 32, 13, 33, 51, 64, 63, 46, 20, 79, 47, 68, 11, 44, 43, 42, 83, 98, 30, 52, 57, 56, 40, 25, 69, 21, 16, 96, 76, 18, 55, 9, 87, 90, 27, 2, 93, 73, 6]
  invFun := ![10, 29, 96, 53, 6, 30, 99, 43, 23, 92, 9, 73, 25, 63, 58, 7, 87, 49, 90, 51, 69, 86, 48, 28, 50, 84, 26, 95, 56, 2, 79, 34, 62, 64, 16, 45, 31, 4, 60, 15, 83, 8, 76, 75, 74, 3, 68, 71, 27, 17, 35, 65, 80, 57, 11, 91, 82, 81, 46, 59, 38, 36, 41, 67, 66, 14, 52, 1, 72, 85, 5, 42, 19, 98, 21, 40, 89, 39, 20, 70, 12, 24, 32, 77, 33, 54, 44, 93, 13, 18, 94, 55, 0, 97, 47, 37, 88, 61, 78, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem localWord_inclusion (w : List (Fin 3)) :
    inclusion (Seed.localWord w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a, b, b⁻¹] i * Seed.localWord w) = _
    rw [map_mul, ih]
    congr 1
    fin_cases i <;> simp [a, b, inclusion, generatorA_eq_table, generatorB_eq_table]

set_option maxRecDepth 100000 in
private theorem eight_inclusion : inclusion eight = eightTable := by
  rw [eight, localWord_inclusion]
  apply Equiv.ext
  have h : ∀ p : Fin 100,
      evalWord ![tableA, tableB, tableB⁻¹] eightWord p = eightTable p := by
    apply allFin
    decide +kernel
  exact h

theorem eight_fixed : involutionAut eight = eight := by
  apply inclusion_injective
  change involution * inclusion eight * involution⁻¹ = inclusion eight
  rw [eight_inclusion]
  decide +kernel

/-- Carrier elements fixed by the exact involutory automorphism commute with
its permutation on every one of the original hundred points. -/
theorem fixed_commutes (g : involutionAut.fixedSubgroup) (p : Fin 100) :
    involution (inclusion g.val p) = inclusion g.val (involution p) := by
  have h := congrArg inclusion ((MulAut.mem_fixedSubgroup involutionAut g.val).mp g.property)
  change involution * inclusion g.val * involution⁻¹ = inclusion g.val at h
  have h' : involution * inclusion g.val = inclusion g.val * involution :=
    (mul_inv_eq_iff_eq_mul).mp h
  exact congrArg (fun f : Equiv.Perm (Fin 100) => f p) h'

@[expose] def point (i : Fin 14) : Fin 100 :=
  ![0, 83, 92, 40, 49, 9, 7, 75, 17, 39, 10, 15, 43, 77] i

private def pointIndex (i : Fin 100) : Fin 14 :=
  ![0, 0, 0, 0, 0, 0, 0, 6, 0, 5, 10, 0, 0, 0, 0, 11, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 3, 0, 0, 12, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 13, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0] i

private theorem point_fixed : ∀ i, involution (point i) = point i := by decide +kernel
private theorem index_point : ∀ i, pointIndex (point i) = i := by decide +kernel
private theorem point_injective : Function.Injective point :=
  Function.LeftInverse.injective index_point
private theorem point_index : ∀ p, involution p = p → point (pointIndex p) = p := by
  decide +kernel

/-- The listed fourteen points are exactly the fixed points. -/
private def pointEquiv : Fin 14 ≃ {p : Fin 100 // involution p = p} where
  toFun i := ⟨point i, point_fixed i⟩
  invFun p := pointIndex p.val
  left_inv := index_point
  right_inv p := Subtype.ext (point_index p.val p.property)

private theorem preserves_points (g : involutionAut.fixedSubgroup) (p : Fin 100) :
    involution (inclusion g.val p) = inclusion g.val p ↔ involution p = p := by
  rw [fixed_commutes]
  exact (inclusion g.val).injective.eq_iff

private def pointAction : involutionAut.fixedSubgroup →*
    Equiv.Perm {p : Fin 100 // involution p = p} where
  toFun g := (inclusion g.val).subtypePerm (preserves_points g)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Restriction of the full fixed subgroup to its fourteen fixed points. -/
def action : involutionAut.fixedSubgroup →* Equiv.Perm (Fin 14) :=
  pointEquiv.symm.permCongrHom.toMonoidHom.comp pointAction

theorem action_point (g : involutionAut.fixedSubgroup) (i : Fin 14) :
    point (action g i) = inclusion g.val (point i) := by
  change point (pointIndex (inclusion g.val (point i))) = _
  apply point_index
  rw [fixed_commutes, point_fixed]

def fixedA : involutionAut.fixedSubgroup :=
  ⟨a, (MulAut.mem_fixedSubgroup involutionAut a).mpr involutionAut_a⟩

def fixedB : involutionAut.fixedSubgroup :=
  ⟨eight, (MulAut.mem_fixedSubgroup involutionAut eight).mpr eight_fixed⟩

theorem action_a : action fixedA = modelA := by
  apply Equiv.ext
  intro i
  apply point_injective
  rw [action_point]
  change generatorA (point i) = _
  rw [generatorA_eq_table]
  have h : ∀ i, tableA (point i) = point (modelA i) := by decide +kernel
  exact h i

theorem action_b : action fixedB = modelB := by
  apply Equiv.ext
  intro i
  apply point_injective
  rw [action_point]
  change inclusion eight (point i) = _
  rw [eight_inclusion]
  have h : ∀ i, eightTable (point i) = point (modelB i) := by decide +kernel
  exact h i

/-- Both concrete model generators lift to the literal fixed subgroup. -/
theorem model_le_range : model ≤ action.range := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact ⟨fixedA, action_a⟩
  · rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨fixedB, action_b⟩

end Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
