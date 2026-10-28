module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Fixed.Action
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Mathlib.GroupTheory.PGroup

/-!
# Literal point stabilizers in the natural MS head

The actual ambient action on D/C_D(L) is transitive on its seven nonzero
vectors. A two-subgroup fixes one of these points. Pulling its stabilizer
back to the ambient group yields an index-seven subgroup, and membership
is exactly the original commutator condition modulo C_D(L).
This constructs the point subgroup; identifying its two-core with the MS
radical is a separate geometric assertion.

Source: Aschbacher–Smith C.1.34(5), printed p.137.
-/

@[expose] public section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R) [IsElementaryAbelian 2 (commutatorCore L)]
namespace AbelianCore.NaturalQuotient
variable (q : NaturalQuotient h 1)

/-- The stabilizer in the original ambient group of a specified head point. -/
noncomputable def pointSubgroup (v : BinaryLinearThree.Vector) : Subgroup J where
  carrier := {j | BinaryLinearThree.W (q.ambientActor h j) v = v}
  one_mem' := by
    change BinaryLinearThree.W (q.ambientActor h 1) v = v
    rw [map_one, map_one]
    rfl
  mul_mem' := by
    intro a b ha hb
    change BinaryLinearThree.W (q.ambientActor h (a * b)) v = v
    rw [map_mul, map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    change BinaryLinearThree.W (q.ambientActor h a⁻¹) v = v
    rw [map_inv]
    have he := congrArg (BinaryLinearThree.W (q.ambientActor h a)⁻¹) ha
    simpa only [BinaryLinearThree.W.inv_self_apply] using he.symm

/-- Point stabilizer membership is the literal commutator condition. -/
theorem mem_pointSubgroup_iff (d : commutatorCore L) (j : J) :
    j ∈ q.pointSubgroup h ((q.projection d).toAdd 0) ↔
      j * (d : J) * j⁻¹ * (d : J)⁻¹ ∈ centralizer (L : Set J) := by
  have hker : h.coreAmbientConjugation j d * d⁻¹ ∈ q.projection.ker ↔
      q.projection (h.coreAmbientConjugation j d) = q.projection d := by
    change q.projection (h.coreAmbientConjugation j d * d⁻¹) = 1 ↔ _
    rw [map_mul, map_inv, mul_inv_eq_one]
  rw [q.kernel] at hker
  have hval : ((h.coreAmbientConjugation j d * d⁻¹ : commutatorCore L) : J) =
      j * (d : J) * j⁻¹ * (d : J)⁻¹ := by
    rw [coe_mul, coe_inv, h.coreAmbientConjugation_apply]
  change BinaryLinearThree.W (q.ambientActor h j) ((q.projection d).toAdd 0) =
    (q.projection d).toAdd 0 ↔ _
  rw [← q.ambientActor_equivariant]
  rw [← hval]
  change _ ↔ h.coreAmbientConjugation j d * d⁻¹ ∈ coreFixed L
  rw [hker]
  constructor
  · intro he
    apply Multiplicative.toAdd.injective
    funext i
    simpa only [Subsingleton.elim i 0] using he
  · intro he
    exact congrArg (fun x => x.toAdd 0) he

/-- Every nonzero head point has orbit size seven in the actual ambient action. -/
theorem pointSubgroup_index (v : BinaryLinearThree.Vector) (hv : v ≠ 0) :
    (q.pointSubgroup h v).index = 7 := by
  classical
  let : MulAction J BinaryLinearThree.Vector := {
    smul := fun j w => BinaryLinearThree.W (q.ambientActor h j) w
    one_smul := by
      intro w
      change BinaryLinearThree.W (q.ambientActor h 1) w = w
      rw [map_one, map_one]
      rfl
    mul_smul := by
      intro a b w
      change BinaryLinearThree.W (q.ambientActor h (a * b)) w = _
      rw [map_mul, map_mul]
      rfl }
  have he : q.pointSubgroup h v = MulAction.stabilizer J v := rfl
  have ho : MulAction.orbit J v = ({0} : Set BinaryLinearThree.Vector)ᶜ := by
    ext w
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨j, rfl⟩
      change BinaryLinearThree.W (q.ambientActor h j) v ≠ 0
      intro hz
      apply hv
      have hh := congrArg (BinaryLinearThree.W (q.ambientActor h j)⁻¹) hz
      simpa only [BinaryLinearThree.W.inv_self_apply, map_zero] using hh
    · intro hw
      have hw0 : w ≠ 0 := hw
      obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three v w hv hw0
      obtain ⟨j,rfl⟩ := q.ambientActor_surjective h g
      exact ⟨j,hg⟩
  rw [he, MulAction.index_stabilizer, ho, Set.ncard_compl, Set.ncard_singleton]
  change Nat.card BinaryLinearThree.Vector - 1 = 7
  simp only [BinaryLinearThree.Vector, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  decide

/-- A two-subgroup lies in a literal point stabilizer of index seven. -/
theorem exists_pointSubgroup (S : Subgroup J) (hS : IsPGroup 2 S) :
    ∃ d : commutatorCore L, d ∉ coreFixed L ∧
      S ≤ q.pointSubgroup h ((q.projection d).toAdd 0) ∧
      (q.pointSubgroup h ((q.projection d).toAdd 0)).index = 7 := by
  let : MulAction S BinaryLinearThree.Vector := {
    smul := fun s w => BinaryLinearThree.W (q.ambientActor h s) w
    one_smul := by
      intro w
      change BinaryLinearThree.W (q.ambientActor h 1) w = w
      rw [map_one, map_one]
      rfl
    mul_smul := by
      intro a b w
      change BinaryLinearThree.W (q.ambientActor h ((a : J) * (b : J))) w = _
      rw [map_mul, map_mul]
      rfl }
  have hcard : 2 ∣ Nat.card BinaryLinearThree.Vector := by
    simp only [BinaryLinearThree.Vector, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    decide
  obtain ⟨v,hv,hv0⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := BinaryLinearThree.Vector) hcard (show (0 : BinaryLinearThree.Vector) ∈ MulAction.fixedPoints S _ from
      MulAction.mem_fixedPoints.mpr (fun _ => map_zero _))
  obtain ⟨d,hd⟩ := q.surjective (Multiplicative.ofAdd (fun _ => v))
  have hcoord : (q.projection d).toAdd 0 = v := congrArg (fun x => x.toAdd 0) hd
  refine ⟨d, ?_, ?_, ?_⟩
  · intro hc
    have hz := (q.oneProjection_kernel h (Additive.ofMul d)).mpr hc
    exact hv0 (hcoord ▸ hz.symm)
  · intro s hs
    change BinaryLinearThree.W (q.ambientActor h s) ((q.projection d).toAdd 0) = _
    rw [hcoord]
    exact MulAction.mem_fixedPoints.mp hv (⟨s,hs⟩ : S)
  · exact q.pointSubgroup_index h _ (hcoord ▸ Ne.symm hv0)

end AbelianCore.NaturalQuotient
end CFSG.Quasithin.ChapterC.BinaryMS
