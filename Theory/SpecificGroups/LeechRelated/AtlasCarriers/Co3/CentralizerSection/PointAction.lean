module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.Seed
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The actual 36-point quotient of a Co₃ centralizing subgroup

Restrict the numerator's defining permutation action to the fixed points of its
involution, enumerated explicitly. Its image is exactly the subgroup generated
by the three checked degree-36 tables. Thus the range restriction is a genuine
surjection with relatively normal kernel, without a splitting assumption.
Identification of this permutation group with the binary symplectic matrix
group is a separate mathematical comparison.

Source: GLS3 Table 5.3j and Aschbacher--Smith A.2.19, printed pp.40--41.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Co3.CentralizerSection

abbrev FixedPoint := {x : Fin 276 // inclusion involution x = x}

def fixedPointsEquiv : Fin 36 ≃ FixedPoint where
  toFun i := ⟨Tables.fixedPoint i, by
    rw [inclusion_involution]
    exact Tables.fixedPoint_fixed i⟩
  invFun x := Tables.fixedIndex x.val
  left_inv := Tables.fixedIndex_left
  right_inv x := Subtype.ext (Tables.fixedIndex_right x.val (by
    rw [← inclusion_involution]
    exact x.property))

private theorem preserves_fixed (g : numerator) (x : FixedPoint) :
    inclusion involution (inclusion g.val x.val) = inclusion g.val x.val := by
  have hc := congrArg inclusion
    (Subgroup.mem_centralizer_singleton_iff.mp (numerator_centralizes g.property))
  simp only [map_mul] at hc
  have hx := Equiv.congr_fun hc x.val
  simpa only [Equiv.Perm.mul_apply, x.property] using hx.symm

/-- Restriction to the literal fixed letters of the involution. -/
def fixedAction : numerator →* Equiv.Perm FixedPoint where
  toFun g :=
    { toFun := fun x => ⟨inclusion g.val x.val, by exact preserves_fixed g x⟩
      invFun := fun x => ⟨inclusion (g⁻¹).val x.val, by exact preserves_fixed g⁻¹ x⟩
      left_inv := fun x => Subtype.ext (by
        change inclusion (g.val⁻¹) (inclusion g.val x.val) = x.val
        rw [map_inv]
        exact Equiv.symm_apply_apply _ _)
      right_inv := fun x => Subtype.ext (by
        change inclusion g.val (inclusion (g.val⁻¹) x.val) = x.val
        rw [map_inv]
        exact Equiv.apply_symm_apply _ _) }
  map_one' := by ext x; rfl
  map_mul' := fun _ _ => by ext x; rfl

/-- The same action with its fixed enumeration by `Fin 36`. -/
def pointAction : numerator →* Equiv.Perm (Fin 36) :=
  fixedPointsEquiv.symm.permCongrHom.toMonoidHom.comp fixedAction

theorem pointAction_agrees (g : numerator) (i : Fin 36) :
    Tables.fixedPoint (pointAction g i) = inclusion g.val (Tables.fixedPoint i) := by
  exact congrArg Subtype.val (fixedPointsEquiv.apply_symm_apply
    (fixedAction g (fixedPointsEquiv i)))

theorem pointAction_generator (i : Fin 3) :
    pointAction (numeratorGenerator i) = Tables.pointGenerator i := by
  apply Equiv.ext
  intro j
  apply fixedPointsEquiv.injective
  apply Subtype.ext
  change Tables.fixedPoint (pointAction (numeratorGenerator i) j) =
    Tables.fixedPoint (Tables.pointGenerator i j)
  rw [pointAction_agrees]
  change inclusion (generator i) (Tables.fixedPoint j) = _
  rw [inclusion_generator]
  exact Tables.pointGenerator_agrees i j

/-- The explicit permutation quotient whose classical comparison is still needed. -/
def pointGroup : Subgroup (Equiv.Perm (Fin 36)) :=
  Subgroup.closure (Set.range Tables.pointGenerator)

private theorem numerator_generated :
    Subgroup.closure (Set.range numeratorGenerator) = ⊤ := by
  have hs : Set.range numeratorGenerator =
      ((↑) : numerator → Carrier) ⁻¹' Set.range generator := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  rw [hs]
  exact Subgroup.closure_closure_coe_preimage

theorem pointAction_range : pointAction.range = pointGroup := by
  rw [MonoidHom.range_eq_map, ← numerator_generated, MonoidHom.map_closure, ← Set.range_comp]
  exact congrArg (fun f => Subgroup.closure (Set.range f)) (funext pointAction_generator)

private theorem pointAction_mem (g : numerator) : pointAction g ∈ pointGroup := by
  rw [← pointAction_range]
  exact ⟨g, rfl⟩

/-- The actual surjection onto the generated permutation group. -/
def pointQuotient : numerator →* pointGroup :=
  pointAction.codRestrict pointGroup (by exact pointAction_mem)

theorem pointQuotient_surjective : Function.Surjective pointQuotient := by
  intro x
  have hx : x.val ∈ pointAction.range := by
    rw [pointAction_range]
    exact x.property
  obtain ⟨g, hg⟩ := hx
  exact ⟨g, Subtype.ext hg⟩

end Sporadic.LeechRelated.Co3.CentralizerSection
