module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Exhaustion.Geometry
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The normal subgroup in the full special-unitary lift

Normality is taken inside the projective subgroup `M`. Its inverse image is
therefore normal inside the full SU lift, and its image in GL is normalized
by that lift. A nontrivial projective subgroup gives a nonscalar matrix
subgroup. If the projective subgroup is abelian, commutators in its inverse
image are scalar matrices of cube one; the inverse image need not be abelian.

These are the lifting conventions for the first part of the proof of
Hartley–Mitchell, GLS3, Theorem 6.5.3, `refs/KGroup/GLS3/chapter6.tex`.
The representation-theoretic steps are separate from these lift identities.
-/

open Matrix BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source.Unitary
open scoped IsMulCommutative

namespace CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion.PrimitiveAbelian

variable {F : Type} [Field F] (J : HermitianForm 3 F)
  (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))

/-- Projection from the full SU inverse image onto the projective subgroup. -/
@[expose] public def liftProjection : specialLift J M →* M :=
  (suProjection J).subgroupComap M

public theorem liftProjection_surjective : Function.Surjective (liftProjection J M) :=
  (suProjection J).subgroupComap_surjective_of_surjective M (suProjection_surjective J)

/-- The faithful matrix inclusion of the full SU lift. -/
@[expose] public def liftToGL : specialLift J M →* GL (Fin 3) F :=
  J.specialSubgroup.subtype.comp (specialLift J M).subtype

public theorem liftToGL_injective : Function.Injective (liftToGL J M) :=
  J.specialSubgroup.subtype_injective.comp (specialLift J M).subtype_injective

/-- The natural representation on the original coefficient-field space. -/
@[expose] public noncomputable def liftRepresentation :
    Representation F (specialLift J M) (Fin 3 → F) :=
  (Representation.generalLinearNatural 3).comp (liftToGL J M)

public theorem liftRepresentation_injective :
    Function.Injective (liftRepresentation J M) :=
  (Representation.generalLinearNatural_injective 3).comp (liftToGL_injective J M)

/-- The geometric irreducibility condition is irreducibility of the actual
natural representation, over `F` rather than its algebraic closure. -/
public theorem liftRepresentation_irreducible (hM : ¬ IsReducible J M) :
    Representation.IsIrreducible (liftRepresentation J M) := by
  refine ⟨fun W => ?_⟩
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  by_contra htop
  apply hM
  refine ⟨W.toSubmodule, ?_, ?_, ?_⟩
  · exact fun h => hW (Subrepresentation.toSubmodule_injective h)
  · exact fun h => htop (Subrepresentation.toSubmodule_injective h)
  · intro g v hv
    exact W.apply_mem_toSubmodule g hv

/-- Inverse image of a subgroup normal inside `M`, not in ambient PSU. -/
@[expose] public def normalLift (A : Subgroup M) : Subgroup (specialLift J M) :=
  A.comap (liftProjection J M)

public instance normalLift_normal (A : Subgroup M) [A.Normal] :
    (normalLift J M A).Normal := Subgroup.Normal.comap inferInstance _

/-- Its actual faithful matrix image. -/
@[expose] public def normalLiftMatrix (A : Subgroup M) : Subgroup (GL (Fin 3) F) :=
  (normalLift J M A).map (liftToGL J M)

/-- Projection of the inverse image onto `A`. -/
@[expose] public def normalLiftProjection (A : Subgroup M) : normalLift J M A →* A :=
  (liftProjection J M).subgroupComap A

public theorem normalLiftProjection_surjective (A : Subgroup M) :
    Function.Surjective (normalLiftProjection J M A) :=
  (liftProjection J M).subgroupComap_surjective_of_surjective A
    (liftProjection_surjective J M)

public theorem normalLiftMatrix_normalized (A : Subgroup M) [A.Normal] :
    (liftToGL J M).range ≤ Subgroup.normalizer (normalLiftMatrix J M A : Set (GL (Fin 3) F)) := by
  have h := (normalLift J M A).le_normalizer_map (liftToGL J M)
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, normalLiftMatrix] using h

/-- Nontriviality in PSU rules out the scalar representation branch. -/
public theorem normalLiftMatrix_not_le_center (A : Subgroup M) (hA : A ≠ ⊥) :
    ¬ normalLiftMatrix J M A ≤ Subgroup.center (GL (Fin 3) F) := by
  intro h
  apply hA
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨x, hx⟩ := normalLiftProjection_surjective J M A ⟨a, ha⟩
  have hc := h (Subgroup.mem_map_of_mem (liftToGL J M) x.property)
  have hk : suProjection J x.val.val = 1 := (mem_suProjection_ker J _).mpr hc
  have he : liftProjection J M x.val = 1 := Subtype.ext hk
  have hp := congrArg (fun z : A => (z : M)) hx
  exact Subgroup.mem_bot.mpr (hp.symm.trans he)

/-- Every scalar in SU₃ has cube one by its determinant condition. -/
public theorem suProjection_kernel_cube (x : J.specialSubgroup)
    (hx : x ∈ (suProjection J).ker) : x ^ 3 = 1 := by
  have hc := (mem_suProjection_ker J x).mp hx
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨a, ha⟩ := hc
  have hd := (J.mem_specialSubgroup_iff (x : GL (Fin 3) F)).mp x.property |>.2
  rw [← ha] at hd
  have ha3 : a ^ 3 = 1 := by
    apply Units.ext
    have h := congrArg (fun a : Fˣ => (a : F)) hd
    simpa [GeneralLinearGroup.det, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_fin_three, pow_succ, pow_two] using h
  apply Subtype.ext
  change (x.val ^ 3 : GL (Fin 3) F) = 1
  rw [← ha, ← map_pow, ha3, map_one]

/-- The derived subgroup of an abelian projective inverse image is central. -/
public theorem normalLift_commutator_le_center (A : Subgroup M) [IsMulCommutative A] :
    commutator (normalLift J M A) ≤ Subgroup.center (normalLift J M A) := by
  let : CommGroup A := { A.toGroup with mul_comm := mul_comm' }
  intro x hx
  have hk := Abelianization.commutator_subset_ker (normalLiftProjection J M A) hx
  have hk' : suProjection J x.val.val = 1 :=
    congrArg (fun a : A => ((a : M) : ProjectiveSpecialUnitaryMatrixGroup J)) hk
  have hc := suProjection_ker_central J hk'
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  apply Subtype.ext
  apply Subtype.ext
  exact hc y.val.val

/-- Every element of that derived subgroup has cube one. -/
public theorem normalLift_commutator_cube (A : Subgroup M) [IsMulCommutative A]
    (x : normalLift J M A) (hx : x ∈ commutator (normalLift J M A)) : x ^ 3 = 1 := by
  let : CommGroup A := { A.toGroup with mul_comm := mul_comm' }
  have hk := Abelianization.commutator_subset_ker (normalLiftProjection J M A) hx
  have hk' : suProjection J x.val.val = 1 :=
    congrArg (fun a : A => ((a : M) : ProjectiveSpecialUnitaryMatrixGroup J)) hk
  apply Subtype.ext
  apply Subtype.ext
  exact suProjection_kernel_cube J x.val.val hk'

/-- Solvability descends along the genuine SU-to-PSU projection. -/
public theorem solvable_of_lift [Group.IsSolvable (specialLift J M)] :
    Group.IsSolvable M :=
  Group.isSolvable_of_surjective (liftProjection_surjective J M)

end CFSG.Quasithin.MainConverse.UnitaryThreeSections.Exhaustion.PrimitiveAbelian
