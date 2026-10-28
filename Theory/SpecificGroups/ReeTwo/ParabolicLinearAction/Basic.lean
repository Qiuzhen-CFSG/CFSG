module

public import Theory.SpecificGroups.ReeTwo.ParabolicCoreStructure
public import Theory.SpecificGroups.ReeTwo.CoreMarkedCenter
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Basic
public import Mathlib.Algebra.Module.ZMod

/-!
# The marked binary action of the Ree local group

The five tail coordinates identify the actual derived subgroup of the core
with a binary vector space. Restricting core conjugation and transporting
through those coordinates gives a linear representation. Every core
automorphism fixes the last root, so the representation lands in its point
stabilizer. Its kernel is exactly the centralizer of the embedded derived
subgroup, and hence the induced representation of that quotient is faithful.

The coordinate embedding and its conjugation equation record the link with
the specified semidirect product; no ambient Ree or Tits identification is used.
Source: Aschbacher--Smith, Lemma 14.2.21, printed p.989, and Aschbacher,
*The Tits group as a standard subgroup* (1982), Section 3, using the verified
Shinoda root coordinates of `Core`.
-/

public section

open Subgroup
namespace ReeTwo.Centralizer
/-- The binary space with the ordered last five root coordinates. -/
abbrev DerivedSpace := Fin 5 → ZMod 2

/-- The restriction of actual core conjugation to its characteristic derived subgroup. -/
@[expose] def derivedAction : Centralizer →* MulAut (commutator Core) :=
  (MulAut.characteristic (commutator Core)).comp coreConjugation

/-- The same action in the multiplicative form of the published binary coordinates. -/
@[expose] def derivedCoordinateAction : Centralizer →* MulAut (Multiplicative DerivedSpace) :=
  (MulAut.congr Core.derivedCoordinates).toMonoidHom.comp derivedAction

set_option maxRecDepth 2048 in
private def derivedAddAction (g : Centralizer) : DerivedSpace ≃+ DerivedSpace where
  toFun v := (derivedCoordinateAction g (Multiplicative.ofAdd v)).toAdd
  invFun v := ((derivedCoordinateAction g).symm (Multiplicative.ofAdd v)).toAdd
  left_inv v := (derivedCoordinateAction g).symm_apply_apply v
  right_inv v := (derivedCoordinateAction g).apply_symm_apply v
  map_add' v w := (derivedCoordinateAction g).map_mul v w

/-- The actual conjugation representation on binary five-space. -/
def derivedLinearAction : Centralizer →* (DerivedSpace ≃ₗ[ZMod 2] DerivedSpace) where
  toFun g := (derivedAddAction g).toLinearEquiv (ZMod.map_smul (derivedAddAction g))
  map_one' := by ext v i; exact congrFun (congrArg Multiplicative.toAdd
    (DFunLike.congr_fun derivedCoordinateAction.map_one (Multiplicative.ofAdd v))) i
  map_mul' g h := by ext v i; exact congrFun (congrArg Multiplicative.toAdd
    (DFunLike.congr_fun (derivedCoordinateAction.map_mul g h) (Multiplicative.ofAdd v))) i

theorem derivedLinearAction_apply (g : Centralizer) (v : DerivedSpace) :
    derivedLinearAction g v = (Core.derivedCoordinates
      (derivedAction g (Core.derivedCoordinates.symm (Multiplicative.ofAdd v)))).toAdd := by rfl

theorem derivedLinearAction_coordinates (g : Centralizer) (x : commutator Core) :
    derivedLinearAction g (Core.derivedCoordinates x).toAdd =
      (Core.derivedCoordinates (derivedAction g x)).toAdd := by
  change (Core.derivedCoordinates (derivedAction g
    (Core.derivedCoordinates.symm (Core.derivedCoordinates x)))).toAdd = _
  rw [Core.derivedCoordinates.symm_apply_apply]

theorem derivedAction_val (g : Centralizer) (x : commutator Core) :
    (derivedAction g x : Core) = g.left * (g.right : MulAut Core) x * g.left⁻¹ := rfl

/-- The vector corresponding to the last root, which marks the fixed central line. -/
@[expose] def markedVector : DerivedSpace := ![0,0,0,0,1]

theorem markedVector_coordinates :
    markedVector = (Core.derivedCoordinates
      ⟨Core.root 9, Core.tail_root_mem_derived 4⟩).toAdd := rfl

theorem derivedSpace_finrank : Module.finrank (ZMod 2) DerivedSpace = 5 := by
  simp [DerivedSpace]

theorem markedVector_ne_zero : markedVector ≠ 0 := by
  intro h
  have := congrFun h 4
  exact (by decide : (1 : ZMod 2) ≠ 0) this

theorem derivedLinearAction_fixes_mark (g : Centralizer) :
    derivedLinearAction g markedVector = markedVector := by
  rw [markedVector_coordinates, derivedLinearAction_coordinates]
  congr 2
  apply Subtype.ext
  exact Core.aut_root_nine (coreConjugation g)

/-- The specified coordinates embedded in the whole local group. -/
@[expose] def derivedEmbedding : Multiplicative DerivedSpace →* Centralizer :=
  (SemidirectProduct.inl : Core →* Centralizer).comp
    ((commutator Core).subtype.comp Core.derivedCoordinates.symm.toMonoidHom)

theorem derivedEmbedding_injective : Function.Injective derivedEmbedding :=
  SemidirectProduct.inl_injective.comp (Subtype.val_injective.comp
    Core.derivedCoordinates.symm.injective)

theorem derivedEmbedding_range : derivedEmbedding.range = derived := by
  ext g
  constructor
  · rintro ⟨v, rfl⟩
    exact mem_map_of_mem _ (Core.derivedCoordinates.symm v).property
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Core.derivedCoordinates ⟨x,hx⟩, ?_⟩
    change SemidirectProduct.inl
      (Core.derivedCoordinates.symm (Core.derivedCoordinates ⟨x,hx⟩) : Core) = _
    rw [Core.derivedCoordinates.symm_apply_apply]

theorem derivedEmbedding_action (g : Centralizer) (v : DerivedSpace) :
    derivedEmbedding (Multiplicative.ofAdd (derivedLinearAction g v)) =
      g * derivedEmbedding (Multiplicative.ofAdd v) * g⁻¹ := by
  rw [derivedLinearAction_apply]
  change SemidirectProduct.inl (Core.derivedCoordinates.symm
    (Core.derivedCoordinates (derivedAction g
      (Core.derivedCoordinates.symm (Multiplicative.ofAdd v)))) : Core) = _
  rw [Core.derivedCoordinates.symm_apply_apply]
  exact inl_coreConjugation g _

theorem derivedEmbedding_mark :
    derivedEmbedding (Multiplicative.ofAdd markedVector) = root 9 := rfl

open Theory.LinearAlgebra.BinaryFivePointStabilizer

/-- The actual derived action, with codomain the stabilizer of its root mark. -/
@[expose] def markedRepresentation : Centralizer →* stabilizer markedVector :=
  derivedLinearAction.codRestrict (stabilizer markedVector) derivedLinearAction_fixes_mark

theorem markedRepresentation_ker :
    markedRepresentation.ker = centralizer (derived : Set Centralizer) := by
  ext g
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro hg y hy
    obtain ⟨x,hx,rfl⟩ := hy
    have hh := congrArg (fun a : stabilizer markedVector =>
      a.val (Core.derivedCoordinates ⟨x,hx⟩).toAdd) hg
    change derivedLinearAction g (Core.derivedCoordinates ⟨x,hx⟩).toAdd =
      (Core.derivedCoordinates ⟨x,hx⟩).toAdd at hh
    rw [derivedLinearAction_coordinates] at hh
    have hc : derivedAction g ⟨x,hx⟩ = ⟨x,hx⟩ :=
      Core.derivedCoordinates.injective hh
    have hval := congrArg (fun v : commutator Core =>
      (SemidirectProduct.inl (v : Core) : Centralizer)) hc
    change SemidirectProduct.inl (coreConjugation g x) = SemidirectProduct.inl x at hval
    rw [inl_coreConjugation] at hval
    exact ((mul_inv_eq_iff_eq_mul).mp hval).symm
  · intro hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨x,rfl⟩ := Core.derivedCoordinates.surjective (Multiplicative.ofAdd v)
    change derivedLinearAction g (Core.derivedCoordinates x).toAdd =
      (Core.derivedCoordinates x).toAdd
    rw [derivedLinearAction_coordinates]
    congr 2
    apply Subtype.ext
    apply SemidirectProduct.inl_injective (φ := Core.complement.subtype)
    change SemidirectProduct.inl (coreConjugation g x) = SemidirectProduct.inl (x : Core)
    rw [inl_coreConjugation]
    have hh := hg (SemidirectProduct.inl (x : Core)) (mem_map_of_mem _ x.property)
    rw [← hh, mul_inv_cancel_right]

theorem derivedCentralizer_le_core : centralizer (derived : Set Centralizer) ≤ core := by
  rw [centralizer_derived_eq_map]
  rintro _ ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

/-- The derived centralizer is normal in the local group because it is an action kernel. -/
instance derivedCentralizer_normal : (centralizer (derived : Set Centralizer)).Normal := by
  rw [← markedRepresentation_ker]
  infer_instance

/-- The faithful representation of the local group modulo the derived centralizer. -/
@[expose] def faithfulMarkedRepresentation :
    Centralizer ⧸ centralizer (derived : Set Centralizer) →* stabilizer markedVector :=
  QuotientGroup.lift _ markedRepresentation (le_of_eq markedRepresentation_ker.symm)

theorem faithfulMarkedRepresentation_mk (g : Centralizer) :
    faithfulMarkedRepresentation (QuotientGroup.mk' _ g) = markedRepresentation g := rfl

theorem faithfulMarkedRepresentation_injective :
    Function.Injective faithfulMarkedRepresentation := by
  exact (QuotientGroup.injective_lift_iff _ _ _).mpr markedRepresentation_ker.symm

end ReeTwo.Centralizer
