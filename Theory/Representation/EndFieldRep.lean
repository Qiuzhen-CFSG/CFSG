module

public import Mathlib.RingTheory.LittleWedderburn
public import Theory.Representation.AbsolutelyIrreducible

@[expose] public section

namespace Representation

open _root_.Representation
open Representation
open MonoidAlgebra
open Module
open Module.End

open scoped MonoidAlgebra

/-!
# Representation on Endomorphism Field

Let `G` be a group, `F` be a finite field,
and `M` be an finite dimensional irreducible `F[G]`-module.
Denote `End_{F[G]}(M)` by `K`, we prove that `K` is a finite field.

Meanwhile, we can regard `M` as an absolutely irreducible `K[G]`-module,
by natrual action by endomorphisms.
This representation is called the **endFieldRep** of `M`.

Note that the endFieldRep is a representation over `ρ.asModule` but not `V`,
since `V` has no natrual `F[G]`-module structure.
Also this representation does not rely on the finiteness of `F` and `V`,
though `K` is not a field in general without the finiteness assumptions,
and the definition of irreducibility requires the field structure.
-/

section EndFieldModule


/-- We build the `K[G]`-module instance on `ρ.asModule`.-/
noncomputable instance endFieldModule
    {F G V : Type*} [Field F] [Monoid G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    : Module (_root_.Module.End F[G] ρ.asModule) ρ.asModule :=
  {
    smul := fun k m ↦ k m
    mul_smul := fun _ _ _ ↦ rfl
    one_smul := fun _ ↦ rfl
    smul_zero := fun a ↦ map_zero a
    smul_add := fun a x y ↦ map_add a x y
    add_smul := fun _ _ _ ↦ rfl
    zero_smul := fun _ ↦ rfl
  }

@[simp]
theorem endFieldModule_smul_apply
    {F G V : Type*} [Field F] [Monoid G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (k : _root_.Module.End F[G] ρ.asModule) (m : ρ.asModule)
    : (k • m) = k m :=
  rfl

end EndFieldModule

section EndField

-- We work on a finite field `F` and a finite dimensional vector space`V`.

/-- We build the finite field instance over the endomorphism field `K = End_{F[G]}(ρ.asModule)`.-/
instance endField_finite
    {F G V : Type*} [Field F] [Finite F] [Monoid G] [AddCommGroup V]
    [Module F V] [iFD : FiniteDimensional F V] (ρ : Representation F G V) :
    Finite (_root_.Module.End F[G] ρ.asModule) :=
  letI : Module F ρ.asModule := Representation.instModuleAsModule ρ
  letI : Finite V := Module.finite_iff_finite.mp iFD
  let : Finite ρ.asModule := Finite.of_injective ρ.asModuleEquiv ρ.asModuleEquiv.injective
  let : Finite (ρ.asModule → ρ.asModule) := Pi.finite
  Finite.of_injective _ fun _ _ h ↦ by ext; exact congrFun h _

set_option backward.isDefEq.respectTransparency false in
noncomputable instance endField_field
    {F G V : Type*} [Field F] [Finite F] [Monoid G] [AddCommGroup V]
    [Module F V] [iFD : FiniteDimensional F V] (ρ : Representation F G V)
    [iIr : IsIrreducible ρ] : Field (_root_.Module.End F[G] ρ.asModule) := by
  classical
  let : IsSimpleModule F[G] ρ.asModule := (irreducible_iff_isSimpleModule_asModule ρ).mp iIr
  exact littleWedderburn _

end EndField

section EndFieldRep


set_option backward.isDefEq.respectTransparency false in
/-- The endomorphism field representation inherited from the original representation `ρ`.-/
def endFieldRep
    {F G V : Type*} [Field F] [Monoid G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) :
    Representation (_root_.Module.End F[G] ρ.asModule) G ρ.asModule :=
  {
    toFun :=
      fun g ↦
        {
          toFun m := ρ.asModuleEquiv.symm (ρ g (ρ.asModuleEquiv m))
          map_add' x y := by simp
          map_smul' x m := by rw [asModuleEquiv_symm_map_rho, asModuleEquiv_symm_map_rho,
            endFieldModule_smul_apply, endFieldModule_smul_apply, map_smul]; rfl
        }
    map_one' := by simp only [map_one, Module.End.one_apply]; rfl
    map_mul' g h := by simp only [map_mul, Module.End.mul_apply]; rfl
  }

@[simp]
theorem endFieldRep_apply {F G V : Type*} [Field F] [Monoid G] [AddCommGroup V]
    [Module F V] (ρ : Representation F G V) (g : G) (m : ρ.asModule)
    : (endFieldRep ρ) g m = ρ.asModuleEquiv.symm (ρ g (ρ.asModuleEquiv m)) :=
  rfl

theorem endFieldRep_apply' {F G V : Type*} [Field F] [Monoid G] [AddCommGroup V]
    [Module F V] (ρ : Representation F G V) (g : G) (m : ρ.asModule)
    : ρ.asModuleEquiv ((endFieldRep ρ) g m) = (ρ g (ρ.asModuleEquiv m)) :=
  rfl

end EndFieldRep

section EndFieldRepIrr

-- We need field structure.

set_option backward.isDefEq.respectTransparency false in
instance endFieldRep_AddHomClass
    {F G V : Type*} [Field F] [Finite F] [Monoid G] [AddCommGroup V]
    [Module F V] [iFD : FiniteDimensional F V] (ρ : Representation F G V)
    [iIr : IsIrreducible ρ]
    : AddHomClass (Representation.End (endFieldRep ρ)) ρ.asModule ρ.asModule where
  map_add f x y := RepMap.map_add f x y

set_option backward.isDefEq.respectTransparency false in
instance endFieldRep_mulActionHomClass
    {F G V : Type*} [Field F] [Finite F] [Monoid G] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (ρ : Representation F G V)
    [IsIrreducible ρ]
    : MulActionHomClass (Representation.End (endFieldRep ρ)) F[G] ρ.asModule
        ρ.asModule where
  map_smulₛₗ f x m := by
    apply MonoidAlgebra.induction_linear
      (motive := fun x ↦ f (x • m) = x • f m) x
    · rw [zero_smul, zero_smul, RepMap.map_zero]
    · intro _ _ a b
      rw [add_smul, map_add, a, b, add_smul]
    · intro g r
      trans f (r • (ρ.asModuleEquiv.symm ((ρ g) (ρ.asModuleEquiv m)))); simp
      have (m : ρ.asModule) : r • m = (r • (1 : _root_.Module.End F[G] ρ.asModule)) • m := rfl
      rw [this, RepMap.map_smul, ← endFieldRep_apply, f.isIntertwining]
      simp

set_option backward.isDefEq.respectTransparency false in
theorem endFieldRep_isIrreducible
    {F G V : Type*} [Field F] [Finite F] [Monoid G] [AddCommGroup V]
    [Module F V] [iFD : FiniteDimensional F V] (ρ : Representation F G V)
    [iIr : IsIrreducible ρ] : IsIrreducible (endFieldRep ρ) :=
  {
    toNontrivial :=
      let : Nontrivial ρ.asModule := Subrepresentation.irreducible_module_nontrivial ρ
      inferInstance
    eq_bot_or_eq_top r := by
      let r' : Subrepresentation ρ := {
        toSubmodule := {
          carrier := r.toSubmodule.carrier
          add_mem' a b := r.toSubmodule.add_mem' a b
          zero_mem' := r.toSubmodule.zero_mem'
          smul_mem' f m h := r.toSubmodule.smul_mem' (f • 1) h
        }
        apply_mem_toSubmodule g m h := r.apply_mem_toSubmodule g h
      }
      obtain h | h := iIr.eq_bot_or_eq_top r' <;>
      simp only [SetLike.ext'_iff, show (r : Set ρ.asModule) = (r' : Set V) by rfl, h] <;>
      tauto
  }

set_option backward.isDefEq.respectTransparency false in
/-- The endomorphism field representation is absolutely irreducible.-/
theorem endFieldRep_isAbsolutelyIrreducible
    {F G V : Type*} [Field F] [Finite F] [Monoid G] [AddCommGroup V]
    [Module F V] [iFD : FiniteDimensional F V] (ρ : Representation F G V)
    [iIr : IsIrreducible ρ] : IsAbsolutelyIrreducible (endFieldRep ρ) :=
  let : IsIrreducible (endFieldRep ρ) := endFieldRep_isIrreducible _
  let : Finite ρ.asModule := Module.finite_iff_finite.mp iFD
  (isAbsolutelyIrreducible_iff_surjective _).mpr
    fun f ↦
      ⟨
        {
          toFun := f
          map_add' x y := RepMap.map_add f x y
          map_smul' x m := by rw [map_smul, RingHom.id_apply]
        },
        rfl
      ⟩

end EndFieldRepIrr

end Representation
