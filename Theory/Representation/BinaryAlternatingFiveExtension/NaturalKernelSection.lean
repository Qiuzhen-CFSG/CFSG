module
public import Theory.Representation.BinaryAlternatingFiveExtension.FaithfulExtension
public import Theory.ElementaryAbelian.Basic

/-!
# From an ambient natural subspace to a literal symmetric-five kernel

An injective linear marking of the binary five-point augmentation module
inside an elementary abelian ambient subgroup gives a faithful natural
kernel whenever its ambient range is exactly the kernel of the prescribed
symmetric-five epimorphism. We construct the kernel equivalence with its
literal coordinates, transport conjugation, and apply the existing
faithful-kernel extension theorem. No splitting or involution lift is an
input.

This is the natural-kernel transport used for the factor centralizers in
Aschbacher–Smith 10.2.1, pp.742–743.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace BinaryPermutation.AlternatingFiveExtension
local notation "S5" => Equiv.Perm (Fin 5)
variable {G : Type*} [Group G]

/-- The multiplicative ambient map represented by a natural linear marking. -/
@[expose] def ambientNaturalMap (U : Subgroup G) [IsElementaryAbelian 2 U]
    (s : core (Fin 5) →ₗ[ZMod 2] Additive U) : V →* G where
  toFun v := ((s v.toAdd).toMul : G)
  map_one' := by
    change ((s 0).toMul : G) = 1
    rw [map_zero]
    rfl
  map_mul' v w := by
    change ((s (v.toAdd + w.toAdd)).toMul : G) =
      ((s v.toAdd).toMul : G) * ((s w.toAdd).toMul : G)
    rw [map_add]
    rfl

theorem ambientNaturalMap_injective (U : Subgroup G) [IsElementaryAbelian 2 U]
    (s : core (Fin 5) →ₗ[ZMod 2] Additive U) (hs : Function.Injective s) :
    Function.Injective (ambientNaturalMap U s) := by
  intro v w h
  apply Multiplicative.toAdd.injective
  apply hs
  exact Additive.toMul.injective (Subtype.ext h)

/-- The literal kernel equivalence records the given ambient coordinates
and the conjugation action through the prescribed quotient map. -/
theorem exists_kernel_equiv_of_natural_range
    (U P : Subgroup G) [IsElementaryAbelian 2 U]
    (q : P →* S5) (s : core (Fin 5) →ₗ[ZMod 2] Additive U)
    (hs : Function.Injective s)
    (hk : q.ker.map P.subtype = (ambientNaturalMap U s).range)
    (he : ∀ (g : P) (v : core (Fin 5)),
      ((s (coreRepresentation (Fin 5) (q g) v)).toMul : G) =
        (g : G) * ((s v).toMul : G) * (g : G)⁻¹) :
    ∃ e : q.ker ≃* V,
      (∀ v : q.ker, ambientNaturalMap U s (e v) = ((v : P) : G)) ∧
      (∀ (g : P) (v : q.ker), e (MulAut.conjNormal g v) = coreAction (q g) (e v)) := by
  let i := ambientNaturalMap U s
  have hi : Function.Injective i := ambientNaturalMap_injective U s hs
  let ek := q.ker.equivMapOfInjective P.subtype P.subtype_injective
  let ei := MonoidHom.ofInjective hi
  let e : q.ker ≃* V := ek.trans ((MulEquiv.subgroupCongr hk).trans ei.symm)
  have hcoord (v : q.ker) : i (e v) = ((v : P) : G) := by
    exact MonoidHom.apply_ofInjective_symm hi ((MulEquiv.subgroupCongr hk) (ek v))
  refine ⟨e,hcoord,?_⟩
  intro g v
  apply hi
  calc
    i (e (MulAut.conjNormal g v)) = (((MulAut.conjNormal g v) : P) : G) := hcoord _
    _ = (g : G) * i (e v) * (g : G)⁻¹ := by rw [hcoord]; rfl
    _ = i (coreAction (q g) (e v)) := (he g (e v).toAdd).symm

variable [Finite G]

/-- An exact natural subspace kernel supplies a section of the original
symmetric-five epimorphism. -/
theorem exists_section_of_natural_range
    (U P : Subgroup G) [IsElementaryAbelian 2 U]
    (q : P →* S5) (hq : Function.Surjective q)
    (s : core (Fin 5) →ₗ[ZMod 2] Additive U) (hs : Function.Injective s)
    (hk : q.ker.map P.subtype = (ambientNaturalMap U s).range)
    (he : ∀ (g : P) (v : core (Fin 5)),
      ((s (coreRepresentation (Fin 5) (q g) v)).toMul : G) =
        (g : G) * ((s v).toMul : G) * (g : G)⁻¹) :
    ∃ σ : S5 →* P, q.comp σ = MonoidHom.id _ := by
  obtain ⟨e,_,heq⟩ := exists_kernel_equiv_of_natural_range U P q s hs hk he
  exact exists_section_of_faithful_kernel q hq e heq

/-- The resulting affine model preserves both the actual quotient and
the original ambient coordinates of every natural vector. -/
theorem exists_marked_symmetric_equiv_of_natural_range
    (U P : Subgroup G) [IsElementaryAbelian 2 U]
    (q : P →* S5) (hq : Function.Surjective q)
    (s : core (Fin 5) →ₗ[ZMod 2] Additive U) (hs : Function.Injective s)
    (hk : q.ker.map P.subtype = (ambientNaturalMap U s).range)
    (he : ∀ (g : P) (v : core (Fin 5)),
      ((s (coreRepresentation (Fin 5) (q g) v)).toMul : G) =
        (g : G) * ((s v).toMul : G) * (g : G)⁻¹) :
    ∃ E : P ≃* V ⋊[coreAction] S5,
      (∀ g : P, (E g).right = q g) ∧
      (∀ v : V, (E.symm (SemidirectProduct.inl v) : G) = ambientNaturalMap U s v) := by
  obtain ⟨e,hcoord,heq⟩ := exists_kernel_equiv_of_natural_range U P q s hs hk he
  obtain ⟨E,hEq,hEe⟩ := exists_marked_symmetric_equiv q hq e heq
  refine ⟨E,hEq,?_⟩
  intro v
  have hh := hEe (e.symm v)
  rw [e.apply_symm_apply] at hh
  have hh' := congrArg (fun x => (E.symm x : G)) hh
  rw [E.symm_apply_apply] at hh'
  rw [←hh',←hcoord,e.apply_symm_apply]

end BinaryPermutation.AlternatingFiveExtension
