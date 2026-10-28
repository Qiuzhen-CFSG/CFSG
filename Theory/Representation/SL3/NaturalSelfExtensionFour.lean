module
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.Coordinates
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.Homogeneous
public import Theory.Representation.SpecialLinearFieldTransport
public import Mathlib.FieldTheory.Finite.GaloisField
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Splitting natural self-extensions over a four-element field

A binary representation with a natural submodule and natural quotient at the
same full SL₃ marking is a direct sum of those two natural modules. The
central cubic has no fixed vectors on either endpoint, hence none on the
extension. Its norm therefore vanishes on the whole extension, discharging
the central quadratic premise of the existing homogeneous block calculation.
A change of section then splits the action. Entrywise field transport returns
the actual equivalence over the supplied coefficient field and group marking.

This uses the intrinsic calculation from the local catalogue for James (1973),
Lemma 8.3, cited in Aschbacher–Smith H.12.1, pp.393–394. Its application to
the saturated central omega in C.1.34 is in NonbinarySource.OmegaSplitFour.
No equivariant complement or central polynomial is an extra hypothesis.
-/

public noncomputable section
open Representation
open scoped MatrixGroups
set_option backward.isDefEq.respectTransparency false
namespace Representation.SL3NaturalSelfExtensionFour
open SL3FourLocalCatalogue

private theorem block_central (c : BlockCocycle .natural .natural) : c.IsCentral := by
  have hf (v : W) (hv : constituent .natural z v = v) : v = 0 := by
    have hh : (SL3FourNaturalDual.omega - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← SL3FourNaturalDual.centralScalar_natural]
      exact sub_eq_zero.mpr hv
    exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (by decide +kernel))
  have hfix (v : W × W) (hv : c.representation z v = v) : v = 0 := by
    have hy := hf v.2 (congrArg Prod.snd hv)
    have hx := congrArg Prod.fst hv
    change constituent .natural z v.1 + c.value z v.2 = v.1 at hx
    rw [hy, map_zero, add_zero] at hx
    exact Prod.ext (hf v.1 hx) hy
  apply (c.centralQuadratic_iff).mp
  apply LinearMap.ext
  intro v
  change c.representation z (c.representation z v) + c.representation z v + v = 0
  apply hfix
  have hz : z ^ 3 = 1 := by decide +kernel
  have hp : c.representation z (c.representation z (c.representation z v)) = v := by
    have hh : (c.representation z)^3 = 1 := by rw [← map_pow, hz, map_one]
    have he := LinearMap.congr_fun hh v
    change ((c.representation z * c.representation z) * c.representation z) v = v at he
    exact he
  rw [map_add, map_add, hp]
  abel

private theorem concrete_split {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL V) (N : Subrepresentation ρ)
    (en : N.toRepresentation.Equiv (constituent .natural))
    (eq : N.quotientRepresentation.Equiv (constituent .natural)) :
    Nonempty (ρ.Equiv ((constituent .natural).prod (constituent .natural))) := by
  obtain ⟨c, ⟨a⟩⟩ := exists_block_equiv ρ N en eq
  let b := (c.shiftEquiv (c.value z)).trans
    (c.normalize.normalizedNaturalSplitEquiv (c.normalize_value_z (block_central c)))
  have hb := a.trans b
  rw [BlockCocycle.zero_representation] at hb
  exact ⟨hb⟩

private def fieldCoordinates {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (e : F ≃+* SL3FourLocalCatalogue.F) :
    (Fin 3 → F) ≃ₗ[ZMod 2] W where
  toFun v i := e (v i)
  invFun v i := e.symm (v i)
  left_inv v := funext (fun i => e.symm_apply_apply (v i))
  right_inv v := funext (fun i => e.apply_symm_apply (v i))
  map_add' v w := funext (fun i => e.map_add (v i) (w i))
  map_smul' c v := funext (fun i => ZMod.map_smul e.toAddMonoidHom c (v i))

private theorem fieldCoordinates_action {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (e : F ≃+* SL3FourLocalCatalogue.F) (g : SL(3,F)) (v : Fin 3 → F) :
    fieldCoordinates e (specialLinearNatural 3 g v) =
      constituent .natural (Atlas.fieldEquivSL 3 e g) (fieldCoordinates e v) :=
  SpecialLinearFieldTransport.natural_action 3 e g v

/-- Natural self-extensions over any four-element coefficient field split at
the supplied full special-linear marking. -/
theorem split {F X V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    [Group X] [AddCommGroup V] [Module (ZMod 2) V]
    (hF : Nat.card F = 4) (ρ : Representation (ZMod 2) X V)
    (e : X ≃* SL(3,F)) (N : Subrepresentation ρ)
    (en : N.toRepresentation.Equiv
      (((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)).comp e.toMonoidHom))
    (eq : N.quotientRepresentation.Equiv
      (((specialLinearNatural (k := F) 3).restrictScalars (k := ZMod 2)).comp e.toMonoidHom)) :
    Nonempty (ρ.Equiv
      ((((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)).restrictScalars
        (k := ZMod 2)).comp e.toMonoidHom)) := by
  let := Fintype.ofFinite F
  let f : F ≃+* SL3FourLocalCatalogue.F := FiniteField.ringEquivOfCardEq
    (by rw [Fintype.card_eq_nat_card, hF, ← SL2FourNatural.card_field])
  let a := e.trans (Atlas.fieldEquivSL 3 f)
  let σ := ρ.comp a.symm.toMonoidHom
  let M : Subrepresentation σ := ⟨N.toSubmodule, fun g _ hv =>
    N.apply_mem_toSubmodule (a.symm g) hv⟩
  let l := fieldCoordinates f
  have ha (g : SL) : Atlas.fieldEquivSL 3 f (e (a.symm g)) = g := a.apply_symm_apply g
  let mn : M.toRepresentation.Equiv (constituent .natural) := .mk
    (en.toLinearEquiv.trans l) (by
      intro g
      apply LinearMap.ext
      intro v
      change l (en (N.toRepresentation (a.symm g) v)) = _
      rw [show en (N.toRepresentation (a.symm g) v) =
          specialLinearNatural 3 (e (a.symm g)) (en v) from
        LinearMap.congr_fun (en.isIntertwining' (a.symm g)) v]
      exact (fieldCoordinates_action f _ _).trans (congrArg (fun t => constituent .natural t (l (en v))) (ha g)))
  let mq : M.quotientRepresentation.Equiv (constituent .natural) := .mk
    (eq.toLinearEquiv.trans l) (by
      intro g
      apply LinearMap.ext
      intro v
      change l (eq (N.quotientRepresentation (a.symm g) v)) = _
      rw [show eq (N.quotientRepresentation (a.symm g) v) =
          specialLinearNatural 3 (e (a.symm g)) (eq v) from
        LinearMap.congr_fun (eq.isIntertwining' (a.symm g)) v]
      exact (fieldCoordinates_action f _ _).trans (congrArg (fun t => constituent .natural t (l (eq v))) (ha g)))
  obtain ⟨b⟩ := concrete_split σ M mn mq
  refine ⟨.mk (b.toLinearEquiv.trans (l.symm.prodCongr l.symm)) ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  have hb := LinearMap.congr_fun (b.isIntertwining' (a g)) v
  change b (ρ (a.symm (a g)) v) =
    (constituent .natural (a g) (b v).1, constituent .natural (a g) (b v).2) at hb
  rw [a.symm_apply_apply] at hb
  change (l.symm (b (ρ g v)).1, l.symm (b (ρ g v)).2) = _
  rw [hb]
  apply Prod.ext
  all_goals
    apply l.injective
    rw [l.apply_symm_apply]
    exact ((fieldCoordinates_action f (e g) _).trans
      (congrArg (constituent .natural (a g)) (l.apply_symm_apply _))).symm

end Representation.SL3NaturalSelfExtensionFour
