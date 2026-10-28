module

public import Theory.Representation.PSL3Two.NaturalDualAxisObstruction
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.Representation.BinaryGroupAction
public import Theory.ElementaryAbelian.Quotient

/-!
# Natural--dual transitivity obstruction

The natural--dual action of `SL₃(2)` preserves the two coordinate axes.  A
normal extension that realizes this action by conjugation therefore cannot be
transitive on all nonidentity elements of an elementary abelian group.  The
first theorem states this in coordinates; the second transports the statement
through the quotient and range maps used by the Chapter 12 local geometry.

Source: Aschbacher--Smith, Chapter 12 natural--dual marking; the coordinate
axis argument is the finite calculation in `NaturalDualAxisObstruction`.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace BinaryLinearThree.NaturalDual

theorem no_transitive_conjugation
    {P : Type*} [_root_.Group P]
    (U B : Subgroup P) [IsElementaryAbelian 2 U] [U.Normal] [B.Normal]
    (q : B →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (e : Additive U ≃ₗ[ZMod 2] Space)
    (he : ∀ b : B, ∀ v : U,
      e (Additive.ofMul (MulAut.conjNormal b.val v)) =
        action (q b) (e (Additive.ofMul v)))
    (htrans : ∀ x y : U, x ≠ 1 → y ≠ 1 →
      ∃ p : P, MulAut.conjNormal p x = y) : False := by
  let ρ := elementaryRepresentation (p := 2) (MulAut.conjNormal : P →* MulAut U)
  let η : Representation (ZMod 2) P Space := {
    toFun p := e.toLinearMap.comp ((ρ p).comp e.symm.toLinearMap)
    map_one' := by
      apply LinearMap.ext
      intro v
      change e (ρ 1 (e.symm v)) = v
      rw [map_one]
      exact e.apply_symm_apply v
    map_mul' p r := by
      apply LinearMap.ext
      intro v
      change e (ρ (p * r) (e.symm v)) =
        e (ρ p (e.symm (e (ρ r (e.symm v)))))
      rw [e.symm_apply_apply, map_mul]
      rfl }
  apply no_transitive_marked_normalizer η B q hq
  · intro b
    apply LinearMap.ext
    intro v
    change e (ρ b.val (e.symm v)) = action (q b) v
    rw [show ρ b.val (e.symm v) =
      Additive.ofMul (MulAut.conjNormal b.val (e.symm v).toMul) from rfl, he]
    exact congrArg (action (q b)) (e.apply_symm_apply v)
  · intro x y hx hy
    have hne (z : Space) (hz : z ≠ 0) : (e.symm z).toMul ≠ 1 := by
      intro hh
      apply hz
      have hz' : e.symm z = 0 := congrArg Additive.ofMul hh
      have := congrArg e hz'
      simpa only [e.apply_symm_apply, map_zero] using this
    obtain ⟨p, hp⟩ := htrans (e.symm x).toMul (e.symm y).toMul (hne x hx) (hne y hy)
    refine ⟨p, ?_⟩
    change e (Additive.ofMul (MulAut.conjNormal p (e.symm x).toMul)) = y
    rw [hp]
    exact e.apply_symm_apply y

private def linearize {U V : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : Multiplicative U ≃* Multiplicative V) : U ≃ₗ[ZMod 2] V :=
  let a : U ≃+ V := {
    toFun v := (e (Multiplicative.ofAdd v)).toAdd
    invFun v := (e.symm (Multiplicative.ofAdd v)).toAdd
    left_inv v := e.symm_apply_apply v
    right_inv v := e.apply_symm_apply v
    map_add' v w := congrArg Multiplicative.toAdd
      (e.map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  { a with map_smul' := ZMod.map_smul a }

theorem no_transitive_mapped_conjugation
    {R Q : Type*} [_root_.Group R] [_root_.Group Q]
    (f : R →* Q) (q : R →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (u : Multiplicative Space →* Q) (hu : Function.Injective u)
    (ha : ∀ r v, f r * u (Multiplicative.ofAdd v) * (f r)⁻¹ =
      u (Multiplicative.ofAdd (action (q r) v)))
    (P : Subgroup Q) (hfP : f.range ≤ P) (hEP : u.range ≤ P)
    (hB : (f.range.subgroupOf P).Normal) (hU : (u.range.subgroupOf P).Normal)
    (htrans : ∀ x y : u.range, x ≠ 1 → y ≠ 1 →
      ∃ p : P, p.val * x.val * p.val⁻¹ = y.val) : False := by
  let B := f.range.subgroupOf P
  let U := u.range.subgroupOf P
  let := hB
  let := hU
  let eB : B ≃* f.range := subgroupOfEquivOfLe hfP
  let eU : U ≃* u.range := subgroupOfEquivOfLe hEP
  let : IsElementaryAbelian 2 (Multiplicative Space) :=
    Representation.BinaryGroupAction.elementary
  let : IsElementaryAbelian 2 u.range := IsElementaryAbelian.of_surjective
    u.rangeRestrict u.rangeRestrict_surjective
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_surjective
    eU.symm.toMonoidHom eU.symm.surjective
  have hk : f.rangeRestrict.ker ≤ q.ker := by
    intro r hr
    have hfr : f r = 1 := congrArg Subtype.val hr
    apply action_injective
    apply LinearMap.ext
    intro v
    have hh := ha r v
    rw [hfr, one_mul, inv_one, mul_one] at hh
    have hh' := congrArg Multiplicative.toAdd (hu hh)
    change v = action (q r) v at hh'
    simpa only [map_one, Module.End.one_apply] using hh'.symm
  let qB : f.range →* BinaryLinearThree.Group :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨q, hk⟩
  have hqB : Function.Surjective qB := by
    intro g
    obtain ⟨r, rfl⟩ := hq g
    exact ⟨f.rangeRestrict r, by simp [qB]⟩
  let v : Multiplicative Space ≃* U := (MonoidHom.ofInjective hu).trans eU.symm
  let c := linearize ((MulEquiv.toMultiplicative_toAdditive :
    Multiplicative (Additive U) ≃* U).trans v.symm)
  apply no_transitive_conjugation U B (qB.comp eB.toMonoidHom)
    (hqB.comp eB.surjective) c
  · intro r x
    obtain ⟨s, hs⟩ := f.rangeRestrict_surjective (eB r)
    obtain ⟨w, rfl⟩ := v.surjective x
    have hqr : qB (eB r) = q s := by rw [← hs]; simp [qB]
    have hfr : f s = r.val.val := congrArg Subtype.val hs
    have hc (z : Multiplicative Space) : c (Additive.ofMul (v z)) = z.toAdd :=
      v.symm_apply_apply z
    have hact : MulAut.conjNormal r.val (v w) =
        v (Multiplicative.ofAdd (action (q s) w.toAdd)) := by
      apply Subtype.ext
      apply Subtype.ext
      change r.val.val * u w * r.val.val⁻¹ = _
      rw [← hfr]
      exact ha s w.toAdd
    rw [hact, hc, hc]
    change _ = action (qB (eB r)) w.toAdd
    rw [hqr]
    rfl
  · intro x y hx hy
    have hx' : eU x ≠ 1 := fun hh => hx (eU.injective (by simpa using hh))
    have hy' : eU y ≠ 1 := fun hh => hy (eU.injective (by simpa using hh))
    obtain ⟨p, hp⟩ := htrans (eU x) (eU y) hx' hy'
    refine ⟨p, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hp

end BinaryLinearThree.NaturalDual
