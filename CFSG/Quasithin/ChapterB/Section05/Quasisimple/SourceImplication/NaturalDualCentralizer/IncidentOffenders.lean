module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.Reduction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Offender exclusion in the incident flag radical

Write C for the common natural fixed space, D for the common dual fixed
space, and M for the annihilator of D in the natural space. Every displacement
lies in M, and the natural-plus-dual fixed codimension is codim(C) + dim(M).

If C lies in H = ker(f), restriction displacement and evaluation outside H
embed the actor into Hom(H/C, span(x)) × M. The logarithm of its order is
therefore at most codim(C) - 1 + dim(M). Otherwise choose a fixed vector
outside H; every displacement then lies in span(x), embedding the actor
into Hom(V/C, span(x)). Nontriviality makes dim(M) positive in this case.
Thus both cases give a strict inequality, excluding all offenders without
using an offender catalogue or the radical's extraspecial structure.

The last theorem discharges the offender input of the published B.5.1(6)
reduction. Its independent extraspecial-core and quotient premise remains
explicit for the source theorem's assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(6),
printed pp.99 and 103; this direct argument replaces the appeal to the
B.4.9(2iii–iv) offender list on printed p.92.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer.IncidentOffenders
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private def naturalFixed (A : Subgroup (BinaryLinear.GL V)) : Submodule (ZMod 2) V where
  carrier := {v | ∀ g : A, g.val v = v}
  zero_mem' := by intro g; exact map_zero g.val
  add_mem' := by intro v w hv hw g; simp only [map_add, hv g, hw g]
  smul_mem' := by intro c v hv g; simp only [map_smul, hv g]

private def dualFixed (A : Subgroup (BinaryLinear.GL V)) :
    Submodule (ZMod 2) (Module.Dual (ZMod 2) V) where
  carrier := {ψ | ∀ g : A, ∀ v, ψ (g.val v) = ψ v}
  zero_mem' := by intro g v; rfl
  add_mem' := by intro ψ φ hψ hφ g v; simp only [LinearMap.add_apply, hψ g, hφ g]
  smul_mem' := by intro c ψ hψ g v; simp only [LinearMap.smul_apply, hψ g]

private theorem displacement_mem (A : Subgroup (BinaryLinear.GL V)) (g : A) (v : V) :
    g.val v - v ∈ (dualFixed A).dualCoannihilator := by
  rw [Submodule.mem_dualCoannihilator]
  intro ψ hψ
  rw [map_sub]
  exact sub_eq_zero.mpr (hψ g v)

private def fixedEquiv (A : Subgroup (BinaryLinear.GL V)) :
    fixedSpace naturalDualRepresentation A ≃ₗ[ZMod 2] naturalFixed A × dualFixed A where
  toFun v := (⟨v.val.1, by
    intro g
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply,
      naturalDualRepresentation_apply] using congrArg Prod.fst (v.property g)⟩,
    ⟨v.val.2, by
      intro g w
      have h := congrArg (fun u : BinaryNaturalDual.Space V => u.2 (g.val w)) (v.property g)
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply,
        naturalDualRepresentation_apply, LinearEquiv.dualMap_apply,
        LinearEquiv.symm_apply_apply] using h.symm⟩)
  invFun v := ⟨(v.1.val, v.2.val), by
    intro g
    change naturalDualRepresentation g.val (v.1.val, v.2.val) = _
    rw [naturalDualRepresentation_apply]
    apply Prod.ext
    · exact v.1.property g
    · apply LinearMap.ext
      intro w
      simpa only [LinearEquiv.dualMap_apply, LinearEquiv.apply_symm_apply] using
        (v.2.property g (g.val.symm w)).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem codim_formula [FiniteDimensional (ZMod 2) V]
    (A : Subgroup (BinaryLinear.GL V)) :
    fixedCodim naturalDualRepresentation A =
      Module.finrank (ZMod 2) (V ⧸ naturalFixed A) +
      Module.finrank (ZMod 2) (dualFixed A).dualCoannihilator := by
  have h := fixedCodim_add_finrank (naturalDualRepresentation (V := V)) A
  rw [(fixedEquiv A).finrank_eq, Module.finrank_prod] at h
  have hC := (naturalFixed A).finrank_quotient_add_finrank
  have hD := Subspace.finrank_add_finrank_dualCoannihilator_eq (dualFixed A)
  change _ = Module.finrank (ZMod 2) (V × Module.Dual (ZMod 2) V) at h
  rw [Module.finrank_prod, Subspace.dual_finrank_eq] at h
  omega

private theorem moved_pos [FiniteDimensional (ZMod 2) V]
    {A : Subgroup (BinaryLinear.GL V)} (hA : A ≠ ⊥) :
    0 < Module.finrank (ZMod 2) (dualFixed A).dualCoannihilator := by
  by_contra h
  have hz := Submodule.finrank_eq_zero.mp (show
    Module.finrank (ZMod 2) (dualFixed A).dualCoannihilator = 0 by omega)
  apply hA
  apply le_antisymm ?_ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply LinearEquiv.ext
  intro v
  have hd := displacement_mem A ⟨g, hg⟩ v
  rw [hz, Submodule.mem_bot] at hd
  exact sub_eq_zero.mp hd

private def restrictionParameter {x : V} {f : Module.Dual (ZMod 2) V}
    {A : Subgroup (BinaryLinear.GL V)} (hA : A ≤ PointCores.incidentRadical x f) (g : A) :
    (f.ker ⧸ (naturalFixed A).comap f.ker.subtype) →ₗ[ZMod 2]
      Submodule.span (ZMod 2) {x} :=
  ((naturalFixed A).comap f.ker.subtype).liftQ
    (((g.val.toLinearMap - LinearMap.id).comp f.ker.subtype).codRestrict
      (Submodule.span (ZMod 2) {x}) (fun v => (hA g.property).2 v v.property))
    (by
      intro v hv
      apply Subtype.ext
      exact sub_eq_zero.mpr (hv g))

private theorem parameters_injective {x t : V} {f : Module.Dual (ZMod 2) V}
    (ht : f t = 1) {A : Subgroup (BinaryLinear.GL V)}
    (hA : A ≤ PointCores.incidentRadical x f) :
    Function.Injective (fun g : A =>
      (restrictionParameter hA g,
        (⟨g.val t - t, displacement_mem A g t⟩ : (dualFixed A).dualCoannihilator))) := by
  intro g k he
  have ht' : g.val t = k.val t :=
    sub_left_injective (congrArg (fun p => (p.2 : V)) he)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  let w : f.ker := ⟨v - f v • t, by simp [ht]⟩
  have hw := congrArg (fun p => ((p.1
    (((naturalFixed A).comap f.ker.subtype).mkQ w)) : V)) he
  change g.val (v - f v • t) - (v - f v • t) =
    k.val (v - f v • t) - (v - f v • t) at hw
  have hw' := sub_left_injective hw
  simp only [map_sub, map_smul, ht'] at hw'
  exact sub_left_injective hw'

private theorem card_parameter_bound [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hx : x ≠ 0) (hf : f ≠ 0)
    {A : Subgroup (BinaryLinear.GL V)} (hA : A ≤ PointCores.incidentRadical x f) :
    Nat.card A ≤ 2 ^ (Module.finrank (ZMod 2) (f.ker ⧸
      (naturalFixed A).comap f.ker.subtype) +
      Module.finrank (ZMod 2) (dualFixed A).dualCoannihilator) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have ht : ∃ t, f t ≠ 0 := by
    by_contra! ht
    exact hf (LinearMap.ext ht)
  obtain ⟨t, ht⟩ := ht
  have ht1 : f t = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ ht
  let P := ((f.ker ⧸ (naturalFixed A).comap f.ker.subtype) →ₗ[ZMod 2]
    Submodule.span (ZMod 2) {x}) × (dualFixed A).dualCoannihilator
  let : Finite P := Module.finite_of_finite (ZMod 2)
  have hb := Nat.card_le_card_of_injective _ (parameters_injective ht1 hA)
  change Nat.card A ≤ Nat.card P at hb
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := P), Nat.card_zmod] at hb
  dsimp [P] at hb
  rw [Module.finrank_prod, Module.finrank_linearMap, finrank_span_singleton hx, mul_one] at hb
  exact hb

private theorem card_bound_of_fixed_outside [FiniteDimensional (ZMod 2) V]
    {x t : V} {f : Module.Dual (ZMod 2) V} (hx : x ≠ 0) (ht : f t = 1)
    {A : Subgroup (BinaryLinear.GL V)} (hA : A ≤ PointCores.incidentRadical x f)
    (htA : t ∈ naturalFixed A) :
    Nat.card A ≤ 2 ^ Module.finrank (ZMod 2) (V ⧸ naturalFixed A) := by
  have hd (g : A) (v : V) : g.val v - v ∈ Submodule.span (ZMod 2) {x} := by
    have h := (hA g.property).2 (v - f v • t) (by simp [ht])
    simpa only [map_sub, map_smul, htA g, sub_sub_sub_cancel_right] using h
  let P := (V ⧸ naturalFixed A) →ₗ[ZMod 2] Submodule.span (ZMod 2) {x}
  let δ : A → P := fun g => (naturalFixed A).liftQ
    ((g.val.toLinearMap - LinearMap.id).codRestrict _ (hd g))
    (by intro v hv; apply Subtype.ext; exact sub_eq_zero.mpr (hv g))
  have hi : Function.Injective δ := by
    intro g k he
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv := congrArg (fun l : P => (l ((naturalFixed A).mkQ v) : V)) he
    exact sub_left_injective hv
  let : Finite P := Module.finite_of_finite (ZMod 2)
  have hb := Nat.card_le_card_of_injective _ hi
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := P), Nat.card_zmod] at hb
  dsimp [P] at hb
  rwa [Module.finrank_linearMap, finrank_span_singleton hx, mul_one] at hb

private theorem rank_lt_codim [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hx : x ≠ 0) (hf : f ≠ 0)
    {A : Subgroup (BinaryLinear.GL V)} (hAb : A ≠ ⊥)
    (hA : A ≤ PointCores.incidentRadical x f) :
    rank A < fixedCodim naturalDualRepresentation A := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective
    (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  apply Nat.log_lt_of_lt_pow (Nat.card_pos.ne')
  by_cases hC : naturalFixed A ≤ f.ker
  · have hc := card_parameter_bound hx hf hA
    apply hc.trans_lt
    apply (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mpr
    have hW := (Submodule.comapSubtypeEquivOfLe hC).finrank_eq
    have hQ := ((naturalFixed A).comap f.ker.subtype).finrank_quotient_add_finrank
    have hH := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    have hN := (naturalFixed A).finrank_quotient_add_finrank
    rw [codim_formula]
    omega
  · obtain ⟨t, htA, ht⟩ := SetLike.not_le_iff_exists.mp hC
    have ht1 : f t = 1 :=
      (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ ht
    have hc := card_bound_of_fixed_outside hx ht1 hA htA
    apply hc.trans_lt
    apply (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mpr
    rw [codim_formula]
    exact Nat.lt_add_of_pos_right (moved_pos hAb)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer.IncidentOffenders

namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer

/-- No offender on the actual natural-plus-contragredient representation is
contained in the flag radical. The argument works in every finite dimension
and does not require the incidence assumption. -/
theorem incident_radical_no_offenders
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hx : x ≠ 0) (hf : f ≠ 0)
    (A : Subgroup (BinaryLinear.GL V))
    (hA : IsOffender naturalDualRepresentation A) :
    ¬ A ≤ PointCores.incidentRadical x f := by
  intro hle
  exact (Nat.not_lt_of_ge hA.2)
    (IncidentOffenders.rank_lt_codim hx hf hA.1.1 hle)

open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions

/-- B.5.1(6) with the radical offender exclusion discharged. Only the independent
calculation of the incident stabilizer's core and quotient remains explicit. -/
theorem sylowFixedCentralizer_of_incident_structure {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hc : ∀ (x : Space d) (f : Module.Dual (ZMod 2) (Space d)),
      x ≠ 0 → f ≠ 0 → f x = 0 →
      IsExtraspecial 2 (pCore 2 (pairStabilizer x f)) ∧
      Nat.card (pCore 2 (pairStabilizer x f)) = 2 ^ (1 + 2 * (d - 2)) ∧
      Nonempty ((pairStabilizer x f ⧸ pCore 2 (pairStabilizer x f)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin (d - 2)) (ZMod 2)))
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin d) (ZMod 2))) :
    Nonempty (SylowFixedCentralizer (slAction d) ⊤ d T) :=
  sylowFixedCentralizer_of_incident_calculations hd hc
    (fun _ _ hx hf _ A hA => incident_radical_no_offenders hx hf A hA) T

end CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer
