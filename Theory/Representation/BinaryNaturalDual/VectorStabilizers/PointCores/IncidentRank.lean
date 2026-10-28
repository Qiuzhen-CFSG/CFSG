module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.PointCores
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.PointCores.IncidentRank.Geometry

/-!
# Abelian subgroups of the binary incident flag radical

For an abelian subgroup A, let W be its common fixed subspace in H = ker(f).
Restriction displacement embeds its image in Hom(H/W, span(x)). The kernel
of restriction embeds, by evaluation at a vector t with f(t) = 1, into W:
this is exactly where commutativity is used. Multiplying the two cardinal
bounds gives |A| ≤ |W| · |Hom(H/W, span(x))| = |H|, hence eight in dimension four.
All displacements use the actual linear operators in `incidentRadical`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), geometric
argument for B.5.1(6), printed p.103; application in 15.3.49, printed p.1145,
with the rank-four offender in B.4.9(2iii), printed p.92.
-/

@[expose] public section

open Subgroup BinaryLinear
namespace BinaryNaturalDual.VectorStabilizers.PointCores
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private def fixedHyperplane (f : Module.Dual (ZMod 2) V)
    (A : Subgroup (BinaryLinear.GL V)) : Submodule (ZMod 2) f.ker where
  carrier := {v | ∀ g : A, g.val v = v}
  zero_mem' := by intro g; exact map_zero g.val
  add_mem' := by intro v w hv hw g; simp only [Submodule.coe_add, map_add, hv g, hw g]
  smul_mem' := by intro c v hv g; simp only [Submodule.coe_smul, map_smul, hv g]

private theorem fixes_line {x : V} {f : Module.Dual (ZMod 2) V}
    {g : BinaryLinear.GL V} (hg : g ∈ incidentRadical x f)
    {v : V} (hv : v ∈ Submodule.span (ZMod 2) {x}) : g v = v := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, hg.1.1]

private def displacement {x : V} {f : Module.Dual (ZMod 2) V}
    {A : Subgroup (BinaryLinear.GL V)} (hA : A ≤ incidentRadical x f) (g : A) :
    f.ker →ₗ[ZMod 2] Submodule.span (ZMod 2) {x} :=
  (((g.val.toLinearMap - LinearMap.id).comp f.ker.subtype).codRestrict
    (Submodule.span (ZMod 2) {x}) (fun v => (hA g.property).2 v v.property))

private def restrictionDisplacement {x : V} {f : Module.Dual (ZMod 2) V}
    {A : Subgroup (BinaryLinear.GL V)} (hA : A ≤ incidentRadical x f) :
    A →* Multiplicative ((f.ker ⧸ fixedHyperplane f A) →ₗ[ZMod 2]
      Submodule.span (ZMod 2) {x}) where
  toFun g := Multiplicative.ofAdd ((fixedHyperplane f A).liftQ (displacement hA g)
    (by
      intro v hv
      apply Subtype.ext
      exact sub_eq_zero.mpr (hv g)))
  map_one' := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v => apply Subtype.ext; exact sub_self _
  map_mul' g k := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v =>
      apply Subtype.ext
      change g.val (k.val v) - v = (g.val v - v) + (k.val v - v)
      have he := fixes_line (hA g.property) ((hA k.property).2 v v.property)
      rw [map_sub] at he
      rw [sub_eq_iff_eq_add.mp he]
      abel

private theorem restrictionDisplacement_ker {x : V} {f : Module.Dual (ZMod 2) V}
    {A : Subgroup (BinaryLinear.GL V)} (hA : A ≤ incidentRadical x f)
    (g : (restrictionDisplacement hA).ker) (v : f.ker) : g.val.val v = v := by
  have he := congrArg (fun q : Multiplicative ((f.ker ⧸ fixedHyperplane f A) →ₗ[ZMod 2]
    Submodule.span (ZMod 2) {x}) => ((Multiplicative.toAdd q)
      ((fixedHyperplane f A).mkQ v) : V)) g.property
  exact sub_eq_zero.mp he

private def kernelEvaluation {x t : V} {f : Module.Dual (ZMod 2) V}
    {A : Subgroup (BinaryLinear.GL V)} (hA : A ≤ incidentRadical x f)
    (hcomm : ∀ g k : A, g * k = k * g) :
    (restrictionDisplacement hA).ker → fixedHyperplane f A := fun k =>
  ⟨⟨k.val.val t - t, by
    change f (k.val.val t - t) = 0
    rw [map_sub, (hA k.val.property).1.2 t, sub_self]⟩, by
      intro g
      have hg : f (g.val t - t) = 0 := by
        rw [map_sub, (hA g.property).1.2 t, sub_self]
      have he := restrictionDisplacement_ker hA k ⟨g.val t - t, hg⟩
      have hc : k.val.val (g.val t) = g.val (k.val.val t) :=
        congrArg (fun a : A => a.val t) (hcomm k.val g)
      change g.val (k.val.val t - t) = k.val.val t - t
      rw [map_sub]
      change k.val.val (g.val t - t) = g.val t - t at he
      rw [map_sub, hc] at he
      have := sub_eq_iff_eq_add.mp he
      rw [this]
      abel⟩

private theorem kernelEvaluation_injective {x t : V} {f : Module.Dual (ZMod 2) V}
    (ht : f t = 1) {A : Subgroup (BinaryLinear.GL V)}
    (hA : A ≤ incidentRadical x f) (hcomm : ∀ g k : A, g * k = k * g) :
    Function.Injective (kernelEvaluation (t := t) hA hcomm) := by
  intro g k he
  have ht' : g.val.val t = k.val.val t := by
    have := congrArg (fun w : fixedHyperplane f A => (w.val : V)) he
    exact sub_left_injective this
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hg := restrictionDisplacement_ker hA g (kernelProjection ht v)
  have hk := restrictionDisplacement_ker hA k (kernelProjection ht v)
  change g.val.val (v - f v • t) = v - f v • t at hg
  change k.val.val (v - f v • t) = v - f v • t at hk
  rw [map_sub, map_smul] at hg hk
  rw [ht'] at hg
  exact sub_left_injective (hg.trans hk.symm)

/-- An abelian subgroup of the actual flag radical has order at most the hyperplane.
The bound also holds without the incidence assumption. -/
theorem incidentRadical_abelian_card_le [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hx : x ≠ 0) (hf : f ≠ 0)
    (A : Subgroup (BinaryLinear.GL V)) (hA : A ≤ incidentRadical x f)
    (hcomm : ∀ g k : A, g * k = k * g) : Nat.card A ≤ Nat.card f.ker := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective
    (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  let W := fixedHyperplane f A
  let L := Submodule.span (ZMod 2) {x}
  let D := (f.ker ⧸ W) →ₗ[ZMod 2] L
  let : Finite D := Module.finite_of_finite (ZMod 2)
  let ρ := restrictionDisplacement hA
  have ht : ∃ t, f t ≠ 0 := by
    by_contra! ht
    exact hf (LinearMap.ext ht)
  obtain ⟨t, ht⟩ := ht
  have ht1 : f t = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ ht
  have hk : Nat.card ρ.ker ≤ Nat.card W :=
    Nat.card_le_card_of_injective _ (kernelEvaluation_injective ht1 hA hcomm)
  have hr : Nat.card ρ.range ≤ Nat.card D :=
    Nat.card_le_card_of_injective _ ρ.range.subtype_injective
  calc
    Nat.card A = Nat.card ρ.ker * Nat.card ρ.range := by
      rw [← ρ.ker.card_mul_index, Subgroup.index_ker]
    _ ≤ Nat.card W * Nat.card D := Nat.mul_le_mul hk hr
    _ = Nat.card f.ker := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D),
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := f.ker)]
      dsimp [D, L]
      rw [Module.finrank_linearMap, finrank_span_singleton hx, mul_one, ← pow_add,
        add_comm, Submodule.finrank_quotient_add_finrank]

open scoped IsMulCommutative

/-- In a binary four-space, every abelian subgroup of the flag radical has order at most eight. -/
theorem incidentRadical_abelian_card_le_eight
    {x : Fin 4 → ZMod 2} {f : Module.Dual (ZMod 2) (Fin 4 → ZMod 2)}
    (hx : x ≠ 0) (hf : f ≠ 0) (A : Subgroup (BinaryLinear.GL (Fin 4 → ZMod 2)))
    (hA : A ≤ incidentRadical x f) (hcomm : ∀ g k : A, g * k = k * g) :
    Nat.card A ≤ 8 := by
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  rw [Module.finrank_pi, Fintype.card_fin] at hd
  have hd3 : Module.finrank (ZMod 2) f.ker = 3 := by omega
  have hc : Nat.card f.ker = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd3, Nat.card_zmod]
    norm_num
  exact (incidentRadical_abelian_card_le hx hf A hA hcomm).trans hc.le

/-- The elementary-subgroup bound for the concrete binary flag-(1,3) radical. -/
theorem incidentRadical_elementary_card_le_eight
    {x : Fin 4 → ZMod 2} {f : Module.Dual (ZMod 2) (Fin 4 → ZMod 2)}
    (hx : x ≠ 0) (hf : f ≠ 0) (A : Subgroup (BinaryLinear.GL (Fin 4 → ZMod 2)))
    (hA : A ≤ incidentRadical x f) [IsElementaryAbelian 2 A] : Nat.card A ≤ 8 :=
  incidentRadical_abelian_card_le_eight hx hf A hA (fun g k => mul_comm g k)

end BinaryNaturalDual.VectorStabilizers.PointCores
