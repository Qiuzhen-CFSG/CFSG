module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.IncidentStructure.Core
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Extraspeciality of the actual incident flag radical

A central element commutes with every hyperplane shear, so it fixes the
hyperplane pointwise. Commutation with the line shears confines its remaining
displacement to the marked line. Evaluation therefore bounds the center by
two, and the p-group center theorem gives equality. Squares fix the hyperplane
and have image in the marked line, so the central quotient is elementary
abelian. The previously calculated order makes this quotient nontrivial.

All shears belong to the original subgroup of linear automorphisms. No
abstract model or assumed core structure enters the argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(6),
printed pp.99 and 103.
-/

@[expose] public section

open Subgroup BinaryLinear
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers
open BinaryNaturalDual.VectorStabilizers.PointCores
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer.IncidentStructure
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem add_self_binary (v : V) : v + v = 0 := by
  calc
    v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

private theorem fixes_line {x : V} {f : Module.Dual (ZMod 2) V}
    (g : incidentRadical x f) {v : V} (hv : v ∈ Submodule.span (ZMod 2) {x}) :
    g.val v = v := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, g.property.1.1]

private def hyperplaneShear {x : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 0) (w : f.ker) : incidentRadical x f :=
  ⟨(restrictionShear h w).val.val, (restrictionShear h w).val.property, by
    intro v hv
    change (v + f v • (w : V)) - v ∈ Submodule.span (ZMod 2) {x}
    simp [hv]⟩

private def lineShear {x : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 0) (a : Module.Dual (ZMod 2) V) (ha : a x = 0) :
    incidentRadical x f :=
  ⟨transvection x a ha, ⟨by change x + a x • x = x; simp [ha], by
    intro v
    change f (v + a v • x) = f v
    simp [h]⟩, by
      intro v _
      change (v + a v • x) - v ∈ Submodule.span (ZMod 2) {x}
      rw [add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)⟩

private theorem central_fixes_hyperplane {x t : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 0) (ht : f t = 1) (g : center (incidentRadical x f)) (w : f.ker) :
    g.val.val w = w := by
  have he := congrArg (fun k : incidentRadical x f => k.val t)
    (mem_center_iff.mp g.property (hyperplaneShear h w))
  change g.val.val t + f (g.val.val t) • (w : V) =
    g.val.val (t + f t • (w : V)) at he
  rw [g.val.property.1.2, ht, one_smul, map_add] at he
  exact (add_left_cancel he).symm

private theorem central_displacement_line {x : V} {f : Module.Dual (ZMod 2) V}
    (hx : x ≠ 0) (h : f x = 0) (g : center (incidentRadical x f)) (t : V) :
    g.val.val t - t ∈ Submodule.span (ZMod 2) {x} := by
  by_contra hout
  obtain ⟨a, ha, hax⟩ := (Submodule.span (ZMod 2) {x}).exists_le_ker_of_notMem hout
  have hax0 : a x = 0 := hax (Submodule.mem_span_singleton_self x)
  have he := congrArg (fun k : incidentRadical x f => k.val t)
    (mem_center_iff.mp g.property (lineShear h a hax0))
  change g.val.val t + a (g.val.val t) • x = g.val.val (t + a t • x) at he
  rw [map_add, map_smul, g.val.property.1.1] at he
  have he' := smul_left_injective (ZMod 2) hx (add_left_cancel he)
  exact ha (by rw [map_sub, he', sub_self])

private def centerEvaluation {x t : V} {f : Module.Dual (ZMod 2) V}
    (hx : x ≠ 0) (h : f x = 0) :
    center (incidentRadical x f) → Submodule.span (ZMod 2) {x} :=
  fun g => ⟨g.val.val t - t, central_displacement_line hx h g t⟩

private theorem centerEvaluation_injective {x t : V} {f : Module.Dual (ZMod 2) V}
    (hx : x ≠ 0) (h : f x = 0) (ht : f t = 1) :
    Function.Injective (centerEvaluation (t := t) hx h) := by
  intro g k he
  have he' : g.val.val t = k.val.val t :=
    sub_left_injective (congrArg Subtype.val he)
  apply Subtype.ext
  apply Subtype.ext
  ext v
  have hg := central_fixes_hyperplane h ht g (kernelProjection ht v)
  have hk := central_fixes_hyperplane h ht k (kernelProjection ht v)
  change g.val.val (v - f v • t) = v - f v • t at hg
  change k.val.val (v - f v • t) = v - f v • t at hk
  rw [map_sub, map_smul, he'] at hg
  rw [map_sub, map_smul] at hk
  exact sub_left_injective (hg.trans hk.symm)

private theorem neg_binary (v : V) : -v = v := by
  exact neg_eq_iff_add_eq_zero.mpr (add_self_binary v)

private theorem square_fixes_hyperplane {x : V} {f : Module.Dual (ZMod 2) V}
    (g : incidentRadical x f) (v : V) (hv : f v = 0) : g.val (g.val v) = v := by
  have he := fixes_line g (g.property.2 v hv)
  rw [map_sub] at he
  rw [sub_eq_iff_eq_add.mp he, sub_eq_add_neg, neg_binary, add_right_comm,
    add_self_binary, zero_add]

private theorem square_displacement_line {x : V} {f : Module.Dual (ZMod 2) V}
    (g : incidentRadical x f) (v : V) :
    g.val (g.val v) - v ∈ Submodule.span (ZMod 2) {x} := by
  have hf : f (g.val v - v) = 0 := by rw [map_sub, g.property.1.2, sub_self]
  have he := g.property.2 (g.val v - v) hf
  rw [map_sub] at he
  have heq : g.val (g.val v) - g.val v - (g.val v - v) =
      g.val (g.val v) - v := by
    calc
      _ = g.val (g.val v) - (g.val v + g.val v) + v := by abel
      _ = _ := by rw [add_self_binary, sub_zero, sub_eq_add_neg, neg_binary]
  rwa [heq] at he

private theorem central_of_displacement {x : V} {f : Module.Dual (ZMod 2) V}
    (g : incidentRadical x f)
    (hfix : ∀ v, f v = 0 → g.val v = v)
    (hline : ∀ v, g.val v - v ∈ Submodule.span (ZMod 2) {x}) :
    g ∈ center (incidentRadical x f) := by
  apply mem_center_iff.mpr
  intro k
  apply Subtype.ext
  ext v
  have hg := hfix (k.val v - v) (by rw [map_sub, k.property.1.2, sub_self])
  have hk := fixes_line k (hline v)
  rw [map_sub] at hg hk
  change k.val (g.val v) = g.val (k.val v)
  rw [sub_eq_iff_eq_add.mp hg, sub_eq_iff_eq_add.mp hk]
  abel

/-- A flag radical element has central square, by its two-step displacement. -/
theorem radical_square_mem_center {x : V} {f : Module.Dual (ZMod 2) V}
    (g : incidentRadical x f) : g ^ 2 ∈ center (incidentRadical x f) :=
  central_of_displacement (g ^ 2) (square_fixes_hyperplane g) (square_displacement_line g)

/-- The displacement flag radical is the literal image of the intrinsic core. -/
noncomputable def coreRadicalEquiv [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hf : f ≠ 0) (h : f x = 0) :
    pCore 2 (pairStabilizer x f) ≃* incidentRadical x f :=
  (MulEquiv.subgroupCongr (incident_core_eq_radical hf h)).trans
    (Subgroup.subgroupOfEquivOfLe (fun _ hg => hg.1))

/-- The order of the ambient radical agrees with that of the intrinsic core. -/
theorem incidentRadical_card [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hx : x ≠ 0) (hf : f ≠ 0) (h : f x = 0) :
    Nat.card (incidentRadical x f) = 2 ^ (1 + 2 * (Module.finrank (ZMod 2) V - 2)) := by
  rw [← Nat.card_congr (coreRadicalEquiv hf h).toEquiv]
  exact incident_core_card hx hf h

/-- The center of the actual incident radical is the binary marked line. -/
theorem radical_center_card [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hx : x ≠ 0) (hf : f ≠ 0) (h : f x = 0) :
    Nat.card (center (incidentRadical x f)) = 2 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective
    (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  have ht : ∃ t, f t ≠ 0 := by
    by_contra! ht
    exact hf (LinearMap.ext ht)
  obtain ⟨t, ht⟩ := ht
  have ht1 : f t = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ ht
  have hle := Nat.card_le_card_of_injective _ (centerEvaluation_injective hx h ht1)
  have hline : Nat.card (Submodule.span (ZMod 2) {x}) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_span_singleton hx,
      Nat.card_zmod, pow_one]
  rw [hline] at hle
  have hc := incidentRadical_card hx hf h
  have hp : IsPGroup 2 (incidentRadical x f) := IsPGroup.of_card hc
  have hgt : 1 < Nat.card (incidentRadical x f) := by
    rw [hc]
    exact Nat.one_lt_pow (by omega) (by decide)
  let : Nontrivial (incidentRadical x f) := Finite.one_lt_card_iff_nontrivial.mp hgt
  let : Nontrivial (center (incidentRadical x f)) := hp.center_nontrivial
  have := Finite.one_lt_card (α := center (incidentRadical x f))
  omega

/-- In dimension at least three the flag radical is extraspecial. -/
theorem radical_extraspecial [FiniteDimensional (ZMod 2) V]
    (hd : 3 ≤ Module.finrank (ZMod 2) V)
    {x : V} {f : Module.Dual (ZMod 2) V} (hx : x ≠ 0) (hf : f ≠ 0) (h : f x = 0) :
    IsExtraspecial 2 (incidentRadical x f) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective
    (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  have hpow (g : incidentRadical x f ⧸ center (incidentRadical x f)) : g ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center (incidentRadical x f)) g
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (g ^ 2)).mpr (radical_square_mem_center g)
  have hcenter := radical_center_card hx hf h
  refine ⟨hcenter, ?_, ?_⟩
  · exact {
      toIsMulCommutative := ⟨⟨fun a b =>
        (Commute.of_orderOf_dvd_two (fun c => orderOf_dvd_of_pow_eq_one (hpow c)) a b).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }
  · have hc := (center (incidentRadical x f)).card_mul_index
    change Nat.card (center (incidentRadical x f)) *
      Nat.card (incidentRadical x f ⧸ center (incidentRadical x f)) =
        Nat.card (incidentRadical x f) at hc
    rw [hcenter, incidentRadical_card hx hf h] at hc
    have hgt : 2 < 2 ^ (1 + 2 * (Module.finrank (ZMod 2) V - 2)) := by
      calc
        2 = 2 ^ 1 := rfl
        _ < _ := pow_lt_pow_right₀ (by decide) (by omega)
    apply Finite.one_lt_card_iff_nontrivial.mp
    omega

end CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer.IncidentStructure
