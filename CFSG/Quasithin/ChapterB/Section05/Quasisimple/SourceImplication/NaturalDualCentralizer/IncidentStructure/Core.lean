module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.PointCores
public import Theory.GroupTheory.PCoreSurjective

/-!
# The core and quotient of the incident-pair stabilizer

Restriction to the hyperplane has its additive space as kernel. The known
point-stabilizer core on that hyperplane therefore lifts to the two-core of
the incident-pair stabilizer. The resulting core is exactly the subgroup
acting trivially on the middle flag section; counting the two restriction
kernels gives its order. The middle action identifies the quotient with the
actual binary projective special linear group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(6),
printed pp.99 and 103. Extraspeciality is established separately.
-/

@[expose] public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers
open BinaryNaturalDual.VectorStabilizers.PointCores
open Theory.LinearAlgebra
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer.IncidentStructure
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem restriction_ker_iff {x : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 0) (g : pairStabilizer x f) :
    g ∈ (incidentRestriction h).ker ↔ ∀ v : f.ker, g.val v = v := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro he v
    exact congrArg (fun k : Pure.pointStabilizer (⟨x, h⟩ : f.ker) => (k.val v : V)) he
  · intro he
    apply Subtype.ext
    ext v
    exact he v

/-- The hyperplane shear, as an element of the actual restriction kernel. -/
def restrictionShear {x : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 0) (w : f.ker) : (incidentRestriction h).ker :=
  ⟨⟨transvection w.val f w.property, by
    constructor
    · change x + f x • w.val = x
      simp [h]
    · intro v
      change f (v + f v • w.val) = f v
      simp [show f w.val = 0 from w.property]⟩, by
    apply (restriction_ker_iff h _).mpr
    intro v
    change (v : V) + f v • w.val = v
    simp [show f v = 0 from v.property]⟩

/-- Evaluation at a vector paired to one identifies the kernel with the additive hyperplane. -/
def restrictionKernelEquiv {x t : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 0) (ht : f t = 1) : (incidentRestriction h).ker ≃* Multiplicative f.ker where
  toFun g := Multiplicative.ofAdd ⟨g.val.val t - t, by
    change f (g.val.val t - t) = 0
    rw [map_sub, g.val.property.2, sub_self]⟩
  invFun w := restrictionShear h (Multiplicative.toAdd w)
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    ext v
    have he := (restriction_ker_iff h g.val).mp g.property (kernelProjection ht v)
    change g.val.val (v - f v • t) = v - f v • t at he
    rw [map_sub, map_smul] at he
    change v + f v • (g.val.val t - t) = g.val.val v
    rw [smul_sub]
    rw [sub_eq_iff_eq_add.mp he]
    abel
  right_inv w := by
    apply Subtype.ext
    change t + f t • ((Multiplicative.toAdd w : f.ker) : V) - t = _
    simp only [ht, one_smul, add_sub_cancel_left]
    rfl
  map_mul' g k := by
    apply Subtype.ext
    change g.val.val (k.val.val t) - t = (g.val.val t - t) + (k.val.val t - t)
    have he := (restriction_ker_iff h g.val).mp g.property
      ⟨k.val.val t - t, by
        change f (k.val.val t - t) = 0
        rw [map_sub, k.val.property.2, sub_self]⟩
    change g.val.val (k.val.val t - t) = k.val.val t - t at he
    rw [map_sub] at he
    rw [sub_eq_iff_eq_add.mp he]
    abel

/-- The restriction kernel has the order of its hyperplane. -/
theorem restriction_kernel_card [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hf : f ≠ 0) (h : f x = 0) :
    Nat.card (incidentRestriction h).ker = 2 ^ Module.finrank (ZMod 2) f.ker := by
  have ht : ∃ t, f t ≠ 0 := by
    by_contra! ht
    exact hf (LinearMap.ext ht)
  obtain ⟨t, ht⟩ := ht
  have ht1 : f t = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ ht
  rw [Nat.card_congr (restrictionKernelEquiv h ht1).toEquiv]
  change Nat.card f.ker = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- The literal action on the middle section of the incident flag. -/
def middleAction {x : V} {f : Module.Dual (ZMod 2) V} (h : f x = 0) :
    pairStabilizer x f →* BinaryLinear.GL (Pure.pointQuotient (⟨x, h⟩ : f.ker)) :=
  (Pure.pointQuotientAction (⟨x, h⟩ : f.ker)).comp (incidentRestriction h)

/-- Every automorphism of the middle section lifts to the pair stabilizer. -/
theorem middleAction_surjective {x : V} {f : Module.Dual (ZMod 2) V}
    (hf : f ≠ 0) (h : f x = 0) : Function.Surjective (middleAction h) :=
  (BinaryFivePointStabilizer.quotientAction_surjective _).comp
    (incidentRestriction_surjective hf h)

/-- The middle action has precisely the intrinsic two-core as kernel. -/
theorem middleAction_ker [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hf : f ≠ 0) (h : f x = 0) :
    (middleAction h).ker = pCore 2 (pairStabilizer x f) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective
    (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  let : Finite (BinaryLinear.GL f.ker) := Finite.of_injective
    (fun g : BinaryLinear.GL f.ker => (g : f.ker → f.ker)) DFunLike.coe_injective
  have hk : IsPGroup 2 (incidentRestriction h).ker :=
    IsPGroup.of_card (restriction_kernel_card hf h)
  change (Pure.pointKernel (⟨x, h⟩ : f.ker)).comap (incidentRestriction h) = _
  rw [← Pure.point_twoCore]
  exact (incidentRestriction h).comap_pCore_of_ker_isPGroup
    (incidentRestriction_surjective hf h) hk

/-- The middle action kernel is the displacement-defined flag radical. -/
theorem middleAction_ker_eq_radical {x : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 0) :
    (middleAction h).ker = (incidentRadical x f).subgroupOf (pairStabilizer x f) := by
  ext g
  change incidentRestriction h g ∈ Pure.pointKernel (⟨x, h⟩ : f.ker) ↔ _
  rw [BinaryFivePointStabilizer.mem_kernel_iff]
  constructor
  · intro hg
    refine ⟨g.property, ?_⟩
    intro v hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hg ⟨v, hv⟩)
    exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
  · intro hg v
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hg.2 v v.property)
    exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext hc⟩

/-- The two-core equals the actual radical inside the pair stabilizer. -/
theorem incident_core_eq_radical [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hf : f ≠ 0) (h : f x = 0) :
    pCore 2 (pairStabilizer x f) =
      (incidentRadical x f).subgroupOf (pairStabilizer x f) :=
  (middleAction_ker hf h).symm.trans (middleAction_ker_eq_radical h)

/-- The two successive elementary restriction kernels give the core order. -/
theorem incident_core_card [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hx : x ≠ 0) (hf : f ≠ 0) (h : f x = 0) :
    Nat.card (pCore 2 (pairStabilizer x f)) =
      2 ^ (1 + 2 * (Module.finrank (ZMod 2) V - 2)) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective
    (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  let : Finite (BinaryLinear.GL f.ker) := Finite.of_injective
    (fun g : BinaryLinear.GL f.ker => (g : f.ker → f.ker)) DFunLike.coe_injective
  have hx' : (⟨x, h⟩ : f.ker) ≠ 0 := fun he => hx (congrArg Subtype.val he)
  rw [(incidentRestriction h).card_pCore_of_ker_isPGroup
    (incidentRestriction_surjective hf h) (IsPGroup.of_card (restriction_kernel_card hf h)),
    restriction_kernel_card hf h, Pure.point_twoCore, Pure.pointKernel_card hx', ← pow_add]
  congr 1
  have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hl := Submodule.finrank_le (Submodule.span (ZMod 2) {(⟨x, h⟩ : f.ker)})
  rw [finrank_span_singleton hx'] at hl
  omega

/-- Linear coordinates on the actual middle flag section. -/
noncomputable def middleCoordinates {d : ℕ}
    {x : OuterCyclic.Space d} {f : Module.Dual (ZMod 2) (OuterCyclic.Space d)}
    (hx : x ≠ 0) (hf : f ≠ 0) (h : f x = 0) :
    Pure.pointQuotient (⟨x, h⟩ : f.ker) ≃ₗ[ZMod 2] OuterCyclic.Space (d - 2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    have hx' : (⟨x, h⟩ : f.ker) ≠ 0 := fun he => hx (congrArg Subtype.val he)
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    have hl := (Submodule.span (ZMod 2) {(⟨x, h⟩ : f.ker)}).finrank_quotient_add_finrank
    rw [finrank_span_singleton hx'] at hl
    have hdV : Module.finrank (ZMod 2) (OuterCyclic.Space d) = d := by
      simp [OuterCyclic.Space]
    rw [hdV] at hh
    have hdW : Module.finrank (ZMod 2) (OuterCyclic.Space (d - 2)) = d - 2 := by
      simp [OuterCyclic.Space]
    rw [hdW]
    change Module.finrank (ZMod 2) (Pure.pointQuotient (⟨x, h⟩ : f.ker)) + 1 = _ at hl
    omega)

/-- The core quotient is the binary projective special linear group via its middle action. -/
noncomputable def incidentQuotientEquiv {d : ℕ} (hd : 2 < d)
    {x : OuterCyclic.Space d} {f : Module.Dual (ZMod 2) (OuterCyclic.Space d)}
    (hx : x ≠ 0) (hf : f ≠ 0) (h : f x = 0) :
    (pairStabilizer x f ⧸ pCore 2 (pairStabilizer x f)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (d - 2)) (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (middleAction_ker hf h).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (middleAction h)
      (middleAction_surjective hf h)).trans
      ((Pure.linearGroupCongr (middleCoordinates hx hf h)).trans
        (projectiveEquivLinear (by omega : 0 < d - 2)).symm))

end CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer.IncidentStructure
