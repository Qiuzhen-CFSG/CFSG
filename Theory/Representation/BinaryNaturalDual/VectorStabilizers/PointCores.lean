module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Structure
public import Theory.GroupTheory.SylowKernelCore

/-!
# Two-cores of binary natural-plus-dual point stabilizers

The zero and pairing-one stabilizers have trivial two-core. At a nonzero pure
point, the two-core has order `2^(dim(V)-1)`; contragredience proves the same
statement for a pure covector.

For an incident pair, restriction to the hyperplane is onto its marked-vector
stabilizer. Its two-core therefore acts trivially on the middle flag section
`ker(f)/span(x)`. This puts the original two-core in the concrete flag radical,
defined here by displacement conditions on the actual linear action. Bounding
elementary subgroups of that radical is a separate calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the geometric
argument for B.5.1(6), printed p.103, used in 15.3.49 on printed p.1145.
-/

@[expose] public section

open Subgroup BinaryLinear
namespace BinaryNaturalDual.VectorStabilizers.PointCores
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem core_eq_bot_of_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : pCore 2 H = ⊥) : pCore 2 G = ⊥ := by
  apply (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
  rw [pCore_map_iso, h]

/-- The stabilizer of the zero pair is the whole linear group, with trivial core. -/
theorem zero_core [FiniteDimensional (ZMod 2) V] :
    (pairStabilizer (0 : V) 0).pCoreIn 2 = ⊥ := by
  have hp : pairStabilizer (0 : V) 0 = ⊤ := by
    ext g
    simp only [mem_pairStabilizer, map_zero, LinearMap.zero_apply, implies_true,
      and_self, mem_top]
  have hc : pCore 2 (pairStabilizer (0 : V) 0) = ⊥ :=
    core_eq_bot_of_equiv ((MulEquiv.subgroupCongr hp).trans Subgroup.topEquiv)
      SmallParabolicLevi.linearGroup_twoCore_eq_bot
  rw [pCoreIn, hc, Subgroup.map_bot]

/-- A pairing-one stabilizer is the full linear group of the complementary kernel. -/
theorem pairing_one_core [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (h : f x = 1) :
    (pairStabilizer x f).pCoreIn 2 = ⊥ := by
  have hc : pCore 2 (pairStabilizer x f) = ⊥ :=
    core_eq_bot_of_equiv (pairStabilizerEquivKernel h)
      SmallParabolicLevi.linearGroup_twoCore_eq_bot
  rw [pCoreIn, hc, Subgroup.map_bot]

/-- The pure-vector core is the elementary line radical. -/
theorem pure_vector_core_card [FiniteDimensional (ZMod 2) V]
    {x : V} (hx : x ≠ 0) :
    Nat.card ((pairStabilizer x 0).pCoreIn 2) =
      2 ^ (Module.finrank (ZMod 2) V - 1) := by
  rw [pCoreIn, card_map_of_injective (pairStabilizer x 0).subtype_injective,
    Pure.pairStabilizer_zero, Pure.point_twoCore, Pure.pointKernel_card hx]

/-- Contragradience sends a pure-covector stabilizer to its actual dual point stabilizer. -/
theorem pure_covector_stabilizer_map [FiniteDimensional (ZMod 2) V]
    (f : Module.Dual (ZMod 2) V) :
    (pairStabilizer 0 f).map Pure.dualGroupEquiv.toMonoidHom =
      Pure.pointStabilizer f := by
  ext k
  obtain ⟨g, rfl⟩ := (Pure.dualGroupEquiv (V := V)).surjective k
  rw [mem_map_equiv, MulEquiv.symm_apply_apply,
    mem_pairStabilizer_iff_action, naturalDualRepresentation_apply]
  change (g 0, g.symm.dualMap f) = (0, f) ↔ g.symm.dualMap f = f
  simp only [map_zero, Prod.mk.injEq, true_and]

/-- The pure-covector core has the same order as the pure-vector core. -/
theorem pure_covector_core_card [FiniteDimensional (ZMod 2) V]
    {f : Module.Dual (ZMod 2) V} (hf : f ≠ 0) :
    Nat.card ((pairStabilizer 0 f).pCoreIn 2) =
      2 ^ (Module.finrank (ZMod 2) V - 1) := by
  rw [← card_map_of_injective (K := (pairStabilizer 0 f).pCoreIn 2)
    (f := (Pure.dualGroupEquiv (V := V)).toMonoidHom)
    (Pure.dualGroupEquiv (V := V)).injective,
    map_pCoreIn_of_injective 2 _ _ (Pure.dualGroupEquiv (V := V)).injective,
    pure_covector_stabilizer_map, pCoreIn,
    card_map_of_injective (Pure.pointStabilizer f).subtype_injective,
    Pure.point_twoCore, Pure.pointKernel_card hf, Subspace.dual_finrank_eq]

/-- The flag-(1,n-1) radical: it fixes the marked pair, and is trivial on
    the middle section ker(f)/span(x). This definition retains the actual action. -/
def incidentRadical (x : V) (f : Module.Dual (ZMod 2) V) : Subgroup (BinaryLinear.GL V) where
  carrier := {g | g ∈ pairStabilizer x f ∧
    ∀ v, f v = 0 → g v - v ∈ Submodule.span (ZMod 2) {x}}
  one_mem' := ⟨(pairStabilizer x f).one_mem, by intro v _; simp⟩
  mul_mem' := by
    rintro g k ⟨hg, hdg⟩ ⟨hk, hdk⟩
    refine ⟨(pairStabilizer x f).mul_mem hg hk, ?_⟩
    intro v hv
    have he : (g * k) v - v = (g (k v) - k v) + (k v - v) := by
      change g (k v) - v = _
      abel
    rw [he]
    exact Submodule.add_mem _ (hdg (k v) ((hk.2 v).trans hv)) (hdk v hv)
  inv_mem' := by
    rintro g ⟨hg, hdg⟩
    have hi := (pairStabilizer x f).inv_mem hg
    refine ⟨hi, ?_⟩
    intro v hv
    have h := hdg (g.symm v) ((hi.2 v).trans hv)
    rw [g.apply_symm_apply] at h
    change g.symm v - v ∈ Submodule.span (ZMod 2) {x}
    simpa only [neg_sub] using Submodule.neg_mem (Submodule.span (ZMod 2) {x}) h

@[simp] theorem mem_incidentRadical (x : V) (f : Module.Dual (ZMod 2) V) (g : BinaryLinear.GL V) :
    g ∈ incidentRadical x f ↔ g ∈ pairStabilizer x f ∧
      ∀ v, f v = 0 → g v - v ∈ Submodule.span (ZMod 2) {x} := Iff.rfl

/-- Restriction to the hyperplane, retaining its marked vector. -/
def incidentRestriction {x : V} {f : Module.Dual (ZMod 2) V} (h : f x = 0) :
    pairStabilizer x f →* Pure.pointStabilizer (⟨x, h⟩ : f.ker) where
  toFun g := ⟨kernelAction x f g, Subtype.ext g.property.1⟩
  map_one' := Subtype.ext (kernelAction x f).map_one
  map_mul' g k := Subtype.ext ((kernelAction x f).map_mul g k)

@[simp] theorem incidentRestriction_apply {x : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 0) (g : pairStabilizer x f) (v : f.ker) :
    ((incidentRestriction h g).val v : V) = g.val v := rfl

/-- Every hyperplane automorphism fixing x extends across a complement of ker(f). -/
theorem incidentRestriction_surjective {x : V} {f : Module.Dual (ZMod 2) V}
    (hf : f ≠ 0) (h : f x = 0) : Function.Surjective (incidentRestriction h) := by
  have ht : ∃ t, f t ≠ 0 := by
    by_contra! ht
    exact hf (LinearMap.ext ht)
  obtain ⟨t, ht⟩ := ht
  have ht1 : f t = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ ht
  intro k
  have hg : extendKernel ht1 k.val ∈ pairStabilizer x f := by
    refine ⟨?_, (extendKernel_mem ht1 k.val).2⟩
    rw [extendKernel_apply, h, zero_smul, zero_add]
    have hp : kernelProjection ht1 x = (⟨x, h⟩ : f.ker) := by
      apply Subtype.ext
      simp [h]
    rw [hp]
    exact congrArg Subtype.val k.property
  refine ⟨⟨extendKernel ht1 k.val, hg⟩, ?_⟩
  apply Subtype.ext
  ext v
  change f v • t + (k.val (kernelProjection ht1 v) : V) = k.val v
  have hp : kernelProjection ht1 v = v := by
    apply Subtype.ext
    simp [show f v = 0 from v.property]
  simp [show f v = 0 from v.property, hp]

/-- The intrinsic point two-core acts trivially on the middle flag section.
    No identification with a two-core in an outer automorphism group is used. -/
theorem incident_core_le [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hf : f ≠ 0) (h : f x = 0) :
    (pairStabilizer x f).pCoreIn 2 ≤ incidentRadical x f := by
  have hc : (pCore 2 (pairStabilizer x f)).map (incidentRestriction h) ≤
      pCore 2 (Pure.pointStabilizer (⟨x, h⟩ : f.ker)) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ (incidentRestriction_surjective hf h),
      pCore_isPGroup.map _⟩
  rw [Pure.point_twoCore] at hc
  rintro g ⟨a, ha, rfl⟩
  refine ⟨a.property, ?_⟩
  intro v hv
  have hd := (Theory.LinearAlgebra.BinaryFivePointStabilizer.mem_kernel_iff
    (⟨x, h⟩ : f.ker) (incidentRestriction h a)).mp (hc ⟨a, ha, rfl⟩) ⟨v, hv⟩
  obtain ⟨c, he⟩ := Submodule.mem_span_singleton.mp hd
  exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val he⟩
end BinaryNaturalDual.VectorStabilizers.PointCores
