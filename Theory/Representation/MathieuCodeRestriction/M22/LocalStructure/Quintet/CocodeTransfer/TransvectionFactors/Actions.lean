module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Linear
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.Quotients
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Inputs
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.Parity

/-!
# Faithful full transvections on the native quintet middle space

Displacements in the sextet tetrad line survive the quotient by the disjoint
pair line. Thus the earlier M24 faithful action descends faithfully. The H.14
order of the actual quintet kernel and the radical cardinal bound force its
image to be the full transvection group. No M22 action-image or fixed-space
conclusion is assumed.

The same displacement pairing computes fixed codimensions of all elementary
subgroups in V6 and proves the common-four fixed dimension five in U7.
Source: Aschbacher--Smith H.15.4, printed p.400, using H.15.3(2) and H.14.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
namespace MathieuCode.M22Quintet.CocodeTransfer

open DualAction
open BinaryTransvectionGroups.LineAction

theorem finrank_U7 : Module.finrank (ZMod 2) U7 = 7 :=
  sextetPairSpan_finrank m22SourceSextet

theorem finrank_V6 : Module.finrank (ZMod 2) V6 = 6 :=
  finrank_V6_of_U7 finrank_U7

/-- Earlier M24 transvections and the H.14 inclusion of the quintet kernel. -/
structure SextetTransvectionInputs : Prop where
  kernel_le : K ≤ KS.comap m22PairStabilizer.subtype
  displacement : ∀ k ∈ KS, ∀ u ∈ U7, cocodeRepresentation k u - u ∈ U1
  faithful : ∀ k ∈ KS, (∀ u ∈ U7, cocodeRepresentation k u = u) → k = 1
  card_kernel : Nat.card K = 32

/-- The geometric center, before its identification with the ambient fixed space. -/
def geometricCenter : Submodule (ZMod 2) V6 := W1.comap V6.subtype

theorem finrank_geometricCenter : Module.finrank (ZMod 2) geometricCenter = 1 := by
  exact (Submodule.comapSubtypeEquivOfLe W1_le_V6).finrank_eq.trans finrank_W1

theorem kernelAction_mem_radical (D : SextetTransvectionInputs) (k : K) :
    cocodeKernelAction k ∈ BinaryLinear.radical geometricCenter := by
  constructor
  · intro v hv
    apply Subtype.ext
    exact W1_fixed (kernelInclusion k) v.val hv
  · intro v
    exact displacement_mem_W1 k.val
      (D.displacement k.val.val (D.kernel_le k.property)) v.val v.property

theorem kernelAction_faithful (D : SextetTransvectionInputs) :
    Function.Injective cocodeKernelAction := by
  apply (MonoidHom.ker_eq_bot_iff cocodeKernelAction).mp
  apply eq_bot_iff.mpr
  intro k hk
  have hkfix (u : Cocode) (hu : u ∈ U7) : cocodeRepresentation k.val.val u = u := by
    have he := congrArg (fun f : BinaryLinear.GL V6 =>
      (f ⟨m22PairLine.mkQ u, ⟨u, hu, rfl⟩⟩).val) hk
    change m22PairLine.mkQ (cocodeRepresentation k.val.val u) = m22PairLine.mkQ u at he
    have hp : cocodeRepresentation k.val.val u - u ∈ m22PairLine :=
      (Submodule.Quotient.eq m22PairLine).mp he
    exact sub_eq_zero.mp ((Submodule.disjoint_def.mp U1_disjoint_pairLine) _
      (D.displacement k.val.val (D.kernel_le k.property) u hu) hp)
  apply Subtype.ext
  apply Subtype.ext
  exact D.faithful k.val.val (D.kernel_le k.property) hkfix

theorem kernelAction_full (D : SextetTransvectionInputs) :
    cocodeKernelAction.range = BinaryLinear.radical geometricCenter := by
  let : Finite V6 := Module.finite_iff_finite.mp (inferInstance : Module.Finite (ZMod 2) V6)
  have hle : cocodeKernelAction.range ≤ BinaryLinear.radical geometricCenter := by
    rintro g ⟨k,rfl⟩
    exact kernelAction_mem_radical D k
  apply Subgroup.eq_of_le_of_card_ge hle
  have hb := card_radical_le geometricCenter
  rw [finrank_V6, finrank_geometricCenter] at hb
  have hc : Nat.card cocodeKernelAction.range = 32 :=
    (Nat.card_congr (MonoidHom.ofInjective (kernelAction_faithful D)).toEquiv).symm.trans
      D.card_kernel
  rw [hc]
  exact hb

/-- The fixed space inside the middle term is exactly the geometric center. -/
theorem middle_fixed_eq_geometricCenter (D : SextetTransvectionInputs) :
    V1.comap V6.subtype = geometricCenter := by
  ext v
  change (∀ k : K, m22OuterCocodeRepresentation k.val v.val = v.val) ↔
    v ∈ geometricCenter
  have hn : geometricCenter ≠ ⊥ := by
    intro he
    have hd := finrank_geometricCenter
    rw [he, finrank_bot] at hd
    omega
  rw [BinaryLinear.mem_iff_fixed_radical hn]
  constructor
  · intro hv g hg
    rw [← kernelAction_full D] at hg
    obtain ⟨k,rfl⟩ := hg
    exact Subtype.ext (hv k)
  · intro hv k
    exact congrArg Subtype.val (hv (cocodeKernelAction k) (kernelAction_mem_radical D k))

/-- The full image may already be stated using the intrinsic center. -/
theorem kernelAction_full_intrinsic (D : SextetTransvectionInputs) :
    cocodeKernelAction.range = BinaryLinear.radical (V1.comap V6.subtype) := by
  rw [middle_fixed_eq_geometricCenter D]
  exact kernelAction_full D

/-- The actual middle action of any subgroup of the quintet kernel. -/
def subgroupMiddleAction (A : Subgroup m22PairStabilizer) (hA : A ≤ K) :
    A →* BinaryLinear.GL V6 := cocodeKernelAction.comp (Subgroup.inclusion hA)

theorem subgroupMiddleAction_fixed (A : Subgroup m22PairStabilizer) (hA : A ≤ K) :
    BinaryLinear.fixedSpace (subgroupMiddleAction A hA).range =
      (fixedSpace m22OuterCocodeRepresentation A).comap V6.subtype := by
  ext v
  constructor
  · intro hv a
    exact congrArg Subtype.val (hv _ ⟨a,rfl⟩)
  · rintro hv g ⟨a,rfl⟩
    exact Subtype.ext (hv a)

/-- Every elementary subgroup has exactly its rank as fixed codimension in V6. -/
theorem finrank_middle_fixed_add (D : SextetTransvectionInputs)
    (A : Subgroup m22PairStabilizer) (hA : A ≤ K) [IsElementaryAbelian 2 A]
    (r : ℕ) (hcard : Nat.card A = 2 ^ r) :
    Module.finrank (ZMod 2) ((fixedSpace m22OuterCocodeRepresentation A).comap V6.subtype)
      + r = 6 := by
  let c : geometricCenter ≃ₗ[ZMod 2] ZMod 2 :=
    LinearEquiv.ofFinrankEq _ _ (by rw [finrank_geometricCenter, Module.finrank_self])
  have hf : Function.Injective (subgroupMiddleAction A hA) :=
    (kernelAction_faithful D).comp (Subgroup.inclusion_injective hA)
  have hd := finrank_fixed_add_of_card (subgroupMiddleAction A hA) geometricCenter c
    (fun a => kernelAction_mem_radical D (Subgroup.inclusion hA a)) hf r hcard
  rwa [subgroupMiddleAction_fixed, finrank_V6] at hd

/-- Restrict the original cocode action to U7, using only the sextet displacement law. -/
def sextetMiddleRepresentation (D : SextetTransvectionInputs) :
    Representation (ZMod 2) KS U7 :=
  (show Subrepresentation (cocodeRepresentation.comp KS.subtype) from
    { toSubmodule := U7
      apply_mem_toSubmodule k u hu := by
        change cocodeRepresentation k.val u ∈ U7
        have h := U7.add_mem (U1_le_U7 (D.displacement k.val k.property u hu)) hu
        simpa only [sub_add_cancel] using h }).toRepresentation

def sextetMiddleAction (D : SextetTransvectionInputs) : KS →* BinaryLinear.GL U7 :=
  linearAction (sextetMiddleRepresentation D)

theorem sextetMiddleAction_faithful (D : SextetTransvectionInputs) :
    Function.Injective (sextetMiddleAction D) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro k hk
  apply Subtype.ext
  apply D.faithful k.val k.property
  intro u hu
  exact congrArg (fun f : BinaryLinear.GL U7 => (f ⟨u,hu⟩).val) hk

def sextetCenter : Submodule (ZMod 2) U7 := U1.comap U7.subtype

theorem finrank_sextetCenter : Module.finrank (ZMod 2) sextetCenter = 1 :=
  (Submodule.comapSubtypeEquivOfLe U1_le_U7).finrank_eq.trans
    (sextetTetradLine_finrank m22SourceSextet)

theorem sextetMiddleAction_mem_radical (D : SextetTransvectionInputs) (k : KS) :
    sextetMiddleAction D k ∈ BinaryLinear.radical sextetCenter := by
  constructor
  · intro u hu
    apply Subtype.ext
    obtain ⟨k',hk',he⟩ := k.property
    change cocodeRepresentation k.val u.val = u.val
    rw [← he]
    exact sextetTetradLine_le_fixed _ hu k'
  · intro u
    exact D.displacement k.val k.property u.val u.property

/-- The source common four fixes precisely five dimensions in the original U7. -/
theorem finrank_common_middle_fixed (D : SextetTransvectionInputs)
    [IsElementaryAbelian 2 E24] (hcard : Nat.card E24 = 4) :
    Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation E24 ⊓ U7 : Submodule (ZMod 2) Cocode) = 5 := by
  let ι : E24 →* KS := Subgroup.inclusion inf_le_right
  let ρ := (sextetMiddleAction D).comp ι
  let c : sextetCenter ≃ₗ[ZMod 2] ZMod 2 :=
    LinearEquiv.ofFinrankEq _ _ (by rw [finrank_sextetCenter, Module.finrank_self])
  have hf : Function.Injective ρ :=
    (sextetMiddleAction_faithful D).comp (Subgroup.inclusion_injective inf_le_right)
  have hd := finrank_fixed_add_of_card ρ sextetCenter c
    (fun e => sextetMiddleAction_mem_radical D (ι e)) hf 2 (by simpa using hcard)
  have he : BinaryLinear.fixedSpace ρ.range =
      (fixedSpace cocodeRepresentation E24).comap U7.subtype := by
    ext u
    constructor
    · intro hu e
      exact congrArg Subtype.val (hu _ ⟨e,rfl⟩)
    · rintro hu g ⟨e,rfl⟩
      exact Subtype.ext (hu e)
  have hdim : Module.finrank (ZMod 2) ((fixedSpace cocodeRepresentation E24).comap U7.subtype) =
      Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation E24 ⊓ U7 :
        Submodule (ZMod 2) Cocode) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_comm]
  rw [he, hdim, finrank_U7] at hd
  omega

end MathieuCode.M22Quintet.CocodeTransfer
