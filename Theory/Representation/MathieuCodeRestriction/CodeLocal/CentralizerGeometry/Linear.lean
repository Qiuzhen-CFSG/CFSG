module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.CommonCenterRank
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Linear algebra for the code involution centralizer

A nontrivial displacement into a line has a hyperplane kernel. An operator
of displacement rank one either fixes an invariant subspace or acts trivially
on the quotient. Finally, common-center displacement duality gives the fixed
codimension even when the elementary actor has a nontrivial action kernel.
The last formula retains that kernel instead of silently assuming faithfulness.

These lemmas apply to the literal Vz and C_V(z) in Aschbacher--Smith,
H.16.2(6--8), printed pp.402--403. The chapter application supplies the native
subspaces and keeps the concrete group and action assertions separate.
-/

public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- Displacement computed in the ambient space has the same rank as the
literal restricted action; the inclusion of W does not alter the image dimension. -/
theorem fixedCodim_stabilizer_zpowers_eq_ambient_displacement
    (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)
    (g : subspaceStabilizer ρ W) :
    fixedCodim (stabilizerRepresentation ρ W) (Subgroup.zpowers g) =
      Module.finrank (ZMod 2)
        (LinearMap.range ((ρ g.val - LinearMap.id).comp W.subtype)) := by
  have he : (ρ g.val - LinearMap.id).comp W.subtype =
      W.subtype.comp (stabilizerRepresentation ρ W g - LinearMap.id) := by
    ext w
    rfl
  rw [fixedCodim_zpowers_eq_displacement_rank, he, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective W.subtype W.subtype_injective _).finrank_eq

theorem finrank_inf_fixedSpace_of_line_displacement (ρ : Representation (ZMod 2) G V)
    (W L : Submodule (ZMod 2) V) (g : G)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hd : ∀ v ∈ W, ρ g v - v ∈ L)
    (hm : ∃ v ∈ W, ρ g v ≠ v) :
    Module.finrank (ZMod 2) (W ⊓ fixedSpace ρ (Subgroup.zpowers g) : Submodule (ZMod 2) V)
      + 1 = Module.finrank (ZMod 2) W := by
  let d : W →ₗ[ZMod 2] V := (ρ g - LinearMap.id).comp W.subtype
  have hr : d.range ≤ L := by
    rintro _ ⟨v, rfl⟩
    exact hd v v.property
  have hle := Submodule.finrank_mono hr
  rw [hL] at hle
  have hne : Module.finrank (ZMod 2) d.range ≠ 0 := by
    intro he
    have hz : d = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp he)
    obtain ⟨v, hv, hm⟩ := hm
    exact hm (sub_eq_zero.mp (LinearMap.congr_fun hz ⟨v, hv⟩))
  let e : d.ker ≃ₗ[ZMod 2]
      (W ⊓ fixedSpace ρ (Subgroup.zpowers g) : Submodule (ZMod 2) V) := {
    toFun := fun v => ⟨v.val.val, v.val.property,
      (mem_fixedSpace_zpowers_iff ρ g v.val).mpr (sub_eq_zero.mp v.property)⟩
    invFun := fun v => ⟨⟨v.val, v.property.1⟩,
      sub_eq_zero.mpr ((mem_fixedSpace_zpowers_iff ρ g v.val).mp v.property.2)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have he := e.finrank_eq
  have hn := d.finrank_range_add_finrank_ker
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem rank_one_displacement_alternative (ρ : Representation (ZMod 2) G V)
    (W U : Submodule (ZMod 2) V) (g : G) (hU : U ≤ W)
    (hstable : ∀ u ∈ U, ρ g u ∈ U)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range ((ρ g - LinearMap.id).comp W.subtype)) = 1) :
    (∀ u ∈ U, ρ g u = u) ∨ (∀ w ∈ W, ρ g w - w ∈ U) := by
  classical
  by_cases hf : ∀ u ∈ U, ρ g u = u
  · exact Or.inl hf
  right
  push Not at hf
  obtain ⟨u, hu, hmove⟩ := hf
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hr
    (show ρ g u - u ∈ LinearMap.range ((ρ g - LinearMap.id).comp W.subtype) from
      ⟨⟨u, hU hu⟩, rfl⟩) (sub_ne_zero.mpr hmove)
  have hle : LinearMap.range ((ρ g - LinearMap.id).comp W.subtype) ≤ U := by
    rw [hspan]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (U.sub_mem (hstable u hu) hu))
  intro w hw
  exact hle ⟨⟨w, hw⟩, rfl⟩

end Representation.BinaryOffender

open scoped IsMulCommutative
namespace Representation.BinaryOffender
open CommonCenter
variable {G V : Type*} [Group G] [Finite G] [IsElementaryAbelian 2 G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem finrank_fixedSpace_top_add_rank_of_common_center (ρ : Representation (ZMod 2) G V)
    (L : Submodule (ZMod 2) V) (hL : Module.finrank (ZMod 2) L = 1)
    (hd : ∀ g v, ρ g v - v ∈ L) (hz : ∀ g v, v ∈ L → ρ g v = v) :
    Module.finrank (ZMod 2) (fixedSpace ρ ⊤) + Nat.log 2 (Nat.card G) =
      Module.finrank (ZMod 2) V + rank (actionHom ρ).ker := by
  let e : L ≃ₗ[ZMod 2] ZMod 2 := LinearEquiv.ofFinrankEq _ _ (by simpa using hL)
  let d := displacementMap ρ L e hd hz
  have hk (a : Additive G) : d a = 0 ↔ actionHom ρ a.toMul = 1 := by
    rw [actionHom_eq_one_iff]
    constructor
    · intro h v
      exact (displacement_eq_zero_iff ρ L e hd a.toMul v).mp (LinearMap.congr_fun h v)
    · intro h
      apply LinearMap.ext
      intro v
      exact (displacement_eq_zero_iff ρ L e hd a.toMul v).mpr (h v)
  let ek : d.ker ≃ (actionHom ρ).ker := {
    toFun := fun a => ⟨a.val.toMul, (hk a.val).mp a.property⟩
    invFun := fun a => ⟨Additive.ofMul a.val, (hk _).mpr a.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hrG : Module.finrank (ZMod 2) (Additive G) = Nat.log 2 (Nat.card G) := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive G)
    rw [Nat.card_zmod] at hc
    change _ = Nat.log 2 (Nat.card (Additive G))
    rw [hc, Nat.log_pow Nat.one_lt_two]
  have hrK : Module.finrank (ZMod 2) d.ker = rank (actionHom ρ).ker := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := d.ker)
    rw [Nat.card_zmod] at hc
    rw [rank, ← Nat.card_congr ek, hc, Nat.log_pow Nat.one_lt_two]
  have hn := d.finrank_range_add_finrank_ker
  have ha := Subspace.finrank_add_finrank_dualCoannihilator_eq d.range
  rw [← fixedSpace_eq_annihilator ρ L e hd hz] at ha
  omega

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem finrank_fixedSpace_add_rank_of_common_center (ρ : Representation (ZMod 2) G V)
    (W L : Submodule (ZMod 2) V) (B : Subgroup G) [IsElementaryAbelian 2 B]
    (hW : B ≤ subspaceStabilizer ρ W) (hLW : L ≤ W)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hd : ∀ b ∈ B, ∀ w ∈ W, ρ b w - w ∈ L)
    (hz : L ≤ fixedSpace ρ B) :
    Module.finrank (ZMod 2) (W ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) + rank B =
      Module.finrank (ZMod 2) W + rank (subspaceKernel ρ W B) := by
  let σ : Representation (ZMod 2) B W :=
    (stabilizerRepresentation ρ W).comp (Subgroup.inclusion hW)
  let Z := L.comap W.subtype
  have hZ : Module.finrank (ZMod 2) Z = 1 :=
    (Submodule.comapSubtypeEquivOfLe hLW).finrank_eq.trans hL
  have h := finrank_fixedSpace_top_add_rank_of_common_center σ Z hZ
    (fun b w => hd b b.property w w.property)
    (fun b w hw => Subtype.ext (hz hw b))
  let ef : fixedSpace σ ⊤ ≃ₗ[ZMod 2]
      (W ⊓ fixedSpace ρ B : Submodule (ZMod 2) V) := {
    toFun := fun w => ⟨w.val.val, w.val.property,
      fun b => congrArg Subtype.val (w.property ⟨b, Subgroup.mem_top _⟩)⟩
    invFun := fun w => ⟨⟨w.val, w.property.1⟩,
      fun b => Subtype.ext (w.property.2 b.val)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  let ek : (actionHom σ).ker ≃ subspaceKernel ρ W B := {
    toFun := fun b => ⟨b.val.val, b.val.property, fun w hw =>
      congrArg Subtype.val ((actionHom_eq_one_iff σ b.val).mp b.property ⟨w, hw⟩)⟩
    invFun := fun b => ⟨⟨b.val, b.property.1⟩,
      (actionHom_eq_one_iff σ _).mpr (fun w => Subtype.ext (b.property.2 w w.property))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [ef.finrank_eq] at h
  change _ + rank B = _ + rank (actionHom σ).ker at h
  simp only [rank] at h
  rw [Nat.card_congr ek] at h
  exact h

end Representation.BinaryOffender
