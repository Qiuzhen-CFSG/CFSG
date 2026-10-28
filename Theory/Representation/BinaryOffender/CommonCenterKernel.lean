module
public import Theory.Representation.BinaryOffender.CommonCenterBound
public import Theory.ElementaryAbelian.Injective

/-!
# Common-line displacement with a known action kernel

If an elementary binary actor moves a module into one fixed line, the
fixed codimension plus the rank of any subgroup acting trivially is at most
the actor rank. Scalar displacement embeds the trivial subgroup into the
kernel of the displacement map; rank-nullity gives the bound. Restriction
to an invariant denominator loses only its actual codimension.

This sharpens the common-center estimate used in Aschbacher--Smith F.9.16
and provides the kernel calculation for 14.6.24(3), printed pp.1039--1040.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryOffender.CommonCenter
variable {A V : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
private theorem actor_dim : Module.finrank (ZMod 2) (Additive A) = Nat.log 2 (Nat.card A) := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  rw [Nat.card_zmod] at hc
  change _ = Nat.log 2 (Nat.card (Additive A))
  rw [hc, Nat.log_pow Nat.one_lt_two]

/-- The effective common-center rank retains every known trivial subgroup. -/
theorem fixedCodim_add_trivial_rank_le (ρ : Representation (ZMod 2) A V)
    (Z : Submodule (ZMod 2) V) (hZ : Module.finrank (ZMod 2) Z ≤ 1)
    (hd : ∀ a v, ρ a v - v ∈ Z) (hz : ∀ a z, z ∈ Z → ρ a z = z)
    (B : Subgroup A) (hB : ∀ b ∈ B, ∀ v, ρ b v = v) :
    fixedCodim ρ ⊤ + rank B ≤ Nat.log 2 (Nat.card A) := by
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective B.subtype B.subtype_injective
  by_cases hn : Z = ⊥
  · have hf : fixedSpace ρ ⊤ = ⊤ := by
      apply top_unique
      intro v _ a
      have hh := hd a v
      rw [hn,Submodule.mem_bot] at hh
      exact sub_eq_zero.mp hh
    have hc := fixedCodim_add_finrank ρ ⊤
    rw [hf,finrank_top] at hc
    have hr : rank B ≤ Nat.log 2 (Nat.card A) :=
      Nat.log_mono_right (Nat.card_le_card_of_injective B.subtype B.subtype_injective)
    omega
  · have hdim : Module.finrank (ZMod 2) Z = 1 := by
      have hp : 0 < Module.finrank (ZMod 2) Z := by
        by_contra hh
        exact hn (Submodule.finrank_eq_zero.mp (by omega))
      omega
    let e : Z ≃ₗ[ZMod 2] ZMod 2 := LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
    let f := displacementMap ρ Z e hd hz
    let j : Additive B →ₗ[ZMod 2] Additive A :=
      AddMonoidHom.toZModLinearMap 2 B.subtype.toAdditive
    have hj : Function.Injective j := B.subtype_injective
    have hker : LinearMap.range j ≤ f.ker := by
      rintro _ ⟨b,rfl⟩
      apply LinearMap.ext
      intro v
      exact (displacement_eq_zero_iff ρ Z e hd b.toMul.val v).mpr (hB _ b.toMul.property v)
    have hr := Submodule.finrank_mono hker
    rw [LinearMap.finrank_range_of_inj hj, actor_dim] at hr
    have hdims := f.finrank_range_add_finrank_ker
    have hn := Subspace.finrank_add_finrank_dualCoannihilator_eq f.range
    rw [←fixedSpace_eq_annihilator ρ Z e hd hz] at hn
    have hc := fixedCodim_add_finrank ρ ⊤
    rw [actor_dim] at hdims
    change Nat.log 2 (Nat.card B) ≤ _ at hr
    change fixedCodim ρ ⊤ + Nat.log 2 (Nat.card B) ≤ _
    omega
/-- The same bound on an invariant subspace includes its exact codimension loss. -/
theorem fixedCodim_add_trivial_rank_le_codim (ρ : Representation (ZMod 2) A V)
    (W : Subrepresentation ρ) (Z : Submodule (ZMod 2) V)
    (hZ : Module.finrank (ZMod 2) Z ≤ 1)
    (hd : ∀ a v, v ∈ W.toSubmodule → ρ a v - v ∈ Z)
    (hz : ∀ a z, z ∈ Z → ρ a z = z)
    (B : Subgroup A) (hB : ∀ b ∈ B, ∀ v ∈ W.toSubmodule, ρ b v = v) :
    fixedCodim ρ ⊤ + rank B ≤ Nat.log 2 (Nat.card A) +
      Module.finrank (ZMod 2) (V ⧸ W.toSubmodule) := by
  let Z' := Z.comap W.toSubmodule.subtype
  have hZ' : Module.finrank (ZMod 2) Z' ≤ 1 := by
    have he : Module.finrank (ZMod 2) Z' =
        Module.finrank (ZMod 2) (W.toSubmodule ⊓ Z : Submodule (ZMod 2) V) := by
      rw [←Submodule.finrank_map_subtype_eq,Submodule.map_comap_subtype]
    exact he.le.trans ((Submodule.finrank_mono inf_le_right).trans hZ)
  have hc := fixedCodim_add_trivial_rank_le W.toRepresentation Z' hZ'
    (fun a v => hd a v v.property) (fun a z hz' => Subtype.ext (hz a z hz'))
    B (fun b hb v => Subtype.ext (hB b hb v v.property))
  have hh := fixedCodim_le_subrepresentation_add_codim ρ W ⊤
  omega
end Representation.BinaryOffender.CommonCenter
