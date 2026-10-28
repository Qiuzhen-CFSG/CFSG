module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Preparation
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SylowSingular
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The singular normal section in the nonabelian rank-two branch

For the literal quotient `U / Z(U)`, a totally singular section invariant
under a Sylow subgroup of the full plus orthogonal group has dimension at
most one. The seed already has this dimension, so lifting through the
actual quotient gives equality with the seed. This is the finite linear
step identifying `E = V` in Aschbacher--Smith 14.3.18(1), pp. 995--996.
The orthogonal marking and invariance remain explicit until the source
recognition theorem constructs them.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- The actual singular section equals the original rank-two seed. -/
public theorem singular_section_eq_seed
    (F : InvariantFlag T V 2) [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 F.Uhat]
    (d : Recognition.ClosureGeometry F) (hcenter : F.ZU = F.Vi 1)
    (E : Subgroup G) (hVE : V ≤ E) (hEU : E ≤ F.U)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] BinaryFourPlus.V)
    (P : Sylow 2 BinaryFourPlus.q.isometrySubgroup)
    (hs : ∀ v ∈ hatSpace F E, BinaryFourPlus.q (e v) = 0)
    (hi : ∀ t : P, ∀ v ∈ hatSpace F E,
      e.symm (t.val.val (e v)) ∈ hatSpace F E) : E = V := by
  let S := (hatSpace F E).map e.toLinearMap
  have hs' : ∀ v ∈ S, BinaryFourPlus.q v = 0 := by
    rintro v ⟨w, hw, rfl⟩
    exact hs w hw
  have hi' : ∀ t : P, ∀ v ∈ S, t.val.val v ∈ S := by
    rintro t v ⟨w, hw, rfl⟩
    exact ⟨e.symm (t.val.val (e w)), hi t w hw, e.apply_symm_apply _⟩
  have hr := BinaryFourPlus.sylow_singular_invariant_finrank P S hs' hi'
  change Module.finrank (ZMod 2) ((hatSpace F E).map e.toLinearMap) ≤ 1 at hr
  rw [LinearEquiv.finrank_map_eq] at hr
  have hv : Module.finrank (ZMod 2) (hatSpace F V) = 1 := by
    exact (congrArg (fun A : Subgroup G => Module.finrank (ZMod 2) (hatSpace F A))
      F.last).symm.trans (finrank_hatSpace_plane F (by decide) d.seed_center)
  have hle : hatSpace F V ≤ hatSpace F E := by
    rintro v ⟨u, hu, rfl⟩
    exact ⟨u, hVE hu, rfl⟩
  have heq : hatSpace F V = hatSpace F E :=
    Submodule.eq_of_le_of_finrank_le hle (by simpa only [hv] using hr)
  apply le_antisymm ?_ hVE
  intro x hx
  let u : F.U := ⟨x, hEU hx⟩
  have hum : Additive.ofMul (QuotientGroup.mk' (center F.U) u) ∈ hatSpace F E :=
    ⟨u, hx, rfl⟩
  rw [← heq] at hum
  obtain ⟨v, hv, he⟩ := hum
  have hk : v⁻¹ * u ∈ center F.U := by
    apply (QuotientGroup.eq_one_iff (N := center F.U) (v⁻¹ * u)).mp
    change QuotientGroup.mk' (center F.U) (v⁻¹ * u) = 1
    rw [map_mul, map_inv, he]
    exact inv_mul_cancel _
  have hz : ((v⁻¹ * u : F.U) : G) ∈ V :=
    (show F.ZU ≤ V from hcenter ▸ F.le_seed 1) ⟨v⁻¹ * u, hk, rfl⟩
  have hx' := V.mul_mem hv hz
  change (v : G) * ((v : G)⁻¹ * x) ∈ V at hx'
  simpa only [mul_inv_cancel_left] using hx'
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource
