module
public import Theory.Representation.BinaryOffender.UniformFixedSpace
public import Theory.Representation.BinaryOffender.ComponentPermutationObstruction

/-!
# Binary elementary actions of fixed codimension at most two

A displacement of rank two has the full actor fixed space as its kernel.
A displacement of rank one is an invariant binary line, hence is fixed
pointwise. These two cases show that every displacement is fixed by the
whole elementary actor. This is the finite linear step used in MS93 (3.6),
printed p.871, for the natural four-dimensional symplectic module.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem fixes_range_of_rank_one (ρ : Representation (ZMod 2) G V)
    (a b : G) (hab : Commute a b)
    (hd : Module.finrank (ZMod 2) (LinearMap.range (ρ b - LinearMap.id)) = 1)
    (v : V) : ρ a (ρ b v-v) = ρ b v-v := by
  let D := LinearMap.range (ρ b - LinearMap.id)
  have hD : Nat.card D = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    rfl
  have hm : ρ a (ρ b v-v) ∈ D := by
    refine ⟨ρ a v, ?_⟩
    change ρ b (ρ a v) - ρ a v = ρ a (ρ b v-v)
    rw [map_sub, ←Module.End.mul_apply, ←map_mul, ←hab.eq, map_mul]
    rfl
  let x : D := ⟨ρ b v-v, ⟨v,rfl⟩⟩
  let y : D := ⟨ρ a (ρ b v-v),hm⟩
  by_cases hx : x = 0
  · have hxv : ρ b v-v=0 := congrArg Subtype.val hx
    simp [hxv]
  obtain ⟨z,hz,hunique⟩ := (Nat.card_eq_two_iff' (0 : D)).mp hD
  have hy : y ≠ 0 := by
    intro he
    apply hx
    apply Subtype.ext
    have hyv : ρ a (ρ b v-v) = 0 := congrArg Subtype.val he
    change ρ b v-v = 0
    apply (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)).injective
    change ρ a (ρ b v-v) = ρ a 0
    rw [hyv,map_zero]
  exact congrArg Subtype.val ((hunique y hy).trans (hunique x hx).symm)

/-- Codimension at most two forces an elementary binary action to be quadratic. -/
theorem isQuadratic_of_fixedCodim_le_two (ρ : Representation (ZMod 2) G V)
    {A : Subgroup G} [IsElementaryAbelian 2 A] (hd : fixedCodim ρ A ≤ 2) :
    IsQuadratic ρ A := by
  intro a ha b hb v
  have hab : Commute a b := congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a,ha⟩ : A) ⟨b,hb⟩)
  have hdb : fixedCodim ρ (zpowers b) ≤ fixedCodim ρ A := by
    have hh := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr hb))
    have hA := fixedCodim_add_finrank ρ A
    have hB := fixedCodim_add_finrank ρ (zpowers b)
    omega
  by_cases htwo : fixedCodim ρ (zpowers b) = 2
  · have hfix := fixedSpace_eq_of_fixedCodim_eq ρ (zpowers_le.mpr hb) (by omega : fixedCodim ρ A = fixedCodim ρ (zpowers b))
    have hv : ρ b v-v ∈ fixedSpace ρ (zpowers b) := by
      rw [mem_fixedSpace_zpowers_iff]
      exact involution_fixes_displacement ρ
        (by simpa [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb) v
    rw [←hfix] at hv
    exact hv ⟨a,ha⟩
  · have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ b - LinearMap.id)) ≤ 1 := by
      rw [←fixedCodim_zpowers_eq_displacement_rank]
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with hz | ho
    · have hbot : LinearMap.range (ρ b - LinearMap.id) = ⊥ := Submodule.finrank_eq_zero.mp hz
      have hv : ρ b v-v = 0 := by
        have hh : ρ b v-v ∈ LinearMap.range (ρ b - LinearMap.id) := ⟨v,rfl⟩
        simpa [hbot] using hh
      simp [hv]
    · exact fixes_range_of_rank_one ρ a b hab ho v
end Representation.BinaryOffender
