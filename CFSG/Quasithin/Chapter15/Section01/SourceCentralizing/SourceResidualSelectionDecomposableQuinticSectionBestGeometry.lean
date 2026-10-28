module

public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.Representation.BinaryOffender.QuadraticTwoCosts
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Strict best-offender weights from a two-dimensional moved space

Displacement sends each element of a faithful actor B to a linear map
from W/C_W(B) into the moved space of any containing actor A. This map
of finite sets is injective; its cardinal bound requires no additivity
in the actor and hence no quadratic hypothesis. If the moved dimension
is at most two, rank B is at most twice its fixed codimension.

At (rank A, fixed codimension A) equal to (2,1) or (4,2), this bound
makes every proper subgroup have strictly smaller weight. Thus the whole
original actor is a minimal best offender; no arbitrary contained strong
offender is asserted to have rank two or four.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- Faithful displacement into a plane bounds every elementary subactor. -/
theorem rank_le_twice_fixedCodim_of_moved_plane
    (σ : Representation (ZMod 2) G W) (hfaith : Function.Injective σ)
    (A B : Subgroup G) [IsElementaryAbelian 2 B] (hBA : B ≤ A)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) ≤ 2) :
    rank B ≤ 2 * fixedCodim σ B := by
  let U := fixedSpace σ B
  let C := subspaceCommutator σ ⊤ A
  let D (b : B) : (W ⧸ U) →ₗ[ZMod 2] C :=
    U.liftQ ((σ b - LinearMap.id).codRestrict C
      (fun w => Submodule.subset_span ⟨b, hBA b.property, w, Submodule.mem_top, rfl⟩))
      (by intro w hw; exact Subtype.ext (sub_eq_zero.mpr (hw b)))
  have hD : Function.Injective D := by
    intro a b he
    apply Subtype.ext
    apply hfaith
    apply LinearMap.ext
    intro w
    have hh := congrArg (fun z : (W ⧸ U) →ₗ[ZMod 2] C => (z (U.mkQ w) : W)) he
    exact sub_left_injective hh
  let : Finite ((W ⧸ U) →ₗ[ZMod 2] C) := Module.finite_of_finite (ZMod 2)
  have hc : Nat.card B ≤ Nat.card ((W ⧸ U) →ₗ[ZMod 2] C) :=
    Nat.card_le_card_of_injective D hD
  have hBc : Nat.card B = 2 ^ rank B := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
    rw [rank, hn, Nat.log_pow (by decide : 1 < 2)]
  rw [hBc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Module.finrank_linearMap] at hc
  have hr := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  change rank B ≤ fixedCodim σ B * Module.finrank (ZMod 2) C at hr
  exact hr.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (fixedCodim σ B) hdim)

/-- Exact rank/codimension equality at the two plane costs makes the whole
original actor a minimal best offender. -/
theorem minimalBestOffender_of_moved_plane_exact_cost
    (σ : Representation (ZMod 2) G W) (hfaith : Function.Injective σ)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) ≤ 2)
    (hcost : (rank A = 2 ∧ fixedCodim σ A = 1) ∨
      (rank A = 4 ∧ fixedCodim σ A = 2)) :
    IsMinimalBestOffender σ A := by
  let : IsElementaryAbelian 2 A := hA.2
  have hstrict (B : Subgroup G) (hBA : B ≤ A) (hne : B ≠ A) : weight σ B < weight σ A := by
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBA
    have hBc : Nat.card B = 2 ^ rank B := by
      obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
      rw [rank, hn, Nat.log_pow (by decide : 1 < 2)]
    have hcard : Nat.card B < Nat.card A := by
      have hle : Nat.card B ≤ Nat.card A :=
        Nat.card_le_card_of_injective (inclusion hBA) (inclusion_injective hBA)
      have hn : Nat.card B ≠ Nat.card A := fun hh => hne (eq_of_le_of_card_ge hBA hh.ge)
      omega
    rw [hBc, hA.card_eq_two_pow_rank] at hcard
    have hr : rank B < rank A := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hcard
    have hb := rank_le_twice_fixedCodim_of_moved_plane σ hfaith A B hBA hdim
    have hda := fixedCodim_add_finrank σ A
    have hdb := fixedCodim_add_finrank σ B
    unfold weight
    rcases hcost with hcost | hcost <;> omega
  refine ⟨⟨hA, ?_⟩, ?_⟩
  · intro B hBA
    by_cases he : B = A
    · exact he ▸ le_rfl
    · exact (hstrict B hBA he).le
  · intro B _ he
    by_contra hn
    exact (ne_of_lt (hstrict B he.1 hn)) he.2

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
