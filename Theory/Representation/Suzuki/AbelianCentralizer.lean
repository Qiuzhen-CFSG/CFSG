module
public import Theory.Representation.Suzuki.AbelianIntersection

/-!
# The exact centralizer in a smallest Suzuki span

For two elementary abelian subgroups normalizing each other, the faithful
Suzuki action on the literal Y/C quotient bounds the centralizer of X in Y
by q^3. The previously proved intersection already has this order. Thus
C_Y(X) is exactly X intersect Y. This retains the actual quotient and
conjugation maps; no fixed-space equality is an input.

The source application identifies the restriction of a full second ball
kernel to the other span, as used in DGS (12.8).
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.6)(c), (12.8), printed pp.183,185, and the Chapter 5 module bounds.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

/-- The original abelian intersection is the whole mutual centralizer inside Y. -/
theorem suzuki_abelian_intersection_centralizer
    (X Y C : Subgroup G) [IsElementaryAbelian 2 X] [IsElementaryAbelian 2 Y]
    [Finite Y] [(C.subgroupOf Y).Normal]
    (hC : C ≤ X ⊓ Y) (hXY : X ≤ normalizer (Y : Set G))
    (hYX : Y ≤ normalizer (X : Set G))
    {n : ℕ} (hn : 0 < n)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup n)
      (Additive (Y ⧸ C.subgroupOf Y))) (hf : Function.Injective ρ)
    (f : X →* SuzukiMatrixGroup n) (T : Sylow 2 (SuzukiMatrixGroup n))
    (hT : f.range = omegaOneAmbient (T : Subgroup _))
    (hρ : ∀ x : X, ∀ y : Y,
      ρ (f x) (Additive.ofMul (QuotientGroup.mk y)) =
        Additive.ofMul (QuotientGroup.mk ⟨(x : G) * y * (x : G)⁻¹,
          le_normalizer_iff.mp hXY x x.property y y.property⟩))
    (hcard : Nat.card (Y ⧸ C.subgroupOf Y) = (2^(2*n+1))^4)
    (hCcard : Nat.card C = 2^(2*n+1)) :
    Y ⊓ centralizer (X : Set G) = X ⊓ Y := by
  let W := Additive (Y ⧸ C.subgroupOf Y)
  let π := QuotientGroup.mk' (C.subgroupOf Y)
  let D := Y ⊓ centralizer (X : Set G)
  let E := omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup n))
  let M := quotientImage Y π D
  have hHD : X ⊓ Y ≤ D := by
    intro y hy
    refine ⟨hy.2,?_⟩
    intro x hx
    exact congrArg Subtype.val (mul_comm (⟨x,hx⟩ : X) ⟨y,hy.1⟩)
  have hCD : C ≤ D := hC.trans hHD
  let : IsElementaryAbelian 2 E := suzukiSylow_omega_elementary hn (MulEquiv.refl _) T
  have hEcard : Nat.card E = 2^(2*n+1) := suzukiSylow_omega_card hn (MulEquiv.refl _) T
  have hEbig : 2 < Nat.card E := by
    rw [hEcard]
    exact (show 2 = (2:ℕ)^1 by norm_num).trans_lt
      (Nat.pow_lt_pow_right (by decide) (by omega))
  have hfix : M ≤ fixedSpace ρ E := by
    intro v hv a
    obtain ⟨y,hy,he⟩ := hv
    have hv' : v = Additive.ofMul (π y) := (congrArg Additive.ofMul he).symm
    rw [hv']
    have ha : a.val ∈ f.range := hT.symm ▸ a.property
    obtain ⟨x,hx⟩ := ha
    change ρ a.val (Additive.ofMul (π y)) = Additive.ofMul (π y)
    rw [←hx]
    change ρ (f x) (Additive.ofMul (QuotientGroup.mk y)) = Additive.ofMul (QuotientGroup.mk y)
    rw [hρ]
    have hy' : (⟨(x : G) * y * (x : G)⁻¹,
        le_normalizer_iff.mp hXY x x.property y y.property⟩ : Y) = y := by
      apply Subtype.ext
      change (x : G) * (y : G) * (x : G)⁻¹ = y
      have hc : (x : G) * (y : G) = (y : G) * (x : G) := hy.2 x x.property
      rw [hc,mul_inv_cancel_right]
    rw [hy']
  have hlow := Representation.RankOne.QuadraticRecognition.suzuki_noncyclic_square_bound
    hn ρ hf T E (omegaOneAmbient_le _) hEbig
  rw [hEcard] at hlow
  have hMfix : Nat.card M ≤ Nat.card (fixedSpace ρ E) :=
    Nat.card_le_card_of_injective (Submodule.inclusion hfix) (Submodule.inclusion_injective hfix)
  have hprod := Submodule.card_eq_card_quotient_mul_card (fixedSpace ρ E)
  change Nat.card (Y ⧸ C.subgroupOf Y) = _ at hprod
  rw [hcard] at hprod
  have hMcard : Nat.card M ≤ (2^(2*n+1))^2 := by
    have hp : 0 < (2^(2*n+1))^2 := by positivity
    have hbound : Nat.card M * (2^(2*n+1))^2 ≤ (2^(2*n+1))^2 * (2^(2*n+1))^2 := by
      calc
        _ ≤ Nat.card (fixedSpace ρ E) * Nat.card (W ⧸ fixedSpace ρ E) :=
          Nat.mul_le_mul hMfix hlow
        _ = _ := by rw [←hprod]; ring
    nlinarith
  have hindex : Nat.card M = C.relIndex D := by
    rw [←binarySubgroup_card]
    change Nat.card ((D.subgroupOf Y).map π) = _
    rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf (show D ≤ Y from inf_le_left)]
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup G) C D bot_le hCD
  rw [relIndex_bot_left,relIndex_bot_left,←hindex,hCcard] at hmul
  have hDcard : Nat.card D ≤ (2^(2*n+1))^3 := by
    rw [←hmul]
    calc
      _ ≤ 2^(2*n+1) * (2^(2*n+1))^2 := Nat.mul_le_mul_left _ hMcard
      _ = _ := by ring
  let : Finite D := Finite.of_injective (inclusion (show D ≤ Y from inf_le_left))
    (inclusion_injective _)
  exact (eq_of_le_of_card_ge hHD (hDcard.trans_eq
    (suzuki_abelian_intersection_card X Y C hC hXY hYX hn ρ hf f T hT hρ hcard hCcard).symm)).symm

end Subgroup
