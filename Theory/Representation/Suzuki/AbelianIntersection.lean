module
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiActors
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# An abelian intersection over a smallest Suzuki quotient

Suppose elementary abelian subgroups X and Y normalize each other and
C lies in their intersection. Assume the literal Y/C has a faithful
Suzuki action of order q^4, with X inducing the actual Sylow omega-center.
The image of X intersect Y contains the moved space, because [Y,X] lies
in the intersection. It lies in the fixed space, because X is abelian.

The Suzuki square bound on the action and its dual gives respectively
at most q^2 fixed vectors and at least q^2 moved vectors. Thus the
intersection image has order q^2. If |C| = q, the actual intersection
has order q^3. The action and subgroup quotient maps stay literal.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.6)(c), printed p.183, using the Suzuki module bounds of Chapter 5.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

/-- Faithful Suzuki square bounds determine the order of the original abelian intersection. -/
theorem suzuki_abelian_intersection_card
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
    Nat.card (X ⊓ Y : Subgroup G) = (2^(2*n+1))^3 := by
  let W := Additive (Y ⧸ C.subgroupOf Y)
  let π := QuotientGroup.mk' (C.subgroupOf Y)
  let H := X ⊓ Y
  let E := omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup n))
  let M := quotientImage Y π H
  let : IsElementaryAbelian 2 E := suzukiSylow_omega_elementary hn (MulEquiv.refl _) T
  have hEcard : Nat.card E = 2^(2*n+1) := suzukiSylow_omega_card hn (MulEquiv.refl _) T
  have hEbig : 2 < Nat.card E := by
    rw [hEcard]
    exact (show 2 = (2:ℕ)^1 by norm_num).trans_lt
      (Nat.pow_lt_pow_right (by decide) (by omega))
  have htop : quotientImage Y π Y = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (C.subgroupOf Y) v.toMul
    exact ⟨y,y.property,hy⟩
  have hm : subspaceCommutator ρ ⊤ E ≤ M := by
    have he := quotientImage_commutator ρ Y Y X hXY le_rfl f π
      (QuotientGroup.mk'_surjective _) hρ
    rw [htop,hT] at he
    rw [←he]
    have hc : ⁅Y,X⁆ ≤ H := le_inf
      (by rw [commutator_comm]; exact le_normalizer_iff_commutator_le_left.mp hYX)
      (le_normalizer_iff_commutator_le_left.mp hXY)
    change ((⁅Y,X⁆).subgroupOf Y).map π ≤ (H.subgroupOf Y).map π
    exact map_mono (subgroupOf_mono Y hc)
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
    have hc : (x : G) * (y : G) = (y : G) * (x : G) :=
      congrArg Subtype.val (mul_comm x (⟨y,hy.1⟩ : X))
    have hy' : (⟨(x : G) * y * (x : G)⁻¹,
        le_normalizer_iff.mp hXY x x.property y y.property⟩ : Y) = y := by
      apply Subtype.ext
      change (x : G) * (y : G) * (x : G)⁻¹ = y
      rw [hc,mul_inv_cancel_right]
    rw [hy']
  have hlow := Representation.RankOne.QuadraticRecognition.suzuki_noncyclic_square_bound
    hn ρ hf T E (omegaOneAmbient_le _) hEbig
  let : Finite (Module.Dual (ZMod 2) W) := Finite.of_injective
    (fun f : Module.Dual (ZMod 2) W => (f : W → ZMod 2)) DFunLike.coe_injective
  have hdual := Representation.RankOne.QuadraticRecognition.suzuki_noncyclic_square_bound
    hn ρ.dual (faithful_dual ρ hf) T E (omegaOneAmbient_le _) hEbig
  have hdualcard : Nat.card (Module.Dual (ZMod 2) W ⧸ fixedSpace ρ.dual E) =
      Nat.card (subspaceCommutator ρ ⊤ E) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := Module.Dual (ZMod 2) W ⧸ fixedSpace ρ.dual E),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subspaceCommutator ρ ⊤ E)]
    exact congrArg (fun d => Nat.card (ZMod 2)^d) (fixedCodim_dual_eq_moved_finrank ρ E)
  rw [hdualcard,hEcard] at hdual
  rw [hEcard] at hlow
  have hMlow : (2^(2*n+1))^2 ≤ Nat.card M := hdual.trans
    (Nat.card_le_card_of_injective (Submodule.inclusion hm) (Submodule.inclusion_injective hm))
  have hMfix : Nat.card M ≤ Nat.card (fixedSpace ρ E) :=
    Nat.card_le_card_of_injective (Submodule.inclusion hfix) (Submodule.inclusion_injective hfix)
  have hprod := Submodule.card_eq_card_quotient_mul_card (fixedSpace ρ E)
  change Nat.card (Y ⧸ C.subgroupOf Y) = _ at hprod
  rw [hcard] at hprod
  have hMcard : Nat.card M = (2^(2*n+1))^2 := by
    have hp : 0 < (2^(2*n+1))^2 := by positivity
    have hbound : Nat.card M * (2^(2*n+1))^2 ≤ (2^(2*n+1))^2 * (2^(2*n+1))^2 := by
      calc
        _ ≤ Nat.card (fixedSpace ρ E) * Nat.card (W ⧸ fixedSpace ρ E) :=
          Nat.mul_le_mul hMfix hlow
        _ = _ := by rw [←hprod]; ring
    apply le_antisymm _ hMlow
    nlinarith
  have hindex : Nat.card M = C.relIndex H := by
    rw [←binarySubgroup_card]
    change Nat.card ((H.subgroupOf Y).map π) = _
    rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf (show H ≤ Y from inf_le_right)]
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup G) C H bot_le hC
  rw [relIndex_bot_left,relIndex_bot_left,←hindex,hMcard,hCcard] at hmul
  rw [←hmul]
  ring

end Subgroup
