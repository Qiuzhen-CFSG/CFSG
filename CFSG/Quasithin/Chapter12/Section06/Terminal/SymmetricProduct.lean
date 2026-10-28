module
public import CFSG.Quasithin.Chapter12.Section06.Terminal.ProductAction
public import CFSG.Quasithin.Chapter12.Section06.Terminal
public import CFSG.Quasithin.Chapter12.Section06.Setup
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# Applying the terminal displacement bound to the original F.9 section

The actual coordinate map U_H → U_H/V₁ induces a linear quotient equivalence
from the full original U_H. Its kernel is used as the invariant subrepresentation,
so the existing terminal theorem applies with the same conjugation and projection.
The index bound |U_H:D_H|≤4 and |A₁|≤2 give its filtration bounds; the cubic
factor constructs its two faithful S₅ summands. The same actor's A₅ image has
at least two dimensions of displacement on each summand.

The final theorem discharges the action, decomposition, faithfulness, cubic
movement and factor-displacement premises. It retains the actual product marking,
local cubic placement and geometric witnesses from F.9.13/16. Their construction,
the nonabelian exclusion and the preceding local alternatives remain necessary
before the original natural-module reduction can be asserted.

Source: Aschbacher–Smith, proof of Theorem12.6.34, printed p.838 (PDF p.855).
-/

public section
open Subgroup Module Representation Representation.BinaryOffender InvertedCubicTensor
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06.Terminal
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The section's original coordinates and ambient commutator bound feed the
existing terminal theorem; the paired module and its lower bound are constructed. -/
theorem product_section_contradiction
    (H U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (π : H →* (Equiv.Perm (Fin 5) × S₃))
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 5) × S₃) W)
    (c : BinaryConjugationSection H U Z (σ.comp π))
    (hf : Function.Injective σ)
    (hfree : fixedSpace (rightAction σ) (alternatingGroup (Fin 3)) = ⊥)
    (D A : Subgroup G) (hDU : D ≤ U) (hD : D.relIndex U ≤ 4)
    (hA : Nat.card A ≤ 2) (b : H)
    (a : alternatingGroup (Fin 5)) (ha : orderOf a = 2) (hb : π b = (a.val, 1))
    (hcomm : ⁅D, zpowers (b : G)⁆ ≤ A) : False := by
  let ρ := seedRepresentation H U c.normalized
  let q : Additive U →ₗ[ZMod 2] W := c.coordinates.toAdditiveLeft.toZModLinearMap 2
  have hq : Function.Surjective q := Multiplicative.toAdd.surjective.comp c.onto
  have hqe (x : H) (u : Additive U) : q (ρ x u) = σ (π x) (q u) := c.equivariant x u.toMul
  let N : Subrepresentation ρ := {
    toSubmodule := q.ker
    apply_mem_toSubmodule := by
      intro x u hu
      change q (ρ x u) = 0
      rw [hqe, show q u = 0 from hu, map_zero] }
  let e₀ : (Additive U ⧸ N.toSubmodule) ≃ₗ[ZMod 2] W := q.quotKerEquivOfSurjective hq
  have he₀ (x : H) (u : Additive U ⧸ N.toSubmodule) :
      e₀ (N.quotientRepresentation x u) = σ (π x) (e₀ u) := by
    induction u using Submodule.Quotient.induction_on with
    | _ u => exact hqe x u
  let e := e₀.trans (productPairEquiv σ hfree).symm
  have he (u : Additive U ⧸ N.toSubmodule) :
      e (N.quotientRepresentation b u) =
        (productMultiplicity σ a.val (e u).1, productMultiplicity σ a.val (e u).2) := by
    apply (productPairEquiv σ hfree).injective
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [he₀, hb, productPairEquiv_equivariant, LinearEquiv.apply_symm_apply]
  let P := AddSubgroup.toZModSubmodule 2 (D.subgroupOf U).toAddSubgroup
  let B := AddSubgroup.toZModSubmodule 2 (A.subgroupOf U).toAddSubgroup
  have hPc : Nat.card P = Nat.card D :=
    Nat.card_congr (subgroupOfEquivOfLe hDU).toEquiv
  have hdimP : finrank (ZMod 2) (Additive U ⧸ P) ≤ 2 := by
    have hp := log_card_sub_log_card_eq_log_relIndex U D hDU
    rw [← hPc] at hp
    have hcU : Nat.card U = 2 ^ finrank (ZMod 2) (Additive U) :=
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)).trans
        (by rw [Nat.card_zmod])
    rw [hcU, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      Nat.log_pow Nat.one_lt_two, Nat.log_pow Nat.one_lt_two] at hp
    have hn := P.finrank_quotient_add_finrank
    have hl : Nat.log 2 (D.relIndex U) ≤ 2 := (Nat.log_mono_right hD).trans (by decide)
    omega
  have hdimB : finrank (ZMod 2) B ≤ 1 := by
    have hc : Nat.card B ≤ 2 :=
      (Nat.card_le_card_of_injective
        (f := fun x : A.subgroupOf U => (⟨x.val.val, x.property⟩ : A))
        (by
          intro x y hh
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun a : A => (a : G)) hh)).trans hA
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    by_contra! hh
    have h4 : 4 ≤ 2 ^ finrank (ZMod 2) B := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    omega
  have hs := Representation.AlternatingFiveInvolutionDisplacement.displacement_lower
    ((productMultiplicity σ).comp (alternatingGroup (Fin 5)).subtype)
    ((Representation.SymmetricFiveThree.multiplicity_faithful σ hf hfree).comp Subtype.val_injective)
    a ha
  apply terminal_contradiction_of_quotient_action ρ N P B b (productMultiplicity σ a.val)
    e he hdimP hdimB _ hs
  intro u hu
  change (ρ b u - u).toMul ∈ A.subgroupOf U
  change ((ρ b u - u).toMul : G) ∈ A
  rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
  change (b : G) * (u.toMul : G) * (b : G)⁻¹ * (u.toMul : G)⁻¹ ∈ A
  rw [commutator_comm] at hcomm
  exact hcomm (commutator_mem_commutator (mem_zpowers _) hu)

end CFSG.Quasithin.Chapter12.Section06.Terminal

namespace CFSG.Quasithin.Chapter12.Section06.Terminal
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}

/-- The marked product branch of the original F.9 setup. -/
theorem f9_terminal_contradiction (h : D.Hypothesis) (hV : D.V ≤ D.QH)
    (e : (D.H ⧸ pCore 2 D.H) ≃* Product)
    (hplace : cubicFactor ≤
      ((D.L₁ ⊔ (D.T : Subgroup G)).subgroupOf D.H).map (productMap e))
    (B A : Subgroup G) (hBU : B ≤ D.UH) (hB : B.relIndex D.UH ≤ 4)
    (hA : Nat.card A ≤ 2) (b : D.H)
    (a : alternatingGroup (Fin 5)) (ha : orderOf a = 2)
    (hb : productMap e b = (a.val, 1)) (hcomm : ⁅B, zpowers (b : G)⁆ ≤ A) : False := by
  let := h.UH_elementary_of_V_le_QH hV
  let : (D.V₁.subgroupOf D.UH).Normal := normal_of_isMulCommutative _
  obtain ⟨τ, c, hf, hfree, _⟩ := exists_product_section h e hplace
  exact product_section_contradiction D.H D.UH D.V₁ (productMap e) τ c hf hfree
    B A hBU hB hA b a ha hb hcomm

end CFSG.Quasithin.Chapter12.Section06.Terminal
