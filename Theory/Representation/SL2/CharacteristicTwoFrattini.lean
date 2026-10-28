module
public import Theory.Representation.SL2.FullFixedIndex
public import Theory.Representation.FrattiniAction
public import Theory.GroupTheory.PCoreFrattiniAction

/-!
# Frattini size above a nonbinary linear quotient

A finite group with self-centralizing two-core acts faithfully on that
core modulo its Frattini subgroup. If the quotient is SL₂(q), q > 3,
the nontrivial binary representation has dimension at least twice the
field degree. Consequently the Frattini quotient has order at least q².

This is the degree estimate used after the core-order calculation in
Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985), (10.9), p.163,
invoking the binary rank-one degree bound (5.7).
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace Representation.SL2
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
local instance characteristicTwoFrattiniAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The faithful Frattini action has at least the natural binary degree. -/
theorem characteristic_two_frattini_card_lower
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F)) (hF : 3 < Nat.card F) :
    Nat.card F ^ 2 ≤ Nat.card (pCore 2 H ⧸ frattini (pCore 2 H)) := by
  let Q := pCore 2 H
  let V := Q ⧸ frattini Q
  let : Fact (IsPGroup 2 Q) := ⟨pCore_isPGroup⟩
  let : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini
  let a : H →* MulAut V := (quotientAut (frattini Q)).comp MulAut.conjNormal
  have hk : a.ker = Q := pCore_frattini_action_kernel 2 hc
  let b := QuotientGroup.lift Q a hk.ge
  have hb : Function.Injective b := (QuotientGroup.injective_lift_iff _ _ _).mpr hk.symm
  let d := b.comp e.symm.toMonoidHom
  have hd : Function.Injective d := hb.comp e.symm.injective
  let ρ := FrattiniAction.ofAutomorphismHom d
  have hnt : ∃ g, ρ g ≠ 1 := by
    let g : SL(2,F) := ⟨!![1,1;0,1],by simp [Matrix.det_fin_two]⟩
    have hg : g ≠ 1 := by
      intro he
      have hh := congrArg (fun a : SL(2,F) => a.val 0 1) he
      simp [g] at hh
    have hne : ρ ≠ 1 := FrattiniAction.ofAutomorphismHom_ne_one d g
      (fun he => hg (hd (he.trans d.map_one.symm)))
    by_contra! hh
    exact hne (MonoidHom.ext hh)
  let n := Module.finrank (ZMod 2) F
  have hnF : Nat.card F = 2^n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hn : 1 < n := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [←hnF] at hp
    norm_num at hp
    omega
  have hl := fixedCodim_top_lower ρ hnt hn hnF
  have hd' := BinaryOffender.fixedCodim_add_finrank ρ ⊤
  have hm : 2*n ≤ Module.finrank (ZMod 2) (Additive V) := by omega
  have hV : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    change Nat.card (Additive V) = _
    simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V))
  rw [hnF,←pow_mul,hV]
  exact Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_comm] using hm)
end Representation.SL2
