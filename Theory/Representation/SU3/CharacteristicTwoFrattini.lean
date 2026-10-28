module
public import Theory.Representation.SU3.BinaryDegree
public import Theory.Representation.FrattiniAction
public import Theory.GroupTheory.PCoreFrattiniAction


/-!
# The unitary degree bound on a self-centralizing core

The quotient by a self-centralizing two-core acts faithfully on the
core's Frattini quotient. Transport that action to the marked special
unitary group, or pull it back along the literal scalar projection in the
projective case. The nonbinary unitary degree bound forces dimension at
least six times the fixed-field degree. No irreducibility assumption or
natural-module identification is needed.

The Chapter 11 consumer identifies the Frattini subgroup with its actual
beta center and combines this bound with three-neighbor generation.
Source: DGS85, Groups and Graphs (1985), (5.7), p.108, and (11.8), p.176;
the degree argument and its sources are given in SU3.BinaryDegree.
-/

public noncomputable section
open Subgroup Representation BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Representation.SU3
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

/-- A marked unitary quotient forces the full natural lower bound on the
actual Frattini quotient of the self-centralizing two-core. -/
theorem characteristic_two_frattini_card_lower
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : Nonempty ((H ⧸ pCore 2 H) ≃* J.specialSubgroup) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    2^(6*n) ≤ Nat.card (pCore 2 H ⧸ frattini (pCore 2 H)) := by
  let Q := pCore 2 H
  let V := Q ⧸ frattini Q
  let : Fact (IsPGroup 2 Q) := ⟨pCore_isPGroup⟩
  let : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini
  let a : H →* MulAut V := (quotientAut (frattini Q)).comp MulAut.conjNormal
  have hk : a.ker = Q := pCore_frattini_action_kernel 2 hc
  let b := QuotientGroup.lift Q a hk.ge
  have hb : Function.Injective b := (QuotientGroup.injective_lift_iff _ _ _).mpr hk.symm
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
  have hq : 2 < 2^n := (by decide : 2 < 2^2).trans_le
    (Nat.pow_le_pow_right (by decide) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J (2^n) hq hF hf
  obtain ⟨z,hz⟩ := exists_ne (1 : ProjectiveSpecialUnitaryMatrixGroup J)
  obtain ⟨x,hx⟩ := J.specialToProjective_surjective z
  have hdim : 6*n ≤ Module.finrank (ZMod 2) (Additive V) := by
    rcases e with he | he
    · obtain ⟨e⟩ := he
      let d := b.comp e.symm.toMonoidHom
      let ρ := FrattiniAction.ofAutomorphismHom d
      have hmove : d x ≠ 1 := by
        intro he
        have hx1 : x = 1 := e.symm.injective (hb (he.trans d.map_one.symm))
        exact hz (by rw [←hx,hx1,map_one])
      have hnt : ∃ g, ρ g ≠ 1 := by
        by_contra! hh
        exact FrattiniAction.ofAutomorphismHom_ne_one d x hmove (MonoidHom.ext hh)
      exact BinaryDegree.finrank_ge J hn hF hconj ρ hnt
    · obtain ⟨e⟩ := he
      let d := b.comp (e.symm.toMonoidHom.comp J.specialToProjective)
      let ρ := FrattiniAction.ofAutomorphismHom d
      have hmove : d x ≠ 1 := by
        intro he
        have he' : b (e.symm (J.specialToProjective x)) = b (e.symm 1) := by
          simpa only [d,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_one] using he
        exact hz (hx ▸ e.symm.injective (hb he'))
      have hnt : ∃ g, ρ g ≠ 1 := by
        by_contra! hh
        exact FrattiniAction.ofAutomorphismHom_ne_one d x hmove (MonoidHom.ext hh)
      exact BinaryDegree.finrank_ge J hn hF hconj ρ hnt
  have hV : Nat.card V = 2^Module.finrank (ZMod 2) (Additive V) := by
    change Nat.card (Additive V) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [hV]
  exact Nat.pow_le_pow_right (by decide) hdim
end Representation.SU3
