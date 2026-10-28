module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.Basic
public import Theory.GroupAction.CubicClassTwoFixed
public import Theory.GroupAction.SubgroupConjugation

/-!
# The cubic-action obstruction in J.2.3(7)

This file uses the literal subgroup Q ∩ C_G(B). Once its equality with
C_S(B), its order eight and its order-two intersection with V are known,
J.2.3(6) excludes commutativity. Choose a fixed element outside V: its
centralizer in S has index eight. If the fixed subgroup were abelian,
coprime fixed-point lifting would make the quotient fixed-point-free,
contradicting cubic orbit counting.

The equality and cardinalities must still be deduced from J.2.2(3).
Construction of the two cyclic-four lifts also remains separate. No
quaternion assertion is included in the Ru hypotheses. The earlier full
commutator premise is produced by `qt-j123-commutator-geometry`; the
preceding parabolic conclusions are produced by `qt-j12-parabolic-structure`.

Source: Aschbacher–Smith, J.2.3(7), printed p.434 (PDF p.445), combined
manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- The literal cubic fixed subgroup of Q. -/
def cubicFixedQ (d : TypeRuSetup G) (B : Sylow 3 d.L₁) : Subgroup G :=
  d.Q ⊓ centralizer (cubicSubgroup d B : Set G)

/-- The source odd-dimensional cubic-action contradiction, with the numerical
fixed-subgroup calculations still explicit. -/
theorem cubicFixedQ_not_commutative
    (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hfixed : cubicFixedQ d.toTypeRuSetup B =
      d.toTypeRuSetup.S ⊓ centralizer (cubicSubgroup d.toTypeRuSetup B : Set G))
    (hcard : Nat.card (cubicFixedQ d.toTypeRuSetup B) = 8)
    (hinter : Nat.card (cubicFixedQ d.toTypeRuSetup B ⊓ d.V : Subgroup G) = 2)
    (hfull : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V) :
    ¬ IsMulCommutative (cubicFixedQ d.toTypeRuSetup B) := by
  classical
  let D := d.toTypeRuSetup
  let A := cubicSubgroup D B
  let C := cubicFixedQ D B
  have hA : IsPGroup 3 A := B.isPGroup'.map D.L₁.subtype
  have hnorm : A ≤ normalizer D.S :=
    (cubicSubgroup_le_L D B).trans d.ru1.steinberg.normalized
  let _ : MulDistribMulAction A D.S := conjMulDistribMulActionOfLeNormalizer A D.S hnorm
  have hfix (x : D.S) : x ∈ FixedPoints.subgroup A D.S ↔ (x : G) ∈ centralizer (A : Set G) := by
    constructor
    · intro hx a ha
      have hh := congrArg Subtype.val (hx ⟨a,ha⟩)
      change a * (x : G) * a⁻¹ = x at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hx a
      apply Subtype.ext
      change (a : G) * (x : G) * (a : G)⁻¹ = x
      rw [hx a a.property, mul_inv_cancel_right]
  have hcop : Nat.Coprime (Nat.card A) (Nat.card D.S) := by
    exact IsPGroup.coprime_card_of_ne 3 2 (by decide) A D.S hA
      (isPGroup_pCoreIn 2 D.L)
  have hnil : Group.IsNilpotent D.S := (isPGroup_pCoreIn 2 D.L).isNilpotent
  let _ := hnil
  have ht : ∃ t : C, (t : G) ∉ d.V := by
    by_contra! hh
    have he : C ⊓ d.V = C := inf_eq_left.mpr (fun x hx => hh ⟨x,hx⟩)
    change Nat.card (C ⊓ d.V : Subgroup G) = 2 at hinter
    rw [he, hcard] at hinter
    omega
  obtain ⟨t, ht⟩ := ht
  have htSC : (t : G) ∈ D.S ⊓ centralizer (A : Set G) := hfixed ▸ t.property
  let tS : D.S := ⟨t, htSC.1⟩
  have hindex : (centralizer ({tS} : Set D.S)).index = 8 := by
    rw [d.ru1.centralizer_index_eq, hfull tS ht, d.ru1.card_V]
  obtain ⟨x, hx, htx⟩ := ClassTwo.exists_fixed_not_commute_of_index
    d.ru1.classTwo hA (inferInstance : Group.IsSolvable D.S) hcop tS
      ((hfix tS).mpr htSC.2) (by rw [hindex]; decide)
  have hxC : (x : G) ∈ C := by
    change (x : G) ∈ cubicFixedQ d.toTypeRuSetup B
    rw [hfixed]
    exact ⟨x.property, (hfix x).mp hx⟩
  intro hc
  let _ := hc
  apply htx
  apply Subtype.ext
  exact congrArg (fun y : C => (y : G)) (mul_comm t ⟨x,hxC⟩)
end CFSG.Quasithin.ChapterJ.SpecialCore
