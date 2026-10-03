module
public import Stellmacher.QuotientModuleFixedPoints
public import Stellmacher.QuotientModuleImageCard
public import Stellmacher.SectionOne.LemmaOneFiveRelativeM

/-!
# The faithful quotient index bound

For an elementary abelian ambient subgroup Y acting on V, a centralizer
quotient satisfying Section 1's hypotheses obeys
|Y| |C_V(Y)| ≤ |V| |C_Y(V)|. Thus the index of the vector fixed points
is at least the order of the faithful actor image.

The image of Y is elementary abelian and lies in some Sylow 2-subgroup.
The proved relative form of Stellmacher (1.5)(e) gives its module measure
at least one. The quotient-module fixed-point bridge identifies the vector
factor, and the kernel-image cardinal formula identifies the actor factor.
Multiplication yields the ambient inequality without quotient division.

This is the counting step used symmetrically at the two endpoints in
Stellmacher (8.1)(a), journal p.37. All Section 1 hypotheses remain explicit,
and the action is exactly the one specified by the quotient-module witness.
-/

namespace Stellmacher.Later

universe u

/-- The Section 1 lower bound transported to ambient subgroup indices. -/
public theorem QuotientModuleWitness.index_bound
    {G : Type u} [Group G] [Finite G] {A V : Subgroup G}
    [IsElementaryAbelian 2 V]
    (w : QuotientModuleWitness A (A ⊓ Subgroup.centralizer (V : Set G)) V)
    (Y : Subgroup G) (hYA : Y ≤ A) [IsElementaryAbelian 2 Y] :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom V w.action
    SectionOne.Hypotheses w.X V →
      Nat.card Y * Nat.card (V ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) ≤
        Nat.card V * Nat.card (Y ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom V w.action
  dsimp only
  intro h
  let Yb : Subgroup w.X := (Y.subgroupOf A).map w.projection
  let : IsElementaryAbelian 2 (Y.subgroupOf A) := IsElementaryAbelian.subgroupOf hYA
  let : IsElementaryAbelian 2 Yb := IsElementaryAbelian.map w.projection
  obtain ⟨T, hYT⟩ := (IsElementaryAbelian.isPGroup 2 Yb).exists_le_sylow
  have hm := SectionOne.lemma_one_five_m_ge_one_relative h T Yb hYT inferInstance
  have hpos : (0 : ℚ) <
      (Nat.card (FixedPoints.subgroup Yb V) : ℚ) * (Nat.card Yb : ℚ) :=
    mul_pos (by exact_mod_cast Nat.card_pos) (by exact_mod_cast Nat.card_pos)
  have hprod : Nat.card (FixedPoints.subgroup Yb V) * Nat.card Yb ≤ Nat.card V := by
    have hh := (le_div_iff₀ hpos).mp hm
    simp only [one_mul] at hh
    exact_mod_cast hh
  have hfix := w.fixedPoints_card Y hYA
  change Nat.card (FixedPoints.subgroup Yb V) = _ at hfix
  rw [hfix] at hprod
  let K : Subgroup G := Y ⊓ Subgroup.centralizer (V : Set G)
  have hcard := w.image_card_mul_centralizer_card Y hYA
  change Nat.card Yb * Nat.card K = Nat.card Y at hcard
  have hmul := Nat.mul_le_mul_right (Nat.card K) hprod
  change Nat.card Y * Nat.card (V ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) ≤
    Nat.card V * Nat.card K
  nlinarith

end Stellmacher.Later
