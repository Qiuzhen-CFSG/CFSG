module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CenterOrbits.Square
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CenterOrbits.SevenWeights

/-!
# Center placement and square conjugators for the irreducible alternatives

The three natural-module alternatives construct h in H and l in L₂T
with A^h=V₁^l and l² in H. The linear-four and symmetric-six cases use
nonzero-vector transitivity in the actual quotient U/V₁. The symmetric-seven
case derives weight two from the nontrivial center displacement, then uses
the literal marking in 13.7.6(3b). Each orbit lifts to A^h ≤ V₂ before the
marked plane involutions construct l. Every model identification contains
both an actual group equivalence and an intertwining linear equivalence.
The linear case uses GL₄(F₂) on F₂⁴.

Earlier source inputs remain explicit: H=C_G(z), V₁=⟨z⟩, order two and
disjointness of A from V₁ (endpoint transport/F.9), V₁ ≤ V₂ and a nonzero
vector of V₂/V₁ (Notation 13.2.1), the conjugation-module identifications of
13.8.5, and the marked natural V/parabolic action described in `Square`.
For source use set U=U_H and A=V₁^g. F.9.2(3) identifies the quotient action
image with H/O₂(H). These theorems need no further 13.8.6 conclusion.

For S₇ the additional earlier inputs are the nontrivial displacement with
center A (the transported F.9.16(1i) configuration) and the vector e₅,₆ in
13.7.6(3b), expressed in zero-based coordinates 4 and 5. The combined theorem
`center_conjugator_irreducible` handles all three alternatives. It constructs
the witnesses; the parent source theorem still supplies these earlier inputs
and uses the interchange obstruction to finish the irreducible cases.

Source: Aschbacher–Smith, 13.8.7, printed pp.948–949.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G : Type*} [Group G]
variable {H U V V₂ L₂ T : Subgroup G}
  [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]

/-- Placement in V₂ feeds the explicit parabolic construction. -/
theorem center_conjugator_of_placement
    (P : MarkedPlaneAction L₂ T V V₂) (A : Subgroup G) (z : V)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hz : P.moduleEquiv (Additive.ofMul z) = pairVector 4 5)
    (hcard : Nat.card A = 2)
    (hplace : ∃ h ∈ H, A.conjBy h ≤ V₂) :
    ∃ h ∈ H, ∃ l ∈ L₂ ⊔ T,
      A.conjBy h = (zpowers (z : G)).conjBy l ∧ l ^ 2 ∈ H := by
  obtain ⟨h, hh, hA⟩ := hplace
  have hc : Nat.card (A.conjBy h) = 2 :=
    (Nat.card_congr ((MulAut.conj h).subgroupMap A).toEquiv).symm.trans hcard
  obtain ⟨l, hl, he, hs⟩ := P.square_conjugator H (A.conjBy h) z hH hz hA hc
  exact ⟨h, hh, l, hl, he, hs⟩

variable (z : V) [((zpowers (z : G)).subgroupOf U).Normal]

/-- The natural four-dimensional binary linear action used in the L₄(2) case. -/
abbrev linearFourRepresentation :
    Representation (ZMod 2)
      ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) (Fin 4 → ZMod 2) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom

/-- Condition (*) and its square conjugator in the natural L₄(2) alternative. -/
theorem center_conjugator_linear
    (Q : CenterQuotientAction H U (zpowers (z : G)))
    (M : Q.Model linearFourRepresentation)
    (P : MarkedPlaneAction L₂ T V V₂) (A : Subgroup G)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hz : P.moduleEquiv (Additive.ofMul z) = pairVector 4 5)
    (hA : A ≤ U) (hcard : Nat.card A = 2)
    (hdisj : A ⊓ zpowers (z : G) = ⊥) (hZ : zpowers (z : G) ≤ V₂)
    (b : U) (hb : (b : G) ∈ V₂) (hbZ : (b : G) ∉ zpowers (z : G)) :
    ∃ h ∈ H, ∃ l ∈ L₂ ⊔ T,
      A.conjBy h = (zpowers (z : G)).conjBy l ∧ l ^ 2 ∈ H := by
  apply center_conjugator_of_placement P A z hH hz hcard
  exact Q.place_of_nonzero_transitive M
    CenterQuotientAction.linear_nonzero_transitive A V₂ hA hcard hdisj hZ b hb hbZ

/-- Condition (*) and its square conjugator in the natural S₆ alternative. -/
theorem center_conjugator_six
    (Q : CenterQuotientAction H U (zpowers (z : G)))
    (M : Q.Model (BinaryPermutation.naturalRepresentation (Fin 6)))
    (P : MarkedPlaneAction L₂ T V V₂) (A : Subgroup G)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hz : P.moduleEquiv (Additive.ofMul z) = pairVector 4 5)
    (hA : A ≤ U) (hcard : Nat.card A = 2)
    (hdisj : A ⊓ zpowers (z : G) = ⊥) (hZ : zpowers (z : G) ≤ V₂)
    (b : U) (hb : (b : G) ∈ V₂) (hbZ : (b : G) ∉ zpowers (z : G)) :
    ∃ h ∈ H, ∃ l ∈ L₂ ⊔ T,
      A.conjBy h = (zpowers (z : G)).conjBy l ∧ l ^ 2 ∈ H := by
  apply center_conjugator_of_placement P A z hH hz hcard
  exact Q.place_of_nonzero_transitive M
    SixCenterGeometry.nonzero_transitive A V₂ hA hcard hdisj hZ b hb hbZ

/-- Condition (*) and its square conjugator in the natural S₇ alternative.
The center weight is proved from its displacement, not assumed. -/
theorem center_conjugator_seven
    (Q : CenterQuotientAction H U (zpowers (z : G)))
    (M : Q.Model (BinaryPermutation.coreRepresentation (Fin 7)))
    (P : MarkedPlaneAction L₂ T V V₂) (A : Subgroup G)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hz : P.moduleEquiv (Additive.ofMul z) = pairVector 4 5)
    (hA : A ≤ U) (hcard : Nat.card A = 2)
    (hc : Q.IsNontrivialCenter A) (hZ : zpowers (z : G) ≤ V₂)
    (b : U) (hb : (b : G) ∈ V₂)
    (hmarked : (M.moduleEquiv (CenterQuotientAction.vector b)).val =
      Pi.single (4 : Fin 7) 1 + Pi.single 5 1) :
    ∃ h ∈ H, ∃ l ∈ L₂ ⊔ T,
      A.conjBy h = (zpowers (z : G)).conjBy l ∧ l ^ 2 ∈ H := by
  apply center_conjugator_of_placement P A z hH hz hcard
  exact place_seven_center Q M A V₂ hA hcard hc hZ b hb hmarked

/-- The complete center-orbit and square-conjugator construction for the three
irreducible alternatives of 13.8.7. The alternatives are actual equivariant
models of the quotient conjugation action; only the S₇ case needs the marked
weight-two vector from 13.7.6(3b). For the transported endpoint use A=V₁^g. -/
theorem center_conjugator_irreducible
    (Q : CenterQuotientAction H U (zpowers (z : G)))
    (P : MarkedPlaneAction L₂ T V V₂) (A : Subgroup G)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hz : P.moduleEquiv (Additive.ofMul z) = pairVector 4 5)
    (hA : A ≤ U) (hcard : Nat.card A = 2)
    (hdisj : A ⊓ zpowers (z : G) = ⊥)
    (hc : Q.IsNontrivialCenter A) (hZ : zpowers (z : G) ≤ V₂)
    (b : U) (hb : (b : G) ∈ V₂) (hbZ : (b : G) ∉ zpowers (z : G))
    (hmodels : Nonempty (Q.Model linearFourRepresentation) ∨
      Nonempty (Q.Model (BinaryPermutation.naturalRepresentation (Fin 6))) ∨
      ∃ M : Q.Model (BinaryPermutation.coreRepresentation (Fin 7)),
        (M.moduleEquiv (CenterQuotientAction.vector b)).val =
          Pi.single (4 : Fin 7) 1 + Pi.single 5 1) :
    ∃ h ∈ H, ∃ l ∈ L₂ ⊔ T,
      A.conjBy h = (zpowers (z : G)).conjBy l ∧ l ^ 2 ∈ H := by
  rcases hmodels with hlinear | hsix | ⟨M, hmarked⟩
  · obtain ⟨M⟩ := hlinear
    exact center_conjugator_linear z Q M P A hH hz hA hcard hdisj hZ b hb hbZ
  · obtain ⟨M⟩ := hsix
    exact center_conjugator_six z Q M P A hH hz hA hcard hdisj hZ b hb hbZ
  · exact center_conjugator_seven z Q M P A hH hz hA hcard hc hZ b hb hmarked

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair

end
