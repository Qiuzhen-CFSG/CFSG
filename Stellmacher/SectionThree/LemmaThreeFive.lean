module

public import Stellmacher.SectionThree.LemmaThreeFiveOmega

/-!
# Stellmacher (3.5): the central commutator dichotomy

For solvable `P ∈ ℘(S)` and `N ◁ P` contained in `O₂(P)`, centralization
of `O₂(P) ∩ O²(P)` implies that either `Z(S)` fails to centralize `O²(P)`
or `N` centralizes it.  This preserves the original source-facing interface.

The proof applies the stronger omega-center dichotomy and the containment
`Ω₁(Z(S)) ≤ Z(S)`.  Its coprime-action argument and order-two central witness
are developed in `LemmaThreeFiveOmega`.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), Lemma (3.5), p. 22; `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionThree

universe u

/-- **Stellmacher (3.5).** -/
public theorem lemma_three_five
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (N : Subgroup G)
    (hN : N ≤ P ∧ N ≤ twoCoreAmbient P ∧ (N.subgroupOf P).Normal)
    (hsolv : Group.IsSolvable P)
    (hcentral : ⁅N, twoCoreAmbient P ⊓ twoResidualAmbient P⁆ = ⊥) :
    ⁅(Subgroup.center S).map S.subtype, twoResidualAmbient P⁆ ≠ ⊥ ∨
      ⁅N, twoResidualAmbient P⁆ = ⊥ := by
  rcases lemma_three_five_omega S h P hP N hN hsolv hcentral with hOmega | hNcomm
  · left
    intro hcenter
    apply hOmega
    apply le_bot_iff.mp
    rw [← hcenter]
    apply Subgroup.commutator_mono _ le_rfl
    exact Subgroup.map_mono
      (Subgroup.map_subtype_le (omega₁ (G := Subgroup.center S) (p := 2)))
  · exact Or.inr hNcomm

end Stellmacher.SectionThree
