module

public import Stellmacher.SectionTwo.LemmaTwoTwo

namespace Stellmacher.SectionTwo

universe u

/-! **Stellmacher (2.3).**  Here `B` is the *unbarred* subgroup
`C_S(Ω₁(Z(J(S))))` from the Section 2 notation, and `L = ⟨B^G⟩`.  The
quotient `\bar G` used in (2.2) is not part of this statement. -/
public theorem lemma_two_three
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcore : pCore 2 G =
      (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G))
    (B L : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓
      Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hL : L = Subgroup.normalClosure (B : Set G)) :
    ∃ P : Sylow 2 L, P.map L.subtype = B := by
  sorry

end Stellmacher.SectionTwo
