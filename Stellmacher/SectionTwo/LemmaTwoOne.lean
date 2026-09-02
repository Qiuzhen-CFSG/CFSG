module

public import Stellmacher.SectionsOneToFourDefs


namespace Stellmacher.SectionTwo

universe u

public structure Hypotheses
    (G : Type u) [Group G] [Finite G] : Prop where
  solvable : Group.IsSolvable G
  even_order : Even (Nat.card G)
  centralizer_twoCore_le :
    Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G

/-! **Stellmacher (2.1).**  `\bar G=G/C_G(V)` has trivial `2`-core.  The
surjective-kernel presentation keeps the quotient explicit without relying on
a global normality instance for the notation `C_G(V)`. -/
public theorem lemma_two_one
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q)
    (hker : q.ker = cSubgroup S) :
    pCore 2 barG = ⊥ := by
  sorry

end Stellmacher.SectionTwo
