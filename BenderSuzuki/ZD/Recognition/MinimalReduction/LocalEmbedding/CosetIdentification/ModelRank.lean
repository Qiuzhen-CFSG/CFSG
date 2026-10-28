module

public import BenderSuzuki.ZD.ProductClosedCentralFactor.ModelGeometry
public import BenderSuzuki.SE.PermutationQuotient

/-!
# Four-groups in odd extensions of simple Bender groups

The concrete PSL₂, Suzuki and PSU₃ converse constructions contain an
actual elementary abelian subgroup of order four. Transport it through
the multiplicative equivalence in `IsSimpleBenderGroup`, and lift across
the odd core using Schur–Zassenhaus. The unitary construction retains
both the matrix-field and fixed-field cardinalities.

This supplies the commuting pair in GLS, Volume 4, Chapter 2, Lemma 4.7(c);
see also Chapter 4, Section 3 for the Bender-group local structure.
-/

namespace BenderSuzuki.ZD.LocalCosetIdentification
open PFAppendixIII PFchapter1section1 _root_.BenderSuzuki.MatrixGroups

/-- Each of the actual simple Bender models contains an elementary four-group. -/
public theorem model_twoRank
    {G : Type*} [Group G] [Finite G] (hG : IsSimpleBenderGroup G) :
    TwoRankAtLeastTwo G := by
  rcases hG with ⟨⟨n, hn, e⟩⟩ | ⟨⟨n, hn, e⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, e⟩⟩
  · exact (Converse.hypothesisA_PSL2_binary n hn).A3.map_of_injective
      e.some.symm.toMonoidHom e.some.symm.injective
  · let : NeZero n := ⟨by omega⟩
    exact (Converse.hypothesisA_Sz n).A3.map_of_injective
      e.some.symm.toMonoidHom e.some.symm.injective
  · let : Field E := hEfield
    let : Finite E := hEfinite
    obtain ⟨_, rho, _, _, happly, _⟩ :=
      External.huppert_II_10_12 J (2 ^ n) hEcard hfixedCard hJ
    obtain ⟨H, D, Q, t, _, hA⟩ :=
      Converse.hypothesisA_psu3_general J hJ (2 ^ n) hEcard hfixedCard
        (by
          calc (2 : ℕ) < 2 ^ 2 := by norm_num
               _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
        ⟨n, rfl⟩ rho happly
    let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (Converse.psuOmega J) :=
      MulAction.compHom _ rho
    exact hA.A3.map_of_injective e.some.symm.toMonoidHom e.some.symm.injective

/-- The elementary four-group lifts across the genuine odd core. -/
public theorem twoRank_of_model_oddCore_quotient
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleBenderGroup (G ⧸ pPrimeCore 2 G)) : TwoRankAtLeastTwo G := by
  by_contra hrank
  exact not_twoRankAtLeastTwo_quotient_of_odd (pPrimeCore 2 G)
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hrank (model_twoRank hG)

end BenderSuzuki.ZD.LocalCosetIdentification
