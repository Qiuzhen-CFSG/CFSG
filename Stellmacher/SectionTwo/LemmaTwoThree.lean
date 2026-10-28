module

public import Stellmacher.SectionTwo.TwoThreeCentralizingCase
public import Stellmacher.SectionTwo.TwoThreeOppositeConjugate
public import Stellmacher.SectionTwo.CoreBaumannOpposite
public import Stellmacher.SectionTwo.TwoThreeSylowReduction

/-!
# Stellmacher (2.3): Sylow control in the Baumann normal closure

Under the Section 2 hypotheses and the equality `O₂(G) = C_S(V)`, the
Baumann subgroup `B = C_S(Ω₁(Z(J(S))))` is a Sylow 2-subgroup of its
normal closure `L`.

If `V` centralizes `J(S)`, the proved centralizing case makes `B` normal and
finishes immediately. Otherwise the factor/module decomposition of (2.2)
provides one opposite conjugate `J(S)ˣ`: the two conjugates generate the
Thompson normal closure modulo `C_G(V)`, and their fixed spaces span `V`.
The omega-core replacement and centralizer arguments then put `O₂(E)` in
`B`, where `E` is the normal closure of `J(S)`. The final quotient and normal
supplement reduction proves that `S ∩ L = B` and transports this intersection
to a Sylow subgroup of `L`.

This follows Stellmacher, Journal of Algebra 190 (1997), result (2.3), p. 20;
see `refs/latex/stellmacher-n-group.tex`. The source scan confirms that the
supplement is `L = E B` with unbarred `B`, and that `C_E(V)` acts trivially on
the relevant quotient rather than on the whole omega supplement.
-/

namespace Stellmacher.SectionTwo

universe u

/-- **Stellmacher (2.3).** Here `B` is the unbarred subgroup from the Section 2
notation and `L = ⟨B^G⟩`; the quotient used in the proof is not part of the
public statement. -/
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
  by_cases hcent : vSubgroup S ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G)
  · exact lemma_two_three_of_v_centralizes_j h S hcore B L hB hL hcent
  · obtain ⟨x, hx, hgen, hspan⟩ := two_three_opposite_conjugate h S hcent
    apply two_three_sylow_of_core_le_baumann h S hcore B L hB hL
    rw [hB]
    exact two_three_core_le_baumann_of_opposite h S hcore hcent x hx
      (by simpa only [cSubgroup] using hgen) hspan.le

end Stellmacher.SectionTwo
