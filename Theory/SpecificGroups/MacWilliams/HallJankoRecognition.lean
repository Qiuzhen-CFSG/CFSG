module

public import Theory.SpecificGroups.MacWilliams.HallJankoCenter
public import Theory.SpecificGroups.MacWilliams.UnitaryRecognition

/-!
# Recognition from the Hall–Janko generating relations

The certified order of the seven-generator presentation is 128. A generating
tuple satisfying its power and commutator relations therefore identifies any
group of order at least 128 with that presentation: the universal homomorphism
is surjective, and the order comparison makes it injective.

This isolates the presentation argument in the Hall–Janko alternative of
Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386, citing
MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
Constructing the tuple from Sylow hypotheses remains a separate obligation.
-/

namespace MacWilliamsSylow

/-- Generating Hall–Janko relations and the order lower bound suffice for
recognition; no external identification of the presentation is assumed. -/
public theorem nonempty_hallJanko_equiv_of_generators
    {P : Type*} [Group P] (hcard : 128 ≤ Nat.card P)
    (x : Fin 7 → P) (hrel : Relations hallJankoTable x)
    (hgen : Subgroup.closure (Set.range x) = ⊤) :
    Nonempty (P ≃* HallJankoSylow) := by
  exact ⟨(presentationEquivOfCardLE hrel hgen
    (hallJankoSylow_card.symm ▸ hcard)).symm⟩

end MacWilliamsSylow
