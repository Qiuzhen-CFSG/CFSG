module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024ResidualRepresentatives
public import Theory.SpecificGroups.ReeTwo.CoreCharacterKernel
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024Census
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024Automorphisms

/-!
# Assembly for the residual order-1024 Ree two enumeration

Every centric order-1024 subgroup is the canonical core, has a two-group
automorphism group, or is Sylow-conjugate to one of three exceptional
representatives. The checked census and automorphism results for its fifteen
residual representatives, including the parity-kernel cases, give this
alternative. Automorphism groups transport along the subgroup isomorphism
induced by conjugation.

The representatives use Shinoda (1975), (2.3), pp. 81–82, and the
verified root model in `ReeTwo.Sylow`.
-/

namespace ReeTwo.SylowModel

/-- Conjugating a subgroup preserves the two-group property of its automorphism group. -/
public theorem isPGroup_mulAut_map_conj (U : Subgroup SylowModel)
    (hU : IsPGroup 2 (MulAut U)) (g : SylowModel) :
    IsPGroup 2 (MulAut (U.map (MulAut.conj g).toMonoidHom)) := by
  let e := U.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact hU.of_equiv (MulAut.congr e)

/-- Separate census and automorphism results suffice for the residual enumeration. -/
public theorem residualEnumeration_of_census_of_isPGroup
    (hcensus : ∀ U : Subgroup SylowModel,
      Subgroup.centralizer (U : Set SylowModel) ≤ U → Nat.card U = 1024 →
      U = coreSubgroup ∨
        (∃ (i : Fin 15) (g : SylowModel),
          U = (residualCandidate i).map (MulAut.conj g).toMonoidHom) ∨
        ∃ (i : Fin 3) (g : SylowModel),
          U = (exceptionalCandidate i).map (MulAut.conj g).toMonoidHom)
    (ha : ∀ i : Fin 15, IsPGroup 2 (MulAut (residualCandidate i)))
    (U : Subgroup SylowModel)
    (hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hU : Nat.card U = 1024) :
    U = coreSubgroup ∨ IsPGroup 2 (MulAut U) ∨
      ∃ (i : Fin 3) (g : SylowModel),
        U = (exceptionalCandidate i).map (MulAut.conj g).toMonoidHom := by
  rcases hcensus U hc hU with hcore | ⟨i, g, rfl⟩ | hex
  · exact Or.inl hcore
  · exact Or.inr (Or.inl (isPGroup_mulAut_map_conj _ (ha i) g))
  · exact Or.inr (Or.inr hex)

/-- The residual classification of centric order-1024 subgroups: the core,
a two-group automorphism group, or one of the three exceptions up to conjugacy. -/
public theorem residualEnumeration
    (U : Subgroup SylowModel)
    (hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hU : Nat.card U = 1024) :
    U = coreSubgroup ∨ IsPGroup 2 (MulAut U) ∨
      ∃ (i : Fin 3) (g : SylowModel),
        U = (exceptionalCandidate i).map (MulAut.conj g).toMonoidHom :=
  residualEnumeration_of_census_of_isPGroup centric_order1024_census
    residualCandidate_isPGroup_mulAut U hc hU

end ReeTwo.SylowModel
