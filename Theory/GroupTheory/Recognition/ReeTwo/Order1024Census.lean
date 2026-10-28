module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024ResidualRepresentatives
public import Theory.SpecificGroups.ReeTwo.CoreCharacterKernel
public import Theory.SpecificGroups.ReeTwo.SylowTailCoordinates
public import Theory.SpecificGroups.ReeTwo.TailQuotientOrder16Nodes
public import Theory.SpecificGroups.ReeTwo.TailQuotientOrder16Exhaustiveness
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024NodeIdentification

/-!
# The order-1024 census in the Ree two Sylow model

Every order-1024 subgroup contains the six-root tail and is the full preimage
of an order-sixteen subgroup in the explicit order-64 quotient. Thus a complete
list of quotient subgroups and identifications of their preimages prove the
order-1024 census: the canonical core, fifteen residual representatives and
three exceptional representatives, up to Sylow conjugacy. The checked quotient
classification proves this even without centricity; the centric statement is
also exposed for the residual-enumeration interface.

Source: the root and action formulas of Shinoda (1975), (2.3), pp. 81–82,
as checked in `ReeTwo.SylowTailQuotient`; the reduction is subgroup
correspondence for the quotient by the six-root tail.
-/

namespace ReeTwo.SylowModel

/-- Exhaustiveness and preimage identifications in the order-64 quotient
suffice for the census, even without a centricity assumption. -/
public theorem order1024_census_of_quotient_nodes
    (hcomplete : ∀ H : Subgroup TailQuotient.Group, Nat.card H = 16 →
      ∃ i : Fin 27, H = TailQuotient.Order16Nodes.node i)
    (hidentify : ∀ i : Fin 27,
      (TailQuotient.Order16Nodes.node i).comap TailQuotient.projection = coreSubgroup ∨
        (∃ (j : Fin 15) (g : SylowModel),
          (TailQuotient.Order16Nodes.node i).comap TailQuotient.projection =
            (residualCandidate j).map (MulAut.conj g).toMonoidHom) ∨
        ∃ (j : Fin 3) (g : SylowModel),
          (TailQuotient.Order16Nodes.node i).comap TailQuotient.projection =
            (exceptionalCandidate j).map (MulAut.conj g).toMonoidHom)
    (U : Subgroup SylowModel) (hU : Nat.card U = 1024) :
    U = coreSubgroup ∨
      (∃ (i : Fin 15) (g : SylowModel),
        U = (residualCandidate i).map (MulAut.conj g).toMonoidHom) ∨
      ∃ (i : Fin 3) (g : SylowModel),
        U = (exceptionalCandidate i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨i, hi⟩ := hcomplete (U.map TailQuotient.projection)
    (tailQuotient_image_card U hU)
  have hpre : U = (TailQuotient.Order16Nodes.node i).comap TailQuotient.projection := by
    rw [← hi, TailQuotient.comap_map U (tailSubgroup_le_of_card U hU)]
  rw [hpre]
  exact hidentify i

/-- Every order-1024 subgroup is conjugate to one of the nineteen representatives. -/
public theorem order1024_census
    (U : Subgroup SylowModel) (hU : Nat.card U = 1024) :
    U = coreSubgroup ∨
      (∃ (i : Fin 15) (g : SylowModel),
        U = (residualCandidate i).map (MulAut.conj g).toMonoidHom) ∨
      ∃ (i : Fin 3) (g : SylowModel),
        U = (exceptionalCandidate i).map (MulAut.conj g).toMonoidHom := by
  exact order1024_census_of_quotient_nodes TailQuotient.Order16Nodes.exhaustive
    Order1024NodeIdentification.node_preimage_identification U hU

/-- The explicit nineteen-representative census for centric order-1024 subgroups. -/
public theorem centric_order1024_census
    (U : Subgroup SylowModel)
    (_hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hU : Nat.card U = 1024) :
    U = coreSubgroup ∨
      (∃ (i : Fin 15) (g : SylowModel),
        U = (residualCandidate i).map (MulAut.conj g).toMonoidHom) ∨
      ∃ (i : Fin 3) (g : SylowModel),
        U = (exceptionalCandidate i).map (MulAut.conj g).toMonoidHom := by
  exact order1024_census U hU

end ReeTwo.SylowModel
