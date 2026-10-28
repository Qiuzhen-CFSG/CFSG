module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData
public import Theory.SpecificGroups.Held.LocalPairs.Faithfulness
public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!
# Transport and contracts for the inner Held involution rows

GLS3 Table 5.3p (printed p.277), interpreted on pp.260–261, gives a
perfect central cover `E₄.L₃(4)` of index two in the 2A centralizer, and
order 21504 for the 2B centralizer. The quotient-sensitive contract below
retains the actual normal subgroup and its isomorphism to the matrix
`PSL₃(4)` after dividing by its center. It implies the original contract
used in the A₆ component exclusion without changing its witness.

The proposed representatives are the literal ATLAS generator `Held.a` and
`max5First ^ 4`. Their row calculations and exhaustive conjugacy coverage
are separate obligations, not consequences of these definitions. The
transport results use group isomorphisms and the proved centerlessness of
the degree-2058 Held carrier; no simplicity or global order is needed.

Consumers: Aschbacher–Smith, Theorem C (printed p.33) and E.6.18/E.6.23
(printed pp.252/254), with the separate Held actor-bound repair for E.6.18.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Held.InvolutionFixedData

/-- Actual normal central cover in the 2A row, retaining the central quotient. -/
def HasPSL3FourNormalOfIndexTwo (G : Type*) [Group G] : Prop :=
  ∃ D : Subgroup G, D.Normal ∧ IsQuasisimple D ∧ D.index = 2 ∧
    Nat.card (center D) = 4 ∧ Nonempty ((D ⧸ center D) ≃* Matrix.PSL3Four.PSL)

/-- The stronger row data consumed by both the six- and seven-component arguments. -/
def InnerRowsWithQuotient : Prop :=
  ∀ g : He, orderOf (MulAut.conj g) = 2 →
    HasPSL3FourNormalOfIndexTwo (MulAut.conj g).fixedSubgroup ∨
      Nat.card (MulAut.conj g).fixedSubgroup = 21504

/-- Every involution is conjugate to one of the two concrete proposed representatives.
This definition is an obligation; no conjugacy coverage is asserted here. -/
def InnerInvolutionCoverage : Prop :=
  ∀ g : He, orderOf g = 2 →
    (∃ c : He, MulAut.conj c a = g) ∨
      (∃ c : He, MulAut.conj c (TwoLocalCandidates.max5First ^ 4) = g)

variable {G H : Type*} [Group G] [Group H]

/-- Forgetting the central-quotient identification preserves the same witness. -/
theorem HasPSL3FourNormalOfIndexTwo.forget
    (h : HasPSL3FourNormalOfIndexTwo G) : HasQuasisimpleNormalOfIndexTwo G 4 := by
  obtain ⟨D, hn, hq, hi, hz, _⟩ := h
  exact ⟨D, hn, hq, hi, hz⟩

/-- An isomorphism transports the normal subgroup and its actual central quotient. -/
theorem HasPSL3FourNormalOfIndexTwo.of_mulEquiv
    (h : HasPSL3FourNormalOfIndexTwo G) (e : G ≃* H) :
    HasPSL3FourNormalOfIndexTwo H := by
  obtain ⟨D, hn, hq, hi, hz, ⟨q⟩⟩ := h
  let : D.Normal := hn
  let : IsQuasisimple D := hq
  let D' := D.map e.toMonoidHom
  let d : D ≃* D' := e.subgroupMap D
  have hcenter : (center D).map d.toMonoidHom = center D' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr d ⟨x, hx⟩).property
    · intro x hx
      exact ⟨d.symm x, ((Subgroup.centerCongr d).symm ⟨x, hx⟩).property,
        d.apply_symm_apply x⟩
  refine ⟨D', hn.map e.toMonoidHom e.surjective,
    IsQuasisimple.of_mulEquiv d, (D.index_map_equiv e).trans hi, ?_, ?_⟩
  · exact (Nat.card_congr (Subgroup.centerCongr d).toEquiv).symm.trans hz
  · exact ⟨(QuotientGroup.congr _ _ d hcenter).symm.trans q⟩

/-- Centerlessness makes the order of inner conjugation exactly the element order. -/
theorem orderOf_conj (g : He) : orderOf (MulAut.conj g) = orderOf g :=
  orderOf_injective MulAut.conj
    (Theory.GroupTheory.conj_injective_of_center_eq_bot Held.LocalPairs.center_eq_bot) g

/-- Automorphisms restrict to actual equivalences between element fixed subgroups. -/
def innerFixedEquiv (e : MulAut He) (g : He) :
    (MulAut.conj g).fixedSubgroup ≃* (MulAut.conj (e g)).fixedSubgroup := by
  exact (MulAut.fixedSubgroupCongr e (MulAut.conj g)).trans
    (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup (MulAut.congr_conj e g)))

/-- The stronger inner rows give the original public contract. -/
theorem InnerRowsWithQuotient.forget (h : InnerRowsWithQuotient) : InnerRows := by
  intro g hg
  exact (h g hg).imp HasPSL3FourNormalOfIndexTwo.forget id

end Held.InvolutionFixedData
