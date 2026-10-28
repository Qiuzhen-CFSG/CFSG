module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusNodes
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusSteps
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusNodeChecks
public import Theory.GroupTheory.FrattiniNormalizerWitness
public import Theory.GroupTheory.SubgroupEnumerationDescending

/-!
# Assembly of the Ree two parity census

Descending coverage outside the parity kernel and local Frattini-witness
checks on the fixed 131-node family suffice for the nineteen-candidate
census. Centricity and noncontainment in the parity kernel pass to overgroups
and conjugates. The absence of an outside Frattini witness transports to
each representative; the cardinality hypothesis excludes large nodes.

The imported maximal-step and node certificates discharge both finite checks
in `smallParityCensus`. Frattini failures exclude nodes as answers but do not
remove those nodes from the descent.

Source: the maximal-chain argument in `SubgroupEnumerationDescending` and
the Shinoda (1975) root words in `SmallParityCensusNodes`.
-/

namespace ReeTwo.SylowModel
open Theory.GroupTheory.SubgroupEnumeration

private theorem not_le_character_ker_map (U : Subgroup SylowModel)
    (g : SylowModel) (hU : ¬ U ≤ character.ker) :
    ¬ U.map (MulAut.conj g).toMonoidHom ≤ character.ker := by
  intro h
  apply hU
  intro x hx
  have hc := h (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
  have hh := (inferInstance : character.ker.Normal).conj_mem _ hc g⁻¹
  simpa [MulAut.conj_apply, mul_assoc] using hh

/-- Maximal-step coverage and independent local exclusions imply the exact
small parity census. Neither input presupposes intrinsic radicality. -/
public theorem smallParityCensus_of_maximal_steps_of_node_checks
    (hstep : ∀ (i : Fin 131) (H : Subgroup SylowModel),
      H ⋖ smallParityCensusNode i →
      Subgroup.centralizer (H : Set SylowModel) ≤ H →
      ¬ H ≤ character.ker → Represented smallParityCensusNode H)
    (hcheck : ∀ i : Fin 131, Nat.card (smallParityCensusNode i) < 1024 →
      (smallParityCensusNode i).HasFrattiniNormalizerWitness ∨
        ∃ j : Fin 19, smallParityCensusNode i = smallParityCandidate j)
    (U : Subgroup SylowModel)
    (hcent : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hcard : Nat.card U < 1024)
    (hfr : ∀ g : Subgroup.normalizer (U : Set SylowModel),
      Subgroup.quotientAut (frattini U) (U.normalizerMonoidHom g) = 1 →
        (g : SylowModel) ∈ U) :
    U ≤ character.ker ∨ ∃ (i : Fin 19) (g : SylowModel),
      U.map (MulAut.conj g).toMonoidHom = smallParityCandidate i := by
  classical
  by_cases hp : U ≤ character.ker
  · exact Or.inl hp
  have hrep : Represented smallParityCensusNode U :=
    represented_of_maximal_descent smallParityCensusNode
      (fun H => Subgroup.centralizer (H : Set SylowModel) ≤ H ∧ ¬ H ≤ character.ker)
      (fun H V hHV hH => ⟨centralizer_le_of_le hHV hH.1,
        fun hV => hH.2 (hHV.trans hV)⟩)
      (fun H g hH => ⟨centralizer_le_map H (MulAut.conj g) hH.1,
        not_le_character_ker_map H g hH.2⟩)
      ⟨0, smallParityCensusNode_zero⟩
      (fun i H hmax hH => hstep i H hmax hH.1 hH.2) U ⟨hcent, hp⟩
  obtain ⟨i, g, hg⟩ := hrep
  have hn : Nat.card (smallParityCensusNode i) < 1024 := by
    rw [← hg, Nat.card_congr
      (U.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv.symm]
    exact hcard
  rcases hcheck i hn with hw | ⟨j, hj⟩
  · have hf : ¬ (smallParityCensusNode i).HasFrattiniNormalizerWitness := by
      rw [← hg, Subgroup.hasFrattiniNormalizerWitness_map_iff]
      exact (Subgroup.not_hasFrattiniNormalizerWitness_iff U).mpr hfr
    exact (hf hw).elim
  · exact Or.inr ⟨j, g, hg.trans hj⟩

/-- Every small centric subgroup with no outside Frattini normalizer witness
lies in the parity kernel or is conjugate to one of the nineteen candidates. -/
public theorem smallParityCensus
    (U : Subgroup SylowModel)
    (hcent : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hcard : Nat.card U < 1024)
    (hfr : ∀ g : Subgroup.normalizer (U : Set SylowModel),
      Subgroup.quotientAut (frattini U) (U.normalizerMonoidHom g) = 1 →
        (g : SylowModel) ∈ U) :
    U ≤ character.ker ∨ ∃ (i : Fin 19) (g : SylowModel),
      U.map (MulAut.conj g).toMonoidHom = smallParityCandidate i := by
  exact smallParityCensus_of_maximal_steps_of_node_checks
    smallParityCensusStep smallParityCensusNode_checks U hcent hcard hfr

end ReeTwo.SylowModel
