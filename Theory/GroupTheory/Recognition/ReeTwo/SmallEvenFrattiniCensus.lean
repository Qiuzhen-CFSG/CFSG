module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentNodes
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalDescent
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeCertificates
public import Theory.GroupTheory.FrattiniNormalizerWitness
public import Theory.GroupTheory.SubgroupEnumerationDescending

/-!
# Assembly for the small even Frattini census

Descent starts at the parity kernel and retains centric subgroups not contained
in the core-character kernel. Both conditions pass to overgroups and are
invariant under conjugation, so a complete maximal-subgroup step certificate
covers every subgroup in the requested census. A separate finite node
certificate discards large nodes and nodes with outside Frattini normalizer
witnesses. Isomorphism transport transfers the latter exclusion back to the
original subgroup. The remaining nodes are the 59 prescribed representatives.

The checked maximal-descent and finite node certificates discharge both
inputs, giving unconditional coverage by the original 59 representatives.

Source: the finite maximal-chain argument in `SubgroupEnumerationDescending`
and the Shinoda (1975), (2.3), pp. 81–82 root model of `SmallEvenDescentNodes`.
-/

namespace ReeTwo.SylowModel
open Theory.GroupTheory.SubgroupEnumeration

private theorem not_le_coreCharacter_ker_map (U : Subgroup SylowModel)
    (g : SylowModel) (hU : ¬ U ≤ coreCharacter.ker) :
    ¬ U.map (MulAut.conj g).toMonoidHom ≤ coreCharacter.ker := by
  intro h
  apply hU
  intro x hx
  have hc := h (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
  have hh := (inferInstance : coreCharacter.ker.Normal).conj_mem _ hc g⁻¹
  simpa [MulAut.conj_apply, mul_assoc] using hh

/-- Maximal-subgroup coverage and concrete node certificates imply the original
small even census, with all five of its hypotheses unchanged. -/
public theorem smallEvenFrattiniCensus_of_descent_of_node_certificates
    (hstep : ∀ (i : Fin 600) (H : Subgroup SylowModel),
      H ⋖ smallEvenDescentNode i →
      Subgroup.centralizer (H : Set SylowModel) ≤ H → ¬ H ≤ coreCharacter.ker →
      Represented smallEvenDescentNode H)
    (hnode : ∀ i : Fin 600,
      1024 ≤ Nat.card (smallEvenDescentNode i) ∨
      (smallEvenDescentNode i).HasFrattiniNormalizerWitness ∨
      ∃ j : Fin 59, smallEvenDescentNode i = smallEvenCandidate j) :
    SmallEvenFrattiniCensus := by
  intro U hcent hcard hpar hnot hfr
  have hrep : Represented smallEvenDescentNode U :=
    represented_of_maximal_descent_below smallEvenDescentNode character.ker
      (fun H => Subgroup.centralizer (H : Set SylowModel) ≤ H ∧ ¬ H ≤ coreCharacter.ker)
      (fun H V hHV hH => ⟨centralizer_le_of_le hHV hH.1,
        fun hV => hH.2 (hHV.trans hV)⟩)
      (fun H g hH => ⟨centralizer_le_map H (MulAut.conj g) hH.1,
        not_le_coreCharacter_ker_map H g hH.2⟩)
      ⟨0, smallEvenDescentNode_zero⟩
      (fun i H hmax hH => hstep i H hmax hH.1 hH.2) U hpar ⟨hcent, hnot⟩
  obtain ⟨i, g, hg⟩ := hrep
  have hni : Nat.card (smallEvenDescentNode i) < 1024 := by
    rw [← hg]
    calc
      Nat.card (U.map (MulAut.conj g).toMonoidHom) = Nat.card U :=
        Nat.card_congr (U.equivMapOfInjective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).toEquiv.symm
      _ < 1024 := hcard
  have hfi : ¬ (smallEvenDescentNode i).HasFrattiniNormalizerWitness := by
    rw [← hg, Subgroup.hasFrattiniNormalizerWitness_map_iff]
    exact (Subgroup.not_hasFrattiniNormalizerWitness_iff U).mpr hfr
  rcases hnode i with hlarge | hw | ⟨j, hj⟩
  · exact (Nat.not_lt_of_ge hlarge hni).elim
  · exact (hfi hw).elim
  refine ⟨j, g⁻¹, ?_⟩
  rw [← hj, ← hg, Subgroup.map_map]
  have hid : (MulAut.conj g⁻¹).toMonoidHom.comp
      (MulAut.conj g).toMonoidHom = MonoidHom.id SylowModel := by
    apply MonoidHom.ext
    intro x
    change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x
    simp [mul_assoc]
  rw [hid, Subgroup.map_id]

/-- Every small centric subgroup in the parity kernel, outside the
core-character kernel, whose Frattini action has no outside normalizer
element is conjugate to one of the original 59 representatives. -/
public theorem smallEvenFrattiniCensus : SmallEvenFrattiniCensus :=
  smallEvenFrattiniCensus_of_descent_of_node_certificates
    smallEvenMaximalDescent smallEvenNodeCertificates

end ReeTwo.SylowModel
