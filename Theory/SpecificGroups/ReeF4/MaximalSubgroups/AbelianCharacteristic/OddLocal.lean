module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal.Reduction

/-!
# Assembly of the odd-local Ree maximal-subgroup structure

Map the characteristic subgroup into the Ree carrier. Once the semisimple
reduction gives order three, the centralizer calculation gives SU₃ and a
proper normalizer acting nontrivially. Maximality identifies that normalizer
with the supplied maximal subgroup. Restrict its centralizer to this subgroup
to obtain the normal SU₃ layer, with quotient order two.

The finite-group assembly is proved here. The two geometric inputs remain
explicit premises; this module does not yet prove `oddLocalStructure`.
In particular, neither a source list nor a conditional matrix equivalence
discharges those inputs.

Sources: Malle, J. Algebra 139 (1991), 52–69, and GLS3, Table 4.7.3A;
see `OddLocal.Reduction` for parameter conventions and source paths.
-/

public section

namespace ReeF4.MaximalSubgroups.AbelianCharacteristic

open Subgroup BenderSuzuki.MatrixGroups

/-- Assemble the normal SU₃ layer from the two independent geometric inputs.
The final unconditional theorem must construct and supply both inputs. -/
theorem oddLocalStructure_of_cyclicReduction_threeCentralizers
    (hcyclic : OddLocal.CyclicReduction) (hcentralizers : OddLocal.ThreeCentralizers) :
    OddLocalStructure := by
  intro m hm M hM hnsol p hp hp₂ E hEc hEe hE
  let := hEc
  have hcardE := hcyclic m hm M hM hnsol p hp hp₂ E hEc hEe hE
  let A : Subgroup (Model m) := E.map M.subtype
  have hcardA : Nat.card A = 3 :=
    (Nat.card_congr (E.equivMapOfInjective M.subtype M.subtype_injective).toEquiv).symm.trans hcardE
  obtain ⟨hN, hC, F, hF, hFinite, J, hcard, hconj, ⟨e⟩⟩ :=
    hcentralizers m hm A hcardA
  let := hF
  let := hFinite
  have hNM : normalizer (A : Set (Model m)) = M :=
    OddLocal.normalizer_eq_of_isCoatom M hM E hN
  have hCM : centralizer (A : Set (Model m)) ≤ M :=
    hNM ▸ centralizer_le_normalizer (A : Set (Model m))
  let N : Subgroup M := (centralizer (A : Set (Model m))).subgroupOf M
  have hnormal : N.Normal := by
    dsimp only [N]
    rw [← hNM]
    infer_instance
  let := hnormal
  refine ⟨F, hF, hFinite, J, hcard, hconj, N, hnormal,
    ⟨(subgroupOfEquivOfLe hCM).trans e⟩, ?_⟩
  change N.index = 2
  dsimp only [N]
  rw [← hNM]
  exact OddLocal.centralizer_index_of_card_three A hcardA hC

end ReeF4.MaximalSubgroups.AbelianCharacteristic
