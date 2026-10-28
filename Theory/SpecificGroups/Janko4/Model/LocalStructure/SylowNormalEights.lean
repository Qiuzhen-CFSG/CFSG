module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Catalogue
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.MatrixWords
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.MatrixRealization
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles

/-!
# Normal eights and centralizer invariants in the literal matrix two-group

The presentation has order at most 2²¹ by a proved binary collection argument.
The actual matrix subgroup has order exactly 2²¹. Therefore any *surjective
homomorphism* from the presentation to that subgroup is an isomorphism. This
requires literal generator relations and generation; equality of orders alone
does not identify the groups.

The checked literal relations and generation construct `matrixEquiv`, which
discharges the order premise of the presentation's profile calculation.
`matrix_catalogue` transports the complete marked normal-eight catalogue and
the orders 128, 1024 and 512 of the third lower-central terms of their full
centralizers. It has no additional premises. The conditional comparison and
transport interfaces remain available separately.

Source context: Kleidman--Wilson (1988), pp.484--510; Aschbacher--Smith,
`refs/quasithin.pdf`, printed p.511/PDF p.528. Matrix and word provenance is in
`AutomorphismReduction.FirstGenerator.OddIndex.SylowCandidate`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowNormalEights

attribute [local irreducible] modelGroup matrixA matrixB

/-- A verified surjective realization automatically has trivial kernel. -/
noncomputable def matrixEquivOfSurjective
    (f : Presentation.Carrier →* OuterReduction.OddIndex.twoSubgroup)
    (hf : Function.Surjective f) :
    Presentation.Carrier ≃* OuterReduction.OddIndex.twoSubgroup :=
  MulEquiv.ofBijective f (hf.bijective_of_nat_card_le (by
    rw [OuterReduction.OddIndex.twoSubgroup_card]
    exact Presentation.card_le))

/-- Literal relations and generation discharge all requirements of comparison. -/
noncomputable def matrixEquivOfRelations
    (g : Fin 21 → OuterReduction.OddIndex.twoSubgroup)
    (hrel : Presentation.Relations g)
    (hgen : Subgroup.closure (Set.range g) = ⊤) :
    Presentation.Carrier ≃* OuterReduction.OddIndex.twoSubgroup :=
  matrixEquivOfSurjective (Presentation.lift g hrel)
    (MonoidHom.range_eq_top.mp ((Presentation.range_lift g hrel).trans hgen))

/-- The shared literal word sequence has the same comparison criterion. -/
noncomputable def matrixEquivOfWords
    (hrel : Presentation.Relations MatrixWords.pcGenerator)
    (hgen : Subgroup.closure (Set.range MatrixWords.pcGenerator) = ⊤) :
    Presentation.Carrier ≃* OuterReduction.OddIndex.twoSubgroup :=
  matrixEquivOfRelations MatrixWords.pcGenerator hrel hgen

/-- The comparison preserves the marked generators literally. -/
@[simp] theorem matrixEquivOfRelations_generator
    (g : Fin 21 → OuterReduction.OddIndex.twoSubgroup)
    (hrel : Presentation.Relations g)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (i : Fin 21) :
    matrixEquivOfRelations g hrel hgen (Presentation.generator i) = g i :=
  Presentation.lift_generator g hrel i

/-- An actual realization discharges consistency for the abstract calculation. -/
theorem presentation_card_of_equiv
    (e : Presentation.Carrier ≃* OuterReduction.OddIndex.twoSubgroup) :
    Nat.card Presentation.Carrier = 2 ^ 21 :=
  (Nat.card_congr e.toEquiv).trans OuterReduction.OddIndex.twoSubgroup_card

/-- The checked literal words identify the presentation with the actual matrix subgroup. -/
noncomputable def matrixEquiv :
    Presentation.Carrier ≃* OuterReduction.OddIndex.twoSubgroup :=
  matrixEquivOfWords MatrixWords.pcGenerator_relations MatrixWords.pcGenerator_closure

/-- The unconditional comparison takes each canonical generator to its literal matrix word. -/
@[simp] theorem matrixEquiv_generator (i : Fin 21) :
    matrixEquiv (Presentation.generator i) = MatrixWords.pcGenerator i :=
  matrixEquivOfRelations_generator MatrixWords.pcGenerator
    MatrixWords.pcGenerator_relations MatrixWords.pcGenerator_closure i

/-- The literal matrix realization establishes the full order of the presentation. -/
theorem presentation_card : Nat.card Presentation.Carrier = 2 ^ 21 :=
  presentation_card_of_equiv matrixEquiv

/-- Coverage and full-centralizer invariants transport to the literal matrix subgroup. -/
theorem matrix_catalogue_of_equiv
    (e : Presentation.Carrier ≃* OuterReduction.OddIndex.twoSubgroup)
    (hcover : Presentation.CatalogueCoverage)
    (hprofiles : Presentation.CentralizerProfiles) :
    ∃ family : Fin 3 → Subgroup OuterReduction.OddIndex.twoSubgroup,
      (∀ A : Subgroup OuterReduction.OddIndex.twoSubgroup,
        A.Normal → IsElementaryAbelian 2 A → Nat.card A = 8 →
        A ≤ Subgroup.upperCentralSeries OuterReduction.OddIndex.twoSubgroup 3 →
          ∃ i, A = family i) ∧
      (∀ i, Subgroup.centralizerLowerCentralCard (family i) 2 = Presentation.profileOrder i) := by
  refine ⟨fun i => (Presentation.family i).map e.toMonoidHom, ?_, ?_⟩
  · intro A hn he hc hu
    let : A.Normal := hn
    let : IsElementaryAbelian 2 A := he
    have hnormal : (A.map e.symm.toMonoidHom).Normal :=
      Subgroup.Normal.map hn e.symm.toMonoidHom e.symm.surjective
    have helementary : IsElementaryAbelian 2 (A.map e.symm.toMonoidHom) :=
      IsElementaryAbelian.map _
    have hcard : Nat.card (A.map e.symm.toMonoidHom) = 8 := by
      rw [Subgroup.card_map_of_injective e.symm.injective, hc]
    have hupper : A.map e.symm.toMonoidHom ≤
        Subgroup.upperCentralSeries Presentation.Carrier 3 := by
      rw [← Subgroup.comap_upperCentralSeries e 3]
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_comap]
      simpa using hu hx
    obtain ⟨i, hi⟩ := hcover _ hnormal helementary hcard hupper
    exact ⟨i, ((Subgroup.map_symm_eq_iff_map_eq (Presentation.family i)).mp hi).symm⟩
  · intro i
    rw [Subgroup.centralizerLowerCentralCard_map]
    exact hprofiles i

/-- The complete normal-eight catalogue and the third lower-central orders
of its full centralizers in the existing actual matrix two-subgroup. -/
theorem matrix_catalogue :
    ∃ family : Fin 3 → Subgroup OuterReduction.OddIndex.twoSubgroup,
      (∀ A : Subgroup OuterReduction.OddIndex.twoSubgroup,
        A.Normal → IsElementaryAbelian 2 A → Nat.card A = 8 →
        A ≤ Subgroup.upperCentralSeries OuterReduction.OddIndex.twoSubgroup 3 →
          ∃ i, A = family i) ∧
      (∀ i, Subgroup.centralizerLowerCentralCard (family i) 2 = Presentation.profileOrder i) := by
  obtain ⟨hcover, hprofiles⟩ := Presentation.profiles_of_card presentation_card
  exact matrix_catalogue_of_equiv matrixEquiv hcover hprofiles

end Janko4.LocalStructure.SylowNormalEights
