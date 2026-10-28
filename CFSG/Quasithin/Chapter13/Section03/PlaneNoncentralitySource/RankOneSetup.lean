module
public import CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource.ReducedLayer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The original reduced layer satisfies the rank-one source hypotheses

For an original chosen Irr⁺ module, the relative Sylow normalization makes
L normal in its full normalizer. The proved nonsolvable uniqueness theorem
1.2.7 makes that normalizer a maximal two-local containing T. The ambient
image of R₂(LT) is reduced in LT, and its L-action is nontrivial because it
contains the chosen nonzero subgroup U = [U,L]. These facts construct every
field of the genuine 5.2.3 setup, on the same original L, T and reduced layer.

The last theorem restricts the exceptional local output to that original U.
The classification implication 5.2.3 and the larger-field information from
5.2.9 remain separate source obligations; neither is a premise used to
construct the setup, and neither is asserted here.

Source: Aschbacher--Smith, 1.2.7, 5.2.3, 12.2.2(3d), and 13.3.2(3),
printed pp.506,649,795,885. The module alternative in 5.2.3(1) is retained.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource
open Chapter12.Section02
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L U : Subgroup G}

/-- All source 5.2.3 applicability conditions follow from the original
maximal faithful local subgroup, its quotient model, and an Irr⁺ choice.
No T-invariance or reducedness of the chosen U is assumed. -/
theorem source523_setup_of_chosen (D : ChosenModule T L U)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    Source523.Setup KnownSimple.IsKnownSimple T L (normalizer (L : Set G))
      ((ReducedModule (L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype) n := by
  let R := (ReducedModule (L ⊔ (T : Subgroup G))).map
    (L ⊔ (T : Subgroup G)).subtype
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have ho : componentOrbit L (T : Subgroup G) = L := D.localOrbit_eq
  have hM : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [ho] using hu.normalizer_maximal
  have he : R.subgroupOf (L ⊔ (T : Subgroup G)) =
      ReducedModule (L ⊔ (T : Subgroup G)) :=
    comap_map_eq_self_of_injective (L ⊔ (T : Subgroup G)).subtype_injective _
  refine ⟨h.simpleQTKE, h.maximal_faithful.1, h.maximal_faithful.2,
    hmodel, L.le_normalizer, ?_, ⟨hM, D.sylow_normalizes_component⟩,
    map_subtype_le _, ?_, ?_⟩
  · exact (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  · change IsPReduced 2 (R.subgroupOf (L ⊔ (T : Subgroup G)))
    rw [he]
    exact isPReduced_reducedPSubgroup
  · intro hzero
    apply D.ne_bot
    apply le_bot_iff.mp
    calc
      U = ⁅U,L⁆ := D.eq_commutator
      _ ≤ ⁅R,L⁆ := commutator_mono D.le_reduced le_rfl
      _ = ⊥ := hzero

/-- The A₅ quotient gives the exact field-four source marking, while the
original chosen module supplies the noncentral reduced module input. -/
theorem source523_a5_setup_of_chosen (D : ChosenModule T L U)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    Source523.Setup KnownSimple.IsKnownSimple T L (normalizer (L : Set G))
      ((ReducedModule (L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype) 2 := by
  apply source523_setup_of_chosen D h
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card (GaloisField 2 2) = 4 by exact GaloisField.card 2 2 (by decide))
  exact ⟨GaloisField 2 2, inferInstance, inferInstance,
    GaloisField.card 2 2 (by decide), ⟨e.trans f.symm⟩⟩

omit [Finite G] in
/-- The exact exceptional output of 5.2.3, on the source module used by
`source523_setup_of_chosen`, gives the required original chosen A₅ model. -/
theorem chosen_model_of_source523_local_alternative (D : ChosenModule T L U)
    {H : Subgroup G} {n : ℕ}
    (hlocal : Source523.LocalAlternative T L H
      ((ReducedModule (L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype) n) :
    Chapter6.Source.IsConjugationModel L U Chapter6.Source.a5Module :=
  chosen_model_of_source_sum D D.le_reduced hlocal.2.1

end CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource
