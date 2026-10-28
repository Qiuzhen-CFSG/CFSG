module

public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.Preservation

/-!
# Assembly of the Held maximal-normalizer catalogue

The fixed four-word representative has 22 explicitly defined subgroup candidates.
An intrinsic enumeration reduces normal elementary subgroups to these rows. Five
ambient normalizer identities identify the distinguished rows with conjugates of
max3, max4 and max5; exclusion of the other rows uses the maximal-two-local
qualifier. Finally the self-normalizing-two-group criterion makes the fixed
representative an actual Sylow subgroup.

The final `exists_sylow_catalogue` discharges every finite-certificate premise
of the retained conditional assembly. The proved generator action supplies graph
preservation and hence the pair-stabilizer bound used by the ambient identities.
The result has no order, simplicity, graph, or coverage assumptions. It classifies
the actual ambient normalizer only when that normalizer is maximal two-local,
as required by the Sylow-containing local reduction for condition E.

Source: Aschbacher–Smith, condition E and Volume I Theorem 0.1.2(5), printed
pp.3–4 (Volume II Theorem 0.1.1(5), pp.481–482); GLS3 Table 5.3p;
the literal ATLAS degree-2058 carrier.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Subgroup LocalPairs.SylowGeometry.Calculations

/-- Once the fixed representative is a two-group, each literal entry is a
nontrivial two-subgroup, so its ambient normalizer is two-local. -/
public theorem normalizer_ambient_isTwoLocal (hp : IsPGroup 2 representative)
    (j : Fin 22) : IsTwoLocal (normalizer (ambient j : Set He)) := by
  exact ⟨ambient j, ambient_ne_bot j,
    (hp.to_subgroup (entry j)).map representative.subtype, rfl⟩

/-- Strict inclusions into the indicated actual normalizers exclude the 17
nondistinguished entries from maximality among two-locals. -/
public theorem excluded_of_strict_inclusions (hp : IsPGroup 2 representative)
    (hproper : ∀ j : Fin 22, (∀ k : Fin 5, j ≠ distinguished k) →
      normalizer (ambient j : Set He) < normalizer (ambient (container j) : Set He)) :
    ∀ j : Fin 22, (∀ k : Fin 5, j ≠ distinguished k) →
      ¬ IsMaximalTwoLocal (normalizer (ambient j : Set He)) := by
  intro j hj hM
  exact (hproper j hj).ne (hM.eq_of_le
    (normalizer_ambient_isTwoLocal hp (container j)) (hproper j hj).le)

/-- The intrinsic enumeration and separate ambient calculations give the
maximal-normalizer catalogue inside the fixed representative. -/
public theorem catalogue_of_finite_certificates
    (henum : ∀ R : Subgroup representative, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R → ∃ j : Fin 22, R = entry j)
    (hidentified : ∀ k : Fin 5,
      normalizer (ambient (distinguished k) : Set He) =
        (subgroup (candidate k)).map (MulAut.conj (conjugator k)).toMonoidHom)
    (hexcluded : ∀ j : Fin 22, (∀ k : Fin 5, j ≠ distinguished k) →
      ¬ IsMaximalTwoLocal (normalizer (ambient j : Set He))) :
    ∀ R : Subgroup representative, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R →
      IsMaximalTwoLocal (normalizer (R.map representative.subtype : Set He)) →
      ∃ (i : Fin 3) (g : He),
        normalizer (R.map representative.subtype : Set He) =
          (subgroup i).map (MulAut.conj g).toMonoidHom := by
  classical
  intro R hR hn he hM
  obtain ⟨j, rfl⟩ := henum R hR hn he
  change IsMaximalTwoLocal (normalizer (ambient j : Set He)) at hM
  by_cases hj : ∃ k : Fin 5, j = distinguished k
  · obtain ⟨k, rfl⟩ := hj
    exact ⟨candidate k, conjugator k, hidentified k⟩
  · exact False.elim (hexcluded j (fun k hk => hj ⟨k, hk⟩) hM)

/-- Conditional assembly with an actual Sylow witness. The final
`exists_sylow_catalogue` supplies each certificate from the concrete model proofs. -/
public theorem exists_sylow_catalogue_of_finite_certificates
    (hp : IsPGroup 2 representative)
    (hn : normalizer (representative : Set He) = representative)
    (henum : ∀ R : Subgroup representative, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R → ∃ j : Fin 22, R = entry j)
    (hidentified : ∀ k : Fin 5,
      normalizer (ambient (distinguished k) : Set He) =
        (subgroup (candidate k)).map (MulAut.conj (conjugator k)).toMonoidHom)
    (hproper : ∀ j : Fin 22, (∀ k : Fin 5, j ≠ distinguished k) →
      normalizer (ambient j : Set He) < normalizer (ambient (container j) : Set He)) :
    ∃ T : Sylow 2 He, ∀ R : Subgroup T, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R →
      IsMaximalTwoLocal (normalizer (R.map (T : Subgroup He).subtype : Set He)) →
      ∃ (i : Fin 3) (g : He),
        normalizer (R.map (T : Subgroup He).subtype : Set He) =
          (subgroup i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨T, hT⟩ := exists_representative_sylow hp hn
  refine ⟨T, ?_⟩
  rw [hT]
  exact catalogue_of_finite_certificates henum hidentified
    (excluded_of_strict_inclusions hp hproper)

/-- An actual Sylow two-subgroup of Held has the exhaustive maximal-normalizer
catalogue given by the three literal max3/max4/max5 candidates.

Normality is intrinsic to this Sylow subgroup, while the normalizer is taken in
Held through the subtype embedding. The 22-entry enumeration, five normalizer
identities, seventeen strict inclusions and Sylow certificate are all discharged.
The maximal-two-local qualifier is essential for excluding the other rows. -/
public theorem exists_sylow_catalogue :
    ∃ T : Sylow 2 He, ∀ R : Subgroup T, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R →
      IsMaximalTwoLocal (normalizer (R.map (T : Subgroup He).subtype : Set He)) →
      ∃ (i : Fin 3) (g : He),
        normalizer (R.map (T : Subgroup He).subtype : Set He) =
          (subgroup i).map (MulAut.conj g).toMonoidHom := by
  have hgraph := Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
  exact exists_sylow_catalogue_of_finite_certificates representative_isPGroup
    InnerNormalizer.normalizer_eq (intrinsicEnumeration representative_isPGroup)
    (normalizer_identities representative_isPGroup hgraph
      (LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hgraph))
    normalizer_strict_inclusions

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
