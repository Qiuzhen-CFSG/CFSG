module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.SplitGeneration
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.SplitCoverage.Exchange
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.SplitCoverage.Conjugation
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges

/-!
# Restricted Bruhat coverage for the binary split F4 group

Positive-root collection and the proved simple Weyl conjugation identity give
local two-cell exchange. Generation by `U` and the four simple Weyl words then
gives an unrestricted `U N U` expression. Collecting its last factor according
to the signs of its Weyl images absorbs the positive-image factors into the
left subgroup and leaves exactly the required right inversion factor
`U ∩ n⁻¹U⁻n`.

The actual matrix exchanges specialize to `binaryPositiveRootExchanges`.
Together with the proved simple Weyl conjugation, they discharge all root
relations in `exists_split_normal_form`, establishing the existence part of
the binary split Bruhat normal form. No fixed-point generation, order,
simplicity or BN-pair hypothesis is used.

Source: GLS3 1.11.5 and 1.12.1, `refs/KGroup/GLS3/Chapter1.tex`; the intended
fixed-point application is Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of
`refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RadicalCoordinates LargeLocalSeeds Subgroup

/-- The proved supported matrix exchanges specialize to the binary positive roots. -/
theorem binaryPositiveRootExchanges : BinaryPositiveRootExchanges := by
  intro r s a b hrs
  exact rootGenerator_exchange 0 r s a b hrs

/-- Collect the positive Weyl images first and the negative images last. -/
theorem rightUnipotent_factorization_of_root_relations
    (hswap : BinaryPositiveRootExchanges) (hconj : BinarySimpleRootConjugation)
    {n c : SplitGroup 0} (hn : n ∈ splitWeylSubgroup) (hc : c ∈ splitUnipotent 0) :
    ∃ a ∈ splitUnipotent 0, n * a * n⁻¹ ∈ splitUnipotent 0 ∧
      ∃ v ∈ rightUnipotent n, c = a * v := by
  obtain ⟨σ, _, hσ⟩ := weyl_root_conjugation_of_simple hconj hn
  let A := splitUnipotent 0 ⊓ (splitUnipotent 0).comap (MulAut.conj n).toMonoidHom
  have hp (r : Root .positive) (t : CoefficientField 0) :
      rootGeneratorInGroup 0 r.val t ∈ splitUnipotent 0 :=
    subset_closure ⟨r.val, t, r.property, rfl⟩
  have hpartition (r : Root .positive) :
      (∀ t, rootGeneratorInGroup 0 r.val t ∈ A) ∨
      (∀ t, rootGeneratorInGroup 0 r.val t ∈ rightUnipotent n) := by
    by_cases hr : typeF4RootPairing_base.IsPos (σ r.val)
    · refine Or.inl (fun t => ⟨hp r t, ?_⟩)
      change n * rootGeneratorInGroup 0 r.val t * n⁻¹ ∈ splitUnipotent 0
      rw [hσ]
      exact subset_closure ⟨_, t, hr, rfl⟩
    · refine Or.inr (fun t => ⟨hp r t, ?_⟩)
      change n * rootGeneratorInGroup 0 r.val t * n⁻¹ ∈ LocalBlockInput.splitNegativeUnipotent 0
      rw [hσ]
      exact subset_closure ⟨_, t, hr, rfl⟩
  obtain ⟨a, ha, v, hv, he⟩ := positive_factorization_of_root_partition hswap
    A (rightUnipotent n) hpartition hc
  exact ⟨a, ha.1, ha.2, v, hv, he⟩

/-- The two concrete root relations imply the restricted Bruhat normal form.
The final right factor lies in `U ∩ n⁻¹ U⁻ n`, not just in `U`. -/
theorem exists_split_normal_form_of_root_relations
    (hswap : BinaryPositiveRootExchanges) (hconj : BinarySimpleRootConjugation)
    (g : SplitGroup 0) :
    ∃ u ∈ splitUnipotent 0, ∃ n ∈ splitWeylSubgroup,
      ∃ v ∈ rightUnipotent n, g = u * n * v := by
  have hgen : closure ((splitUnipotent 0 : Set (SplitGroup 0)) ∪
      (splitWeylSubgroup : Set (SplitGroup 0))) = ⊤ := by
    rw [Subgroup.closure_union, closure_eq, closure_eq, splitUnipotent_sup_weyl_eq_top]
  have hN : splitWeylSubgroup ≤ closure ((splitUnipotent 0 : Set (SplitGroup 0)) ∪
      Set.range (fun i : Fin 4 => simpleWord 0 [i])) :=
    closure_mono Set.subset_union_right
  obtain ⟨b, n, c, hb, hn, hc, he⟩ :=
    BruhatGeneration.exists_factorization_of_simpleLiftExchange
      (splitUnipotent 0) splitWeylSubgroup (Set.range fun i : Fin 4 => simpleWord 0 [i])
      hgen hN (fun _ hx => subset_closure hx)
      (by rintro _ ⟨i, rfl⟩; rw [simpleWord_mul_self]; exact (splitUnipotent 0).one_mem)
      (simpleLiftExchange_of_root_relations hswap hconj) g
  obtain ⟨a, _, hna, v, hv, hcv⟩ :=
    rightUnipotent_factorization_of_root_relations hswap hconj hn hc
  refine ⟨b * (n * a * n⁻¹), (splitUnipotent 0).mul_mem hb hna, n, hn, v, hv, ?_⟩
  rw [he, hcv]
  group

/-- Restricted split Bruhat coverage follows from positive-root exchanges alone.
Simple Weyl conjugation is proved by the actual integral matrix relations. -/
theorem exists_split_normal_form_of_positive_exchanges
    (hswap : BinaryPositiveRootExchanges) (g : SplitGroup 0) :
    ∃ u ∈ splitUnipotent 0, ∃ n ∈ splitWeylSubgroup,
      ∃ v ∈ rightUnipotent n, g = u * n * v :=
  exists_split_normal_form_of_root_relations hswap binarySimpleRootConjugation g

/-- Every binary split element has a Bruhat form whose right factor belongs to
`U ∩ n⁻¹U⁻n`, with `n` in the subgroup of actual simple Weyl words. -/
theorem exists_split_normal_form (g : SplitGroup 0) :
    ∃ u ∈ splitUnipotent 0, ∃ n ∈ splitWeylSubgroup,
      ∃ v ∈ rightUnipotent n, g = u * n * v :=
  exists_split_normal_form_of_positive_exchanges binaryPositiveRootExchanges g

end ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
