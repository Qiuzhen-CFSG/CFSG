module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.Exchanged
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.ComponentDecomposition

/-!
# Terminal structure and component sum after the exchanged branch

The source sieve now constructs every nonnormal component quotient as PSL₃(2),
with genuine parabolic exchange. Consequently the terminal alternatives,
residual factorization and the full sum on U/Z require model recognition only
for relatively normal components. These consumers discharge the exchanged
model premise using the same original K/O₂(K), T and terminal Mc.

The remaining normal-component exclusions and natural-support directness
remain with qt-e-suitable-component-supports. Original 14.6.18 remains with
qt-e-14625-source. The component sum below does not assert directness.

Source: Aschbacher--Smith 14.6.20--23, printed pp.1037--1038.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.OneCohomology
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Classification
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (hm : ∀ K : Subgroup G, K ≤ Mc → (K.subgroupOf Mc).IsCComponent →
      (K.subgroupOf Mc).Normal → ComponentQuotientModels K)

include hG hempty hM hunique hmany hcard e hab hsolv hm

/-- The full original component family needs quotient recognition only in
its relatively normal branch; exchanged markings are constructed. -/
theorem source_all_component_models_of_normal_models
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    ComponentQuotientModels K := by
  by_cases hn : (K.subgroupOf Mc).Normal
  · exact hm K hKM hK hn
  · obtain ⟨a,_⟩ := Classification.Sieve.terminal_nonnormal_component_linear_three_diagram
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
    exact Or.inl ⟨a.trans Matrix.PSL3Two.equiv.symm⟩

/-- The actual one/two-component alternatives and diagram action after the
complete exchanged-component exclusion. -/
theorem terminal_alternatives_with_diagram_of_normal_models
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    TerminalComponentAlternatives T Mc K ∧ Classification.Sieve.ComponentModelDiagram T K :=
  Classification.Sieve.terminal_alternatives_with_diagram_of_component_models
    hG T hempty hM hunique hmany hcard e hab hsolv
    (source_all_component_models_of_normal_models hG T hempty hM hunique hmany hcard e hab hsolv hm)
    K hKM hK

/-- The literal residual factorization retains only the normal model input. -/
theorem terminal_residual_structure_of_normal_models :
    solvableResidual Mc = pResidual 2 Mc ∧
      (Mc : Set G) = ((solvableResidual Mc).map Mc.subtype : Set G) *
        ((T : Subgroup G) : Set G) :=
  terminal_residual_structure_of_component_models
    hG T hempty hM hunique hmany hcard e hab hsolv
    (source_all_component_models_of_normal_models hG T hempty hM hunique hmany hcard e hab hsolv hm)

/-- The full component sum on the literal U/Z, after constructing all
exchanged quotient models. Recognition of normal components remains explicit. -/
theorem source_canonical_component_sum_of_normal_models :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let _ : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
      h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
    let U := conjugateSpanBy (localModule T M) Mc
    let Z := centralInvolutions T
    ∃ ρ : Representation (ZMod 2) Mc (Additive (U ⧸ Z.subgroupOf U)),
      ∃ c : BinaryConjugationSection Mc U Z ρ,
        (⨆ K : {K : Subgroup Mc // K.IsCComponent},
          c.imageSpace ⁅U, K.val.map Mc.subtype⁆) ⊔ fixed ρ = ⊤ :=
  source_canonical_component_sum_of_models
    hG T hempty hM hunique hmany hcard e hab hsolv
    (source_all_component_models_of_normal_models hG T hempty hM hunique hmany hcard e hab hsolv hm)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports
