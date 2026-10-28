module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CyclicComponent
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Noncyclic
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.DistinctCores
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ActionKernel
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Actual solvable quotient models when the original cores differ

Unequal vertex two-cores preserve the Goldschmidt triple in the literal
quotient X/O₃′(X), and exclude its order-two overlap. A cyclic three-core
would produce a genuine quasisimple component by F.6.17, contrary to
solvability. The completed F.6.16 therefore supplies the two actual
quotient models S₃ × S₃ and 3₊¹⁺² ⋊ E₄, together with the three-group
two-residual. The final theorem applies this to the original local join,
constructing its genuine SQTK cover from Hypothesis 13.3.1.

These are isomorphisms of the whole prime-to-three quotient, not of
X/O₂(X). The further odd-prime exclusion and full action-kernel equality
are still required for source case (iii), its Thompson normality, and
the original plane exclusion. No model or component is assumed here.

Source: Aschbacher--Smith 13.4.7, printed pp.901--902; F.6.11,16--18,
printed pp.306--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal prime-to-three quotient of a solvable unequal-core pair has
one of the two actual four-group-over-three-group models. -/
theorem solvable_prime_quotient_models {K : GroupClass.{u}}
    (hG : IsSQTK K G) {A B : Subgroup G} (hg : ChapterF.IsGoldschmidtTriple A B)
    (hne : A.pCoreIn 2 ≠ B.pCoreIn 2) (hs : Group.IsSolvable G) :
    let Q := G ⧸ pPrimeCore 3 G
    IsPGroup 3 (pResidual 2 Q) ∧
      (Nonempty (Q ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
        Nonempty (Q ≃* MarkedCubicRecognition.HeisenbergExtension)) := by
  let Q := G ⧸ pPrimeCore 3 G
  let q := QuotientGroup.mk' (pPrimeCore 3 G)
  have hq := hg.quotient_primeToThreeCore_of_distinct_cores hne
  let : Group.IsSolvable G := hs
  let : Group.IsSolvable Q := inferInstance
  have hn : ¬ IsCyclic (pCore 3 Q) := by
    intro hcyc
    obtain ⟨C,hC,_⟩ := ChapterF.Cyclic.exists_component_of_cyclic_three_core_quotient
      (MulEquiv.refl Q) hq hcyc
    let : IsQuasisimple C := hC.2
    let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
    let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
    exact Group.IsPerfect.not_isSolvable C inferInstance
  obtain ⟨hr,hcases⟩ := ChapterF.SourceAssembly.source_lemma_F_6_16 hG (MulEquiv.refl Q) hq hn
  refine ⟨hr,?_⟩
  rcases hcases with htwo | he | he
  · exact (hg.primeToThreeCore_intersection_not_cyclic_two hne htwo.1).elim
  · exact Or.inl he
  · exact Or.inr he

private theorem solvable_pair_sqtk (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {X : Subgroup G} (hX : X ∈ Chapter1.H G) : IsSQTK KnownSimple.IsKnownSimple X := by
  let R := X.pCoreIn 2
  let N := normalizer (R : Set G)
  have hXN : X ≤ N := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hN : IsTwoLocal N := ⟨R,hX,isPGroup_pCoreIn 2 X,rfl⟩
  have hh := (hG.twoLocal_sqtk hN).subgroup (X.subgroupOf N)
  exact ⟨hh.stronglyQuasithin.of_injective
    (subgroupOfEquivOfLe hXN).symm.toMonoidHom (subgroupOfEquivOfLe hXN).symm.injective,
    hh.isKGroup.of_injective
      (subgroupOfEquivOfLe hXN).symm.toMonoidHom (subgroupOfEquivOfLe hXN).symm.injective⟩

/-- The original solvable pair selects actual quotient models from the
preceding source theorems, without supplying a marked amalgam model. -/
theorem original_pair_solvable_prime_models {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcores : A.pCoreIn 2 ≠ B.pCoreIn 2) (hs : Group.IsSolvable (A ⊔ B : Subgroup G)) :
    let X := A ⊔ B
    let Q := X ⧸ pPrimeCore 3 X
    IsPGroup 3 (pResidual 2 Q) ∧
      (Nonempty (Q ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
        Nonempty (Q ≃* MarkedCubicRecognition.HeisenbergExtension)) := by
  let X := A ⊔ B
  have hlocal := original_pair_local D m hTA hTB eA eB hne hindexA hindexB
  have hc : (A.subgroupOf X).pCoreIn 2 ≠ (B.subgroupOf X).pCoreIn 2 := by
    intro he
    have hm := congrArg (map X.subtype) he
    rw [pCoreIn_subgroupOf 2 A X le_sup_left,pCoreIn_subgroupOf 2 B X le_sup_right,
      map_subgroupOf_eq_of_le ((A.pCoreIn_le 2).trans le_sup_left),
      map_subgroupOf_eq_of_le ((B.pCoreIn_le 2).trans le_sup_right)] at hm
    exact hcores hm
  exact solvable_prime_quotient_models (solvable_pair_sqtk h₀.qtke hlocal.1)
    (pair_goldschmidt hTA hTB eA eB hne) hc hs
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
