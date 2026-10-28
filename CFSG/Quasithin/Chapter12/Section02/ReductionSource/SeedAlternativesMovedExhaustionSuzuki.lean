module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionComponentRank
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzuki

/-!
# Suzuki support in the literal chosen-seed normalizer action

Each ordinary component of Aut_M(U) is a semisimple section of the original
SQTK normalizer M. Theorem A supplies its odd-rank bounds; subnormality
and the reduced full action kill its two-core. The complete A.3.6 catalogue
then gives an actual Suzuki matrix-group isomorphism for each three-free
component, with no quotient-rank monotonicity assumption.

For the component moved by the selected starred actor's centralizer of K,
normalization by that actor collapses the component orbit to the component.
The invariant-constituent construction and the Suzuki endpoint now contradict
the strict ratio drop. Thus the remaining three-free case necessarily
permutes distinct Suzuki components. The final application retains the same
A, X, K, W and U/W, the original standing guard and every other source branch.

This excludes normalized Suzuki support, not the full component alternative.
The actor-permuted Suzuki case, the normal rank-one component, the FF sections,
U = W and final Source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith Theorems A and C and A.3.6, pp.33--45;
D.3.8--15, pp.199--202; application 3.2.5, p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterD
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Theorem A applies to each actual component as a semisimple section of M. -/
theorem normalizer_action_component_sqtk
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    ∀ J : Subgroup (internalActionImage M U hn),
      IsComponent (internalActionImage M U hn) J → IsSQTK KnownSimple.IsKnownSimple J := by
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  dsimp only
  intro J hJ
  let := hJ.2
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hmax : IsMaximalTwoLocal M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hs := h.simpleQTKE.twoLocal_sqtk hmax.1
  have hsec : ChapterA.Section02.IsSectionOf J M :=
    (ChapterA.Section02.IsSectionOf.subgroup J).ambient_surjective
      (internalHom M U hn) (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  have hsemi : ChapterA.Section02.IsSemisimple J := by
    apply top_unique
    exact le_sSup (show IsComponent J ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup J) ≃* J).symm⟩)
  exact ⟨ChapterA.Section02.TheoremA.stronglyQuasithin_section
    ChapterA.Section02.theoremA_knownSimple hs.stronglyQuasithin hs.isKGroup hsec hsemi,
    hsec.isKGroup hs.isKGroup⟩

/-- Three-free components of the original faithful normalizer action are
actual Suzuki groups; the two-core vanishes by subnormality. -/
theorem normalizer_action_component_suzuki_of_three_free
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    ∀ J : Subgroup (internalActionImage M U hn),
      IsComponent (internalActionImage M U hn) J → ¬ 3 ∣ Nat.card J →
      ∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) := by
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  dsimp only
  intro J hJ h3
  let := hJ.2
  have hJ2 : pCore 2 J = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hJ.1,D.normalizerActor_twoCore_eq_bot h.toHypothesis1221]
    exact J.subtype.ker_eq_bot_iff.mpr J.subtype_injective
  have htop : IsComponent J ⊤ :=
    ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup J) ≃* J).symm⟩
  have hclass := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    J (D.normalizer_action_component_sqtk h J hJ) hJ2 ⊤ htop.isCComponent
  have h3top : Nat.Coprime 3 (Nat.card (⊤ : Subgroup J)) := by
    rw [Nat.card_congr (topEquiv : (⊤ : Subgroup J) ≃* J).toEquiv]
    exact Nat.prime_three.coprime_iff_not_dvd.mpr h3
  obtain ⟨r,hr,⟨e⟩⟩ :=
    Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue.a36_suzuki_of_coprime
      hclass h3top
  exact ⟨r,by omega,⟨(topEquiv : (⊤ : Subgroup J) ≃* J).symm.trans e⟩⟩

/-- The source starred actor cannot normalize a three-free component moved
by its component centralizer. All representation and classification premises
are discharged on the literal chosen-seed action. -/
theorem normalizer_starred_moved_three_free_component_not_normalized
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let C := centralizer (K : Set (internalActionImage M U hn))
    ∀ J A : Subgroup (internalActionImage M U hn),
      IsComponent (internalActionImage M U hn) J → J ≤ C → ¬ 3 ∣ Nat.card J →
      A ∈ QhatStar ρ → ⁅componentOrbit J A,A ⊓ C⁆ = componentOrbit J A →
      ¬ A ≤ normalizer (J : Set _) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let K := (L.subgroupOf M).map (internalHom M U hn)
  let C := centralizer (K : Set (internalActionImage M U hn))
  let := D.normalizer_component_quasisimple h.toHypothesis1221 hc
  dsimp only
  intro J A hJ hJC h3 hA hmove hAJ
  let := hJ.2
  have horbit : componentOrbit J A = J := le_antisymm
    (iSup_conjugates_le_of_le_normalizer J A J le_rfl hAJ) (le_componentOrbit J A)
  obtain ⟨r,hr,⟨e⟩⟩ := D.normalizer_action_component_suzuki_of_three_free h J hJ h3
  apply no_normalized_suzuki_support ρ (UniqueFactor.imageRepresentation_injective M U hn)
    K J A (A ⊓ C) (D.normalizer_component_fixedSpace_eq_bot h.toHypothesis1221 hc)
    hJC (D.normalizer_action_component_sqtk h J hJ) hJ.isCComponent.ne_bot hAJ hA
    inf_le_left (by simpa only [horbit] using hmove) hr e

/-- The actual remaining exhaustion alternatives now have either a
Suzuki component actually permuted by A, one normal component of three-rank one, or an
FF offender on the unchanged W or U/W section. All inputs remain original. -/
theorem exists_normalizer_moved_suzuki_or_rank_one_component_or_section_offender_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let C := centralizer (K : Set (internalActionImage M U hn))
    let S := D.normalizerLocalSection h.toHypothesis1221
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧ A ∈ QhatStar ρ ∧
      ((∃ X : Subgroup (internalActionImage M U hn),
          X ≤ C ∧ A ≤ normalizer (X : Set _) ∧ X ≠ ⊥ ∧ ⁅X,A ⊓ C⁆ = X ∧
          ∃ J : Subgroup (internalActionImage M U hn),
            IsComponent (internalActionImage M U hn) J ∧ J ≤ C ∧ X = componentOrbit J A ∧
            ((¬ 3 ∣ Nat.card J ∧
                (∃ r : ℕ, 0 < r ∧ Nonempty
                  (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)) ∧
                ¬ A ≤ normalizer (J : Set _)) ∨
              (X = J ∧ J.Normal ∧ primeRank 3 J = 1 ∧ pCore 3 C = ⊥))) ∨
        (IsOffender (imageRepresentation S.toRepresentation)
          (actionSubgroup S.toRepresentation (A.subgroupOf D.normalizerLocalActor)) ∨
        IsOffender (imageRepresentation S.quotientRepresentation)
          (actionSubgroup S.quotientRepresentation (A.subgroupOf D.normalizerLocalActor)))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  obtain ⟨A,hAS,hA,hcase⟩ :=
    D.exists_normalizer_rank_one_component_or_section_offender_of_many h hmany hc hm hne
  refine ⟨A,hAS,hA,?_⟩
  rcases hcase with ⟨X,hXC,hAX,hXn,hXB,J,hJ,hJC,hX,hcases⟩ | hff
  · refine Or.inl ⟨X,hXC,hAX,hXn,hXB,J,hJ,hJC,hX,?_⟩
    rcases hcases with hthree | hn
    · exact Or.inl ⟨hthree,D.normalizer_action_component_suzuki_of_three_free h J hJ hthree,
        D.normalizer_starred_moved_three_free_component_not_normalized h hc J A hJ hJC hthree
          hA (by simpa only [←hX] using hXB)⟩
    · exact Or.inr hn
  · exact Or.inr hff

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
