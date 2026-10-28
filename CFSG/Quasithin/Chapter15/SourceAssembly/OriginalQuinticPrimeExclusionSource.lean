module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalQuinticExclusionSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Exclusion

/-!
# The original later quintic exclusion after the order-fifteen contradiction

The broad original quintic callback is preserved. Its order-fifteen branch
is supplied by the actual faithful partner section and its cubic quotient.
The remaining callback has the same original data, preceding residual control,
normalizer bounds and counterexample guards, with literal marked residual
order five. No assertion about the remaining prime branch is inferred.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original later quintic exclusion restricted to literal residual order five. -/
abbrev OriginalQuinticPrimeExclusionAt (T : Sylow 2 G) (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
  (∀ N : Subgroup G, IsOrderingMaximal T N →
    ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
  ∀ (M : Subgroup G) (_hM : IsOrderingMaximal T M), M ≠ Mc →
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
    ∀ h : PreparedChosenModule T M (localModule T M),
      letI := h.elementary
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
          centralizer (thompsonFixed T (localModule T M) : Set G) →
      (M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
          normalizer (thompsonFixed T (localModule T M) : Set G) ∧
        normalizer (thompsonFixed T (localModule T M) : Set G) ≤ Mc ∧
        normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc) →
      ∀ {U : Submodule (ZMod 2) (Additive (localModule T M))}
        (c : FactorData (imageRepresentation M (localModule T M) h.normalized)
          (Jhat (imageRepresentation M (localModule T M) h.normalized)) U)
        (d : Decomposition c.representation), d.FittingFull →
      ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
        (π : internalActionImage M (localModule T M) h.normalized →* Equiv.Perm d.Index),
        (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (c.ambientFactor d (π g i)).actor) →
        (∀ g i, (c.ambientFactor d i).space.map
            (imageRepresentation M (localModule T M) h.normalized g) =
          (c.ambientFactor d (π g i)).space) →
        SourceCases.Decomposable (imageRepresentation M (localModule T M) h.normalized)
          (T : Subgroup G) M (actionHom M (localModule T M) h.normalized).rangeRestrict
          c d π →
        cubicRatio (imageRepresentation M (localModule T M) h.normalized) = 2 →
        s.prime = 5 →
        let Z₁ := thompsonPlane T (localModule T M) (c.ambientFactor d s.first).space
        let C := M ⊓ centralizer (Z₁ : Set G)
        letI := caseI_module_centralizer_normal (Z1 := Z₁) h.normalized
        Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (localModule T M : Set G)).subgroupOf C)) = 5 →
        False

/-- The actual order-fifteen contradiction supplies that branch of the
unchanged broad original later quintic exclusion. -/
theorem original_quintic_exclusion_of_prime_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hprime : OriginalQuinticPrimeExclusionAt T Mc) : OriginalQuinticExclusionAt T Mc := by
  intro hnot hn M hM hne hJ h hres hbounds
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun E hE => hE.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  rcases (s.full_quotient_residual_of_prime_five hM.1.2 h.normalized c d π hp hs hJi hfive).2
      with h5 | h15
  · exact hprime hnot hn M hM hne hJ h hres hbounds c d hd s π hp hs hdec hq hfive h5
  · exact h.false_of_full_decomposable_fifteen
      hG T hempty hM hmany hJ hu hne rfl c d hd s π hp hs hdec hq hfive h15

end CFSG.Quasithin.Chapter15
