module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Doubled.SeedGeneration
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Ranks
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Centers
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Transport
/-!
# The doubled natural SL₃ row on the original seed

Perfectness identifies the source moved section with all of the literal seed
U=[C_V(O₂(LA)),L]. The resulting action equivalence uses the actual faithful
map from L to L⁺ and one intertwiner onto two copies of the same natural
module. Pulling its coordinate embeddings back into V gives irreducible,
noncentral L-submodules. Each is in Irr⁺(L,V), and their sum is U.

The source equality L⁺=(LA)⁺ supplies inner action on L. Centerlessness and
the quotient ratio supply disjointness and the original seed-image rank
equality through the proved literal transport APIs. No identification U=[V,L]
or containment A≤L is used. The full source conclusion and selected row are
explicit inputs; the earlier-source and exhaustive-row assemblies remain
with their existing owners.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.9, printed pp.107–108, case (III).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
variable {G V H W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V)

private theorem irrPlus_range {L : Subgroup G} (σ : Representation (ZMod 2) H W)
    (e : L ≃* H) (j : W →ₗ[ZMod 2] V) (hj : Function.Injective j)
    (he : ∀ l : L, ∀ w, ρ l (j w) = j (σ (e l) w))
    (hi : IsIrreducible σ) (hz : σ.invariants = ⊥) : IsIrrPlus ρ L j.range := by
  let := hi
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  have hs : L ≤ subspaceStabilizer ρ j.range := by
    apply le_subspaceStabilizer
    rintro l hl _ ⟨w, rfl⟩
    exact ⟨σ (e ⟨l, hl⟩) w, (he ⟨l, hl⟩ w).symm⟩
  have hmin (J : Submodule (ZMod 2) V) (hJ : L ≤ subspaceStabilizer ρ J)
      (hle : J ≤ j.range) : J = ⊥ ∨ J = j.range := by
    let T : Subrepresentation σ := ⟨J.comap j, by
      intro g w hw
      change j (σ g w) ∈ J
      rw [← e.apply_symm_apply g, ← he]
      exact (hJ (e.symm g).property _).2 hw⟩
    rcases eq_bot_or_eq_top T with hb | ht
    · left
      apply le_bot_iff.mp
      intro v hv
      obtain ⟨w, rfl⟩ := hle hv
      have hw : w ∈ T.toSubmodule := hv
      rw [hb] at hw
      have hw0 : w = 0 := hw
      simp only [hw0, map_zero, Submodule.zero_mem]
    · right
      apply le_antisymm hle
      rintro _ ⟨w, rfl⟩
      exact (show w ∈ T.toSubmodule from ht ▸ Submodule.mem_top)
  have hn : ¬ j.range ≤ fixedSpace ρ L := by
    intro hc
    have hall (w : W) : w = 0 := by
      apply (Submodule.mem_bot (ZMod 2)).mp
      rw [← hz]
      intro g
      apply hj
      rw [← e.apply_symm_apply g, ← he]
      exact hc ⟨w, rfl⟩ (e.symm g)
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact hw (hall w)
  apply isIrrPlus_of_minimal ρ hs
  · rcases hmin (subspaceCommutator ρ j.range L)
      (subspaceCommutator_invariant ρ _ L) (subspaceCommutator_le_of_invariant ρ hs) with hb | ht
    · exact (hn ((subspaceCommutator_eq_bot_iff ρ _ L).mp hb)).elim
    · exact ht
  · exact hn
  · intro J hJ hle
    rcases hmin J hJ hle with rfl | heq
    · exact Or.inr bot_le
    · exact Or.inl heq

/-- Both coordinate summands use the actor and intertwiner of the same action equivalence. -/
theorem seed_le_irrPlus_span_of_repeated {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (F : BinaryField)
    (e : ActionEquiv (seedComponentAction ρ hLA) (repeated (linearNatural F 3) 2)) :
    naturalSeedSpace ρ L A ≤ sSup {I | IsIrrPlus ρ L I} := by
  classical
  let U := (seedSubrepresentation ρ hLA).toSubmodule
  let j (i : Fin 2) : (Fin 3 → F.Carrier) →ₗ[ZMod 2] V :=
    U.subtype.comp (e.linearEquiv.symm.toLinearMap.comp
      (LinearMap.single (ZMod 2) (fun _ : Fin 2 => Fin 3 → F.Carrier) i))
  have hj (i : Fin 2) : Function.Injective (j i) := by
    intro a b hab
    have hu := U.subtype_injective hab
    have h := congrArg (fun v => e.linearEquiv v i) hu
    simpa [j] using h
  have he (i : Fin 2) (l : L) (w : Fin 3 → F.Carrier) :
      ρ l (j i w) = j i (linearNatural F 3 (e.groupEquiv l) w) := by
    have heq : seedComponentAction ρ hLA l
        (e.linearEquiv.symm (Pi.single i w)) =
        e.linearEquiv.symm (Pi.single i (linearNatural F 3 (e.groupEquiv l) w)) := by
      apply e.linearEquiv.injective
      rw [e.intertwines]
      simp only [LinearEquiv.apply_symm_apply]
      ext k
      by_cases hk : k = i
      · subst k; simp [repeated]
      · simp [repeated, Pi.single_eq_of_ne hk]
    exact congrArg Subtype.val heq
  have hI (i : Fin 2) : IsIrrPlus ρ L (j i).range :=
    irrPlus_range ρ (linearNatural F 3) e.groupEquiv (j i) (hj i) (he i)
      (ExtensionConsequences.linearNatural_irreducible F (by decide))
      (ExtensionConsequences.linearNatural_invariants F (by decide))
  intro v hv
  let u : U := ⟨v, hv⟩
  have heq : ∑ i : Fin 2, j i (e.linearEquiv u i) = v := by
    change ∑ i : Fin 2, U.subtype (e.linearEquiv.symm (Pi.single i (e.linearEquiv u i))) = v
    rw [← map_sum, ← map_sum, Finset.univ_sum_single, e.linearEquiv.symm_apply_apply]
    rfl
  rw [← heq]
  apply Submodule.sum_mem
  intro i _
  exact (show (j i).range ≤ sSup {I | IsIrrPlus ρ L I} from le_sSup (hI i)) ⟨_, rfl⟩

/-- Lift the doubled source section to U, using the actual component image map. -/
noncomputable def seedRepeatedActionEquiv [Finite G] {K : GroupClass}
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (hL : IsComponent G L)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (F : BinaryField)
    (e : ActionEquiv (s.space.toRepresentation.comp (seedComponentImage ρ hLA).subtype)
      (repeated (linearNatural F 3) 2)) :
    ActionEquiv (seedComponentAction ρ hLA) (repeated (linearNatural F 3) 2) := by
  let t := seedComponentActionEquiv ρ hLA p
  have hs : s.space.toSubmodule = ⊤ := s.space_eq.trans (seedQuotient_moved_eq_top ρ hLA hL)
  let q := (LinearEquiv.ofTop s.space.toSubmodule hs).symm
  refine ⟨t.groupEquiv.trans e.groupEquiv,
    t.linearEquiv.trans (q.trans e.linearEquiv), ?_⟩
  intro l u
  change e.linearEquiv (q (t.linearEquiv (seedComponentAction ρ hLA l u))) =
    repeated (linearNatural F 3) 2 (e.groupEquiv (t.groupEquiv l))
      (e.linearEquiv (q (t.linearEquiv u)))
  exact (congrArg (fun v => e.linearEquiv (q v)) (t.intertwines l u)).trans
    (e.intertwines (t.groupEquiv l) (q (t.linearEquiv u)))

/-- The explicit doubled B.5.1 row gives the doubled preliminary comparison.
The offender-family field is retained with exactly the source marking; the
comparison itself needs its whole-actor and ratio fields. -/
theorem compared_doubleThree_of_source [Finite G] {K : GroupClass}
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (hL : IsComponent G L) (hr : primeRank 3 L = 1)
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (F : BinaryField) (ho : Odd F.degree)
    (hwhole : seedComponentImage ρ hLA = ⊤)
    (e : ActionEquiv
      (c.sectionData.space.toRepresentation.comp (seedComponentImage ρ hLA).subtype)
      (repeated (linearNatural F 3) 2))
    (_hoff : ∀ B, IsBestOffender c.sectionData.space.toRepresentation B ↔
      IsFullAxisGroup F 3
        ((B.subgroupOf (seedComponentImage ρ hLA)).map e.groupEquiv.toMonoidHom))
    (hq : quadraticRatio (seedQuotientAction ρ hLA) = 1) :
    ComparedCase ρ hLA := by
  let eU := seedRepeatedActionEquiv ρ hLA p hL c.sectionData F e
  exact .doubleThree F ho ⟨eU⟩
    (seed_le_irrPlus_span_of_repeated ρ hLA F eU)
    (inducesInner_of_seedOffenderImage_le ρ hLA p (hwhole ▸ le_top))
    (seed_disjoint_of_source ρ hLA p hr c)
    (seedRankEquality_of_quotient_ratio_one ρ hLA p hq)
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
