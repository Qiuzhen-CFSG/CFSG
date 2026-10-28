module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.Noncontainment
public import CFSG.Quasithin.Chapter14.Section02.SourceSetup
public import Theory.GroupTheory.PCoreQuotientBorelNormalizer
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.SpecificGroups.SL2.EvenBorelResidual

/-!
# The actual ambient normalizer in the L₂(8) branch

An identification of K/O₂(K) with PSL₂(8) makes its full outer group have
order three. The local Sylow normalizer therefore normalizes the original
ambient T, even when T is not contained in K. Original 14.2.2(7) puts it
in M ∩ Mc. Its quotient image is precisely the Borel at the image of
T ∩ K, and its full inverse image is the same local Sylow normalizer.

These results prove the normalizer-placement half of the contradiction.
The identification of the dotted image with K/O₂(K), and the specialized
14.3.6(1) exclusion of Borel containment in M, remain separate obligations.
Source: Aschbacher--Smith 14.3.6(1) and 14.3.15, printed pp.991,994.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem eight_center_outer {D : Type*} [Group D]
    (e : D ≃* Theory.PSL2.BinaryGroup 3) :
    center D = ⊥ ∧ Nat.Coprime 2 (Nat.card (MulAut.Outer D)) := by
  constructor
  · let f := e.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
    apply eq_bot_iff.mpr
    intro d hd
    have hf : f d ∈ center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
      (centerCongr f ⟨d,hd⟩).property
    rw [Theory.PSL2.sl2_center_eq_bot, mem_bot] at hf
    exact f.injective (hf.trans f.map_one.symm)
  · rw [Nat.card_congr (MulAut.outerCongr e).toEquiv, Theory.PSL2.psl_eight_outer_card]
    decide

/-- The genuine L₂(8) core quotient supplies the full ambient normalizer
inclusion, retaining the intersection Sylow rather than assuming T ≤ K. -/
theorem eight_borel_le_sylow_normalizer
    (T : Sylow 2 G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3) :
    (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤
      normalizer (T : Set G) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  obtain ⟨hz,ho⟩ := eight_center_outer eK
  have h := sylow_normalizer_le_of_coprime_outer T K hn hz ho P hP
  change (normalizer ((P : Subgroup K) : Set K)).map K.subtype ≤ _ at h
  rwa [hP] at h

/-- Original14.2.2(7) places this actual normalizer in both selected locals. -/
theorem source_eight_borel_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (K : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3) :
    (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M ⊓ Mc :=
  (eight_borel_le_sylow_normalizer T K hn eK).trans
    (source_lemma_14_2_2_7 hG T hempty hM hu hmany hcard e)

/-- The same placement on the literal quotient, with both the Sylow marking
and the full inverse-image equality. The model normalizer is the PSL₂ Borel. -/
theorem source_eight_quotient_borel_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (K : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3) :
    ∃ P : Sylow 2 K, (P : Subgroup K) = (T : Subgroup G).subgroupOf K ∧
      let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
      (normalizer (P.map q : Set (Theory.PSL2.BinaryGroup 3))).comap q =
        normalizer (P : Set K) ∧
      normalizer (P.map q : Set (Theory.PSL2.BinaryGroup 3)) ≤
        (M.subgroupOf K).map q ∧
      Nonempty (normalizer (P.map q : Set (Theory.PSL2.BinaryGroup 3)) ≃*
        Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel (GaloisField 2 3)) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  refine ⟨P,hP,?_⟩
  dsimp only
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    ext k
    change eK (QuotientGroup.mk k) = 1 ↔ k ∈ pCore 2 K
    rw [eK.map_eq_one_iff,QuotientGroup.eq_one_iff]
  have hkP : q.ker ≤ (P : Subgroup K) := hk ▸ pCore_isPGroup.le_sylow_of_normal P
  refine ⟨comap_sylow_normalizer_of_ker_le P q hq hkP, ?_, ?_⟩
  · rw [← P.normalizer_map_surjective q hq]
    apply map_mono
    have h := (source_eight_borel_placement hG T hempty hM hu hmany hcard e K hn eK).trans
      inf_le_left
    intro k hk
    apply h
    apply mem_map_of_mem K.subtype
    change k ∈ normalizer ((P : Subgroup K) : Set K) at hk
    rwa [← hP]
  · exact ⟨Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv
      (GaloisField 2 3) (P.mapSurjective hq)⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
