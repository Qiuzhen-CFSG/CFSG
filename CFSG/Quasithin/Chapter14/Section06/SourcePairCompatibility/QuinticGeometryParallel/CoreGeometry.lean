module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.Residual
public import Theory.GroupTheory.PResidual.IndexTwoRestriction
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PCoreNormalizerAction.ResidualNormalizer
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup

/-!
# Intrinsic residual cores in the no-index quintic branch

Use the preimage of the actual permutation kernel to normalize the literal
factor residuals. Its index two puts the whole residual inside this preimage,
without identifying it with the preimage of Jhat. In the residual-closure
case the factor residuals are therefore subnormal in Mc. Two-perfectness
makes the partner core, and then the intrinsic residual-action kernel,
normalize each factor. The central point proves the second normalizer has
nontrivial two-core, so only the proper-local SQTK hypothesis is used there.

Source: Aschbacher--Smith 14.6.12(3) and 14.6.15, printed pp.1031,1034--1035.
The residual-closure equality is a branch assumption, not established here.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer
namespace SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)
include hG hempty hM hu hmany hcard e hab hJ hs hp w

omit hs hp w hab [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)] in
private theorem original_partner_contains : J ≤ Mc := by
  have he := (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
    J hJ.1.1 hJ.1.2).1
  exact (show Mc ∈ maximalTwoLocalOvergroups J from he ▸ Set.mem_singleton Mc).2

/-- The actual residual lies in the preserving preimage, which normalizes
all factor residuals. Only this preimage's proved index is used. -/
theorem source_quintic_residual_normalizes_factor (k : d.Index) :
    residual J ≤ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G) := by
  obtain ⟨hi,hn⟩ := source_quintic_preserving_preimage hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w
  have he : residual (actorPreimage J π.ker) = residual J :=
    embedded_twoResidual_eq_of_relIndex_two (actorPreimage_le J π.ker) hi
  exact (he ▸ residual_le (actorPreimage J π.ker)).trans (hn k)

/-- Each literal factor residual is subnormal in the partner in the
residual-closure branch. This uses relative, not ambient, normality. -/
theorem source_quintic_residual_subnormal
    (hc : residualClosure J Mc = residual J) (k : d.Index) :
    ((residual (actorPreimage J (f.ambientFactor d k).actor)).subgroupOf Mc).IsSubnormal := by
  let B := residual (actorPreimage J (f.ambientFactor d k).actor)
  have hBK : B ≤ residual J := embedded_pResidual_mono 2 (actorPreimage_le J _)
  have hKN : Mc ≤ normalizer (residual J : Set G) := by
    rw [←hc]
    exact le_normalizer_conjugateSpanBy _ _
  let : ((residual J).subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer hKN
  have hn : (residual J).subgroupOf Mc ≤ normalizer (B.subgroupOf Mc : Set Mc) :=
    (comap_mono (source_quintic_residual_normalizes_factor hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π hp w k)).trans (le_normalizer_comap Mc.subtype)
  exact IsSubnormal.step _ _ (subgroupOf_mono Mc hBK)
    (inferInstance : ((residual J).subgroupOf Mc).Normal).isSubnormal
    (normal_subgroupOf_of_le_normalizer hn)

/-- The actual partner two-core normalizes every factor residual, with no
factor-join index premise. -/
theorem source_quintic_core_normalizes_factor
    (hc : residualClosure J Mc = residual J) (k : d.Index) :
    Mc.pCoreIn 2 ≤ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G) := by
  let B := residual (actorPreimage J (f.ambientFactor d k).actor)
  have hB : B ≤ Mc := (residual_le _).trans
    ((actorPreimage_le J _).trans (original_partner_contains hG T hempty hM hu hmany hcard e J hJ))
  let eb := subgroupOfEquivOfLe hB
  have hperfect : IsPPerfect 2 (B.subgroupOf Mc) :=
    (isPPerfect_embedded_pResidual 2 (actorPreimage J (f.ambientFactor d k).actor)).of_surjective
      eb.symm.toMonoidHom eb.symm.surjective
  have hn := le_normalizer_of_isSubnormal_isPPerfect (B.subgroupOf Mc) (pCore 2 Mc)
    (source_quintic_residual_subnormal hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π hp w hc k) hperfect pCore_isPGroup
    (by rw [normalizer_eq_top]; exact le_top)
  have hm := (map_mono hn (f := Mc.subtype)).trans (le_normalizer_map Mc.subtype)
  rwa [map_subgroupOf_eq_of_le hB] at hm

omit hp w in
/-- The central point lies in the intrinsic core of the literal second
normalizer. This supplies the nontrivial-core condition for proper-local K scope. -/
theorem source_quintic_secondNormalizer_point_core (k : d.Index) :
    centralInvolutions T ≤ (normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).pCoreIn 2 := by
  let K := residual (actorPreimage J (f.ambientFactor d k).actor)
  exact (source_factor_residual_point_core hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d k).trans
      (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K)
        ((pCoreIn_le 2 K).trans K.le_normalizer)
        (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))

omit hp w in
/-- The actual second normalizer satisfies the proper-local SQTK hypothesis;
no K-group assertion about the whole simple ambient group is used. -/
theorem source_quintic_secondNormalizer_sqtk (k : d.Index) :
    IsSQTK KnownSimple.IsKnownSimple (normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)) := by
  apply Chapter1.RadicalExclusions.sqtk_of_mem_H hG
  intro hb
  have hz : centralInvolutions T = ⊥ := bot_unique (hb ▸
    source_quintic_secondNormalizer_point_core hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d k)
  have hc := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hc0 : Nat.card (centralInvolutions T) = 1 := (eq_bot_iff_card _).mp hz
  omega

/-- Maximal two-locality identifies the normalizer of the residual closure
in this branch, using the actual point in a factor's intrinsic two-core. -/
theorem source_quintic_residual_closure_normalizer
    (hc : residualClosure J Mc = residual J) :
    normalizer (residualClosure J Mc : Set G) = Mc := by
  let K := residualClosure J Mc
  let B := residual (actorPreimage J (f.ambientFactor d w.factor).actor)
  have hBK : B ≤ K := by
    dsimp only [K]
    rw [hc]
    exact embedded_pResidual_mono 2 (actorPreimage_le J _)
  have hKN : K ≤ normalizer (B : Set G) := by
    dsimp only [K]
    rw [hc]
    exact source_quintic_residual_normalizes_factor hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π hp w w.factor
  have hQ : B.pCoreIn 2 ≤ K.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 B) ((pCoreIn_le 2 B).trans hBK)
      (hKN.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hZ : centralInvolutions T ≤ K.pCoreIn 2 :=
    (source_factor_residual_point_core hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d w.factor).trans hQ
  have hne : K.pCoreIn 2 ≠ ⊥ := by
    intro hb
    have hz := bot_unique (hb ▸ hZ)
    have hzcard := plane_centralInvolutions_card T M hM.1.2 hcard e
    have hzcard0 : Nat.card (centralInvolutions T) = 1 := (eq_bot_iff_card _).mp hz
    omega
  have hMN : Mc ≤ normalizer (K : Set G) := le_normalizer_conjugateSpanBy _ _
  have hNQ : normalizer (K : Set G) ≤ normalizer (K.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image K (pCore 2 K)
  have hmax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).1
  exact le_antisymm (hNQ.trans (hmax.2 ⟨_,hne,isPGroup_pCoreIn 2 K,rfl⟩
    (hMN.trans hNQ))) hMN

/-- The kernel of the literal action of N_G(O²(J)) on its intrinsic core
quotient normalizes every original factor residual. Quotient triviality is
not identified with ordinary centralization. -/
theorem source_quintic_residual_action_kernel_normalizes
    (hc : residualClosure J Mc = residual J) (k : d.Index) :
    ((pCoreNormalizerAction 2 (residual J)).ker).map
        (normalizer (residual J : Set G)).subtype ≤ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G) := by
  have hJM := original_partner_contains hG T hempty hM hu hmany hcard e J hJ
  have hKN : Mc ≤ normalizer (residual J : Set G) := by
    rw [←hc]
    exact le_normalizer_conjugateSpanBy _ _
  have hcore : (residual J).pCoreIn 2 ≤ Mc.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes ((residual_le J).trans hJM) hKN
  exact pCoreNormalizerAction_kernel_normalizes (residual J) _
    (embedded_pResidual_mono 2 (actorPreimage_le J _)) (isPPerfect_embedded_pResidual 2 _)
    (hcore.trans (source_quintic_core_normalizes_factor hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π hp w hc k))

end SourcePairCompatibility.QuinticGeometryParallel
end CFSG.Quasithin.Chapter14.Section06
