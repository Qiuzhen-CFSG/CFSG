module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.PointCentralizer
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.Normalizer
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.PointClosure

/-!
# The source critical endpoint in the no-index residual branch

Select the actual CriticalPair already constructed without an index of Jhat.
In the residual-closure branch, the ambient normalizer index gives the
ordinary quintic point-centralizer identity. Its conjugated identity makes the same critical element normalize the
opposite literal factor residual. This supplies the escaping second normalizer,
its C.2.3 setup, characteristic two, and the original Sylow index.

The residual-closure branch assumption and the ambient normalizer index
remain explicit source obligations. This is a conditional residual-branch
consumer, not the original 14.6.12 conclusion or a quintic exclusion.
Source: Aschbacher--Smith 14.6.13(2) and 14.6.15, pp.1032,1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
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

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J))

/-- The no-index critical endpoint supplies the actual second-normalizer
route in the residual-closure branch once the ambient index is proved. -/
theorem source_quintic_residual_branch_secondNormalizer (hd : d.FittingFull)
    (hc : residualClosure J Mc = residual J)
    (hindex : ∀ k : d.Index, (Mc ⊓ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex Mc = 2) :
    ∃ i j : d.Index, i ≠ j ∧
      ∃ c : Quintic.CriticalPair
        (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1)
          a Mc (actorPreimage J (f.ambientFactor d i).actor),
        let N := normalizer (residual (actorPreimage J (f.ambientFactor d j).actor) : Set G)
        c.endpoint.representative ∈ N ∧ ¬N ≤ Mc ∧
          Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
            N (Mc.pCoreIn 2) (Mc ⊓ N) ∧
          generalizedFitting N = pCore 2 N ∧
          ((T : Subgroup G) ⊓ N).relIndex T = 2 := by
  have hpoint := source_quintic_residual_point_closure hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w hd hc hindex
  obtain ⟨i,⟨c⟩⟩ := source_quintic_critical_pair hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w hd
  obtain ⟨k,l,hkl,_⟩ := f.two_factor_moved_decomposition d w.two_factors
  obtain ⟨j,hij⟩ : ∃ j : d.Index, i ≠ j := by
    by_cases hik : i = k
    · exact ⟨l,hik ▸ hkl⟩
    · exact ⟨k,hik⟩
  obtain ⟨hg,hout⟩ := source_quintic_critical_normalizer_of_point_closure
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d π hp w i j hij c hpoint
  obtain ⟨hsetup,hchar⟩ := source_quintic_secondNormalizer_setup_of_index
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d π hp w hc j (hindex j)
  exact ⟨i,j,hij,c,hg,hout,hsetup,hchar,
    (source_quintic_residual_normalizer_indices hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π hp w hd j).1⟩

end SourcePairCompatibility.QuinticGeometryParallel
end CFSG.Quasithin.Chapter14.Section06
