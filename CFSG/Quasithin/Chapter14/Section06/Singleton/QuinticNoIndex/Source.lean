module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.StrictClosure
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.Wreath
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.FiveSylow
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.Intersections
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.ResidualNormalizer
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.Reduction

/-!
# The original factor-kernel reduction and strict component closure

Apply the no-index residual-action calculation to the same J, quotient map,
ratio factors and factor permutation produced by the original nonsingleton
reduction. Failure of the kernel identification retains the actual D10
markings and outer rotation and forces a Sylow image divisible by sixteen.
Thus the order-eight signed marking used after 14.6.12 cannot be supplied
in this branch before proving the missing kernel identification.

This is a refinement of the literal singleton owner's two-factor branch,
not a proof of 14.6.12. The strict closure now has actual PSL₂(16) components,
its two-factor quotient, residual and generalized-Fitting identifications,
and a faithful marked wreath action with Mc = K_z T. The original J has
index prime to five in Mc. The actual exchanged-component interface is
constructed without the factor-join index: both intrinsic models, both
normalizer indices, the second intersection core and the ordinary
central-point closure are proved. Each component meets J in an intersection
whose two-core is its Sylow intersection and whose quotient has order five.
In the residual-closure branch each original factor normalizer has index
two or six; index six forces a cubic divisor of the relative index of J
in Mc. When all these indices are two, the actual critical-pair argument
supplies the escaping second normalizer, characteristic two and C.2.3.
Excluding index six, original-factor alignment in strict closure, full
outer-image comparison and the final contradiction remain open.
Source: Aschbacher--Smith 14.6.12, p.1031, 14.6.14, p.1033,
and 14.6.15, p.1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open OddNormalizer Chapter1 Chapter1.XiEmbedding
open Chapter13.Section08.Components.Models Chapter13.Section08.Components.SourceModels
open OddNormalizer.Quintic.ModuleGeometry (residualPartnerAction)
open SourcePairCompatibility.QuinticGeometryParallel (actorPreimage)
namespace Singleton.QuinticNoIndex
variable {G : Type*} [Group G] [Finite G]

/-- The same factor permutation either has the required dihedral kernel,
or its actual quintic outer branch has a larger intrinsic Sylow action.
The residual-closure equality is retained only for the latter action. -/
theorem source_ratio_nonsingleton_large_action_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index) :
    ∃ π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index,
      ChapterD.Jhat a.representation ≤ π.ker ∧
      (π.ker.comap (QuotientGroup.mk' (pCore 2 J))).index = 2 ∧
      (∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (f.ambientFactor d (π g i)).actor) ∧
      (∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j) ∧
      ((ChapterD.Jhat a.representation = π.ker ∧
          (ChapterD.Jhat a.representation).index = 2) ∨
        (Nonempty (SourcePairCompatibility.QuinticOuterAction a f d π) ∧
          200 < Nat.card (J ⧸ pCore 2 J) ∧
          ∀ hc : residualClosure J Mc = GenerationOne.residual J,
            16 ∣ Nat.card (((T : Subgroup G).subgroupOf Mc).map
              (residualPartnerAction Mc J hc)))) := by
  obtain ⟨π,hker,hindex,hp,ht,hcases⟩ := source_ratio_nonsingleton_kernel_reduction
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore
  refine ⟨π,hker,hindex,hp,ht,?_⟩
  rcases hcases with hdone | houter
  · exact Or.inl hdone
  · let w := houter.some
    exact Or.inr ⟨houter,
      source_quintic_outer_quotient_card hG T hempty hM hu hmany hcard e hab
        J hJ hs a f d π w hker hp,
      fun hc => source_quintic_outer_sylow_action_card hG T hempty hM hu hmany hcard e hab
        J hJ hs a f d π w hker hp hc⟩

/-- The literal singleton-owner reduction now distinguishes the large
Sylow-action residual branch from the actual exchanged-component closure.
All factors, quotient maps, and the outer rotation witness are retained. -/
theorem source_ratio_nonsingleton_closure_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index) :
    ∃ π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index,
      ChapterD.Jhat a.representation ≤ π.ker ∧
      (π.ker.comap (QuotientGroup.mk' (pCore 2 J))).index = 2 ∧
      (∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (f.ambientFactor d (π g i)).actor) ∧
      (∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j) ∧
      ((ChapterD.Jhat a.representation = π.ker ∧
          (ChapterD.Jhat a.representation).index = 2) ∨
        (Nonempty (SourcePairCompatibility.QuinticOuterAction a f d π) ∧
          200 < Nat.card (J ⧸ pCore 2 J) ∧
          ((∃ hc : residualClosure J Mc = GenerationOne.residual J,
              16 ∣ Nat.card (((T : Subgroup G).subgroupOf Mc).map
                (residualPartnerAction Mc J hc))) ∨
            (residualClosure J Mc ≠ GenerationOne.residual J ∧
              ∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
                IsQuasisimple (XiQuotient L) ∧
                residualClosure J Mc = componentOrbit L (T : Subgroup G) ∧
                (Mc ⊓ normalizer (L : Set G)).relIndex Mc = 2 ∧
                (∃ s ∈ (T : Subgroup G), s ∉ normalizer (L : Set G) ∧
                  (residualClosure J Mc : Set G) = (L : Set G) *
                    (L.map (MulAut.conj s⁻¹).toMonoidHom : Set G)) ∧
                Nonempty (XiQuotient (residualClosure J Mc) ≃*
                  XiQuotient L × XiQuotient L) ∧
                NonnormalF918Models (XiQuotient L))))) := by
  classical
  obtain ⟨π,hker,hindex,hp,ht,hcases⟩ := source_ratio_nonsingleton_large_action_reduction
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore
  refine ⟨π,hker,hindex,hp,ht,?_⟩
  rcases hcases with hdone | ⟨houter,hsize,hlarge⟩
  · exact Or.inl hdone
  · refine Or.inr ⟨houter,hsize,?_⟩
    by_cases hc : residualClosure J Mc = GenerationOne.residual J
    · exact Or.inl ⟨hc,hlarge hc⟩
    · exact Or.inr ⟨hc,source_quintic_strict_closure_geometry
        hG T hempty hM hu hmany hcard e hab J hJ hs a f d π houter.some hc⟩

/-- The singleton owner's actual kernel reduction, retaining the same D10
factors and outer rotation, now has a fully marked strict-closure action.
The residual-branch normalizer and outer contradiction remain unresolved. -/
theorem source_ratio_nonsingleton_marked_closure_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index) :
    ∃ π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index,
      ChapterD.Jhat a.representation ≤ π.ker ∧
      (π.ker.comap (QuotientGroup.mk' (pCore 2 J))).index = 2 ∧
      (∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (f.ambientFactor d (π g i)).actor) ∧
      (∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j) ∧
      ((ChapterD.Jhat a.representation = π.ker ∧
          (ChapterD.Jhat a.representation).index = 2) ∨
        (Nonempty (SourcePairCompatibility.QuinticOuterAction a f d π) ∧
          200 < Nat.card (J ⧸ pCore 2 J) ∧
          ((∃ hc : residualClosure J Mc = GenerationOne.residual J,
              16 ∣ Nat.card (((T : Subgroup G).subgroupOf Mc).map
                (residualPartnerAction Mc J hc))) ∨
            (residualClosure J Mc ≠ GenerationOne.residual J ∧
              ¬5 ∣ J.relIndex Mc ∧
              ∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
                IsQuasisimple (XiQuotient L) ∧
                residualClosure J Mc = componentOrbit L (T : Subgroup G) ∧
                (Mc ⊓ normalizer (L : Set G)).relIndex Mc = 2 ∧
                ClassicalGroup.IsPSL
                  ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 16 ∧
                5 ∣ Nat.card (L ⊓ J : Subgroup G) ∧
                Mc = residualClosure J Mc ⊔ (T : Subgroup G) ∧
                residualClosure J Mc = (primeToResidual 5 Mc).map Mc.subtype ∧
                residualClosure J Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
                StrictClosureLayer Mc (residualClosure J Mc) ∧
                ∃ s : Mc, (s : G) ∈ (T : Subgroup G) ∧
                  (s : G) ∉ normalizer (L : Set G) ∧
                  (residualClosure J Mc : Set G) = (L : Set G) *
                    (L.map (MulAut.conj (s : G)⁻¹).toMonoidHom : Set G) ∧
                  MarkedExchangedWreath Mc (residualClosure J Mc) L s
                    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)))))) := by
  classical
  obtain ⟨π,hker,hindex,hp,ht,hcases⟩ := source_ratio_nonsingleton_large_action_reduction
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore
  refine ⟨π,hker,hindex,hp,ht,?_⟩
  rcases hcases with hdone | ⟨houter,hsize,hlarge⟩
  · exact Or.inl hdone
  · refine Or.inr ⟨houter,hsize,?_⟩
    by_cases hc : residualClosure J Mc = GenerationOne.residual J
    · exact Or.inl ⟨hc,hlarge hc⟩
    · obtain ⟨L,hLM,hL,hq,hcl,hi,hmodel,hgen,hr5,hr3,hlayer,hmarked⟩ :=
        source_quintic_strict_closure_wreath
          hG T hempty hM hu hmany hcard e hab J hJ hs a f d π houter.some hc
      have hindex5 := source_quintic_strict_outside_index_primeTo_five
        hG T hempty hM hu hmany hcard e hab J hJ hs a f d π houter.some hc
      have hinter := source_quintic_strict_component_intersection_five_dvd
        hG T hempty hM hu hmany hcard e hab J hJ hs a f d π houter.some hc hLM hL hmodel
      exact Or.inr ⟨hc,hindex5,L,hLM,hL,hq,hcl,hi,hmodel,hinter,hgen,hr5,hr3,hlayer,hmarked⟩

/-- The original singleton kernel reduction now constructs the actual
exchanged-component interface and computes both intersection quotients.
The original outer rotation and the residual-action branch remain explicit;
the comparison with the original D10 supports is still required. -/
theorem source_ratio_nonsingleton_component_intersection_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index) :
    ∃ π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index,
      ChapterD.Jhat a.representation ≤ π.ker ∧
      (π.ker.comap (QuotientGroup.mk' (pCore 2 J))).index = 2 ∧
      (∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (f.ambientFactor d (π g i)).actor) ∧
      (∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j) ∧
      ((ChapterD.Jhat a.representation = π.ker ∧
          (ChapterD.Jhat a.representation).index = 2) ∨
        (Nonempty (SourcePairCompatibility.QuinticOuterAction a f d π) ∧
          200 < Nat.card (J ⧸ pCore 2 J) ∧
          ((∃ hc : residualClosure J Mc = GenerationOne.residual J,
              16 ∣ Nat.card (((T : Subgroup G).subgroupOf Mc).map
                (residualPartnerAction Mc J hc))) ∨
            (residualClosure J Mc ≠ GenerationOne.residual J ∧
              ¬5 ∣ J.relIndex Mc ∧
              ∃ b : OddNormalizer.Quintic.ModuleGeometry.ExchangedFactorData
                  (T : Subgroup G) Mc J (centralInvolutions T),
                (b.K1 ⊓ J).pCoreIn 2 = b.K1 ⊓ (T : Subgroup G) ∧
                (b.K2 ⊓ J).pCoreIn 2 = b.K2 ⊓ (T : Subgroup G) ∧
                Nat.card ((b.K1 ⊓ J : Subgroup G) ⧸ pCore 2 (b.K1 ⊓ J : Subgroup G)) = 5 ∧
                Nat.card ((b.K2 ⊓ J : Subgroup G) ⧸ pCore 2 (b.K2 ⊓ J : Subgroup G)) = 5)))) := by
  classical
  obtain ⟨π,hker,hindex,hp,ht,hcases⟩ := source_ratio_nonsingleton_large_action_reduction
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore
  refine ⟨π,hker,hindex,hp,ht,?_⟩
  rcases hcases with hdone | ⟨houter,hsize,hlarge⟩
  · exact Or.inl hdone
  · refine Or.inr ⟨houter,hsize,?_⟩
    by_cases hc : residualClosure J Mc = GenerationOne.residual J
    · exact Or.inl ⟨hc,hlarge hc⟩
    · exact Or.inr ⟨hc,
        source_quintic_strict_outside_index_primeTo_five
          hG T hempty hM hu hmany hcard e hab J hJ hs a f d π houter.some hc,
        source_quintic_strict_component_intersections
          hG T hempty hM hu hmany hcard e hab J hJ hs a f d π houter.some hc⟩

/-- Apply the residual normalizer dichotomy to the literal singleton kernel
reduction. The residual branch either has an index-six factor normalizer
and a cubic divisor of Mc/J, or supplies the actual escaping second
normalizer with characteristic two and C.2.3. The strict branch retains
both component intersection quotients. Neither branch is declared excluded. -/
theorem source_ratio_nonsingleton_normalizer_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index) :
    letI : IsElementaryAbelian 2 (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩) :=
      inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J))
    ∃ π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index,
      ChapterD.Jhat a.representation ≤ π.ker ∧
      (π.ker.comap (QuotientGroup.mk' (pCore 2 J))).index = 2 ∧
      (∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (f.ambientFactor d (π g i)).actor) ∧
      (∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j) ∧
      ((ChapterD.Jhat a.representation = π.ker ∧
          (ChapterD.Jhat a.representation).index = 2) ∨
        (Nonempty (SourcePairCompatibility.QuinticOuterAction a f d π) ∧
          200 < Nat.card (J ⧸ pCore 2 J) ∧
          ((∃ hc : residualClosure J Mc = GenerationOne.residual J,
              16 ∣ Nat.card (((T : Subgroup G).subgroupOf Mc).map
                (residualPartnerAction Mc J hc)) ∧
              ((∃ k : d.Index, (Mc ⊓ normalizer
                (GenerationOne.residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex Mc = 6 ∧
                  3 ∣ J.relIndex Mc) ∨
                (∃ i j : d.Index, i ≠ j ∧
                  ∃ c : Quintic.CriticalPair
                    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1)
                      a Mc (actorPreimage J (f.ambientFactor d i).actor),
                    let N := normalizer
                      (GenerationOne.residual (actorPreimage J (f.ambientFactor d j).actor) : Set G)
                    c.endpoint.representative ∈ N ∧ ¬N ≤ Mc ∧
                      Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
                        N (Mc.pCoreIn 2) (Mc ⊓ N) ∧
                      generalizedFitting N = pCore 2 N ∧
                      ((T : Subgroup G) ⊓ N).relIndex T = 2))) ∨
            (residualClosure J Mc ≠ GenerationOne.residual J ∧
              ¬5 ∣ J.relIndex Mc ∧
              ∃ b : OddNormalizer.Quintic.ModuleGeometry.ExchangedFactorData
                  (T : Subgroup G) Mc J (centralInvolutions T),
                (b.K1 ⊓ J).pCoreIn 2 = b.K1 ⊓ (T : Subgroup G) ∧
                (b.K2 ⊓ J).pCoreIn 2 = b.K2 ⊓ (T : Subgroup G) ∧
                Nat.card ((b.K1 ⊓ J : Subgroup G) ⧸ pCore 2 (b.K1 ⊓ J : Subgroup G)) = 5 ∧
                Nat.card ((b.K2 ⊓ J : Subgroup G) ⧸ pCore 2 (b.K2 ⊓ J : Subgroup G)) = 5)))) := by
  classical
  obtain ⟨π,hker,hindex,hp,ht,hcases⟩ := source_ratio_nonsingleton_large_action_reduction
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore
  refine ⟨π,hker,hindex,hp,ht,?_⟩
  rcases hcases with hdone | ⟨houter,hsize,hlarge⟩
  · exact Or.inl hdone
  · refine Or.inr ⟨houter,hsize,?_⟩
    by_cases hc : residualClosure J Mc = GenerationOne.residual J
    · exact Or.inl ⟨hc,hlarge hc,source_quintic_residual_branch_dichotomy
        hG T hempty hM hu hmany hcard e hab J hJ hs a f d π hp houter.some hd hc⟩
    · exact Or.inr ⟨hc,
        source_quintic_strict_outside_index_primeTo_five
          hG T hempty hM hu hmany hcard e hab J hJ hs a f d π houter.some hc,
        source_quintic_strict_component_intersections
          hG T hempty hM hu hmany hcard e hab J hJ hs a f d π houter.some hc⟩

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
