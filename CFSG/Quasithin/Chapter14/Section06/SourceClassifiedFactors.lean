module
public import CFSG.Quasithin.Chapter14.Section06.SourceFactorMovement
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ClassifiedFactors
public import CFSG.Quasithin.Chapter14.Section02.OutsideParabolic
/-!
# Classified factors in the original solvable plane branch

The actual outside subgroup is an SQTK cover of its literal two-core
quotient. The quadratic bound and Fitting-moved decomposition therefore
supply all hypotheses of the completed D.2 factor classification. Every
factor's starred actors are precisely its Sylow two-subgroups, so original
conjugation permutes the embedded actors and their exact support spaces.
The primitive odd residual lies in the kernel of this permutation action.

The last theorem constructs the decomposition and permutation directly
from an original odd-core counterexample. This is the factor-permutation
step of 14.6.12(2); the subsequent exclusion of a single elementary-nine
factor and the exchanged dihedral conclusion remain separate obligations.

Source: Aschbacher--Smith, 14.6.11--12, printed pp.1030--1031, and D.2.17.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab


/-- The source cover classifies each actual ratio factor's starred subgroups. -/
theorem source_ratio_factor_starred_sylow
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (i : d.Index) (A : Subgroup (d.factor i).Carrier) :
    A ∈ ChapterD.QhatStar (d.factor i).action ↔
      ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A := by
  let := hs
  let : (ChapterD.Jhat a.representation).Normal := ChapterD.Jhat_normal a.representation
  obtain ⟨_,_,_,hcover,_,_⟩ := Section02.source_lemma_14_2_2_8_minimal
    hG T hempty hM hu hmany hcard e J hJ
  have hq : cubicRatio a.representation ≤ 2 := (cubicRatio_le_quadraticRatio _).trans
    (source_rankTwo_quadratic_bound_of_action hG T hempty hM hu hmany hcard e hab J hJ.1 a)
  exact f.factor_starred_sylow_iff d (pCore_quotient_pCore_eq_bot 2) hq hd hcover
    (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _) i A

/-- Original conjugation permutes the literal actors and their exact support spaces. -/
theorem source_ratio_factor_permutation
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull) :
    ∃ π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index,
      (⋃ i, f.ambientBlock d i) = ChapterD.QhatStar a.representation ∧
      pResidual 2 (J ⧸ pCore 2 J) ≤ π.ker ∧ ∀ g i,
      Subgroup.map (MulAut.conj g).toMonoidHom '' f.ambientBlock d i = f.ambientBlock d (π g i) ∧
      (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (f.ambientFactor d (π g i)).actor ∧
      (f.ambientFactor d i).space.map (a.representation g) = (f.ambientFactor d (π g i)).space := by
  obtain ⟨π,hblocks,hker,hperm⟩ := f.source_Jhat_partition_action rfl d
    (source_ratio_factor_starred_sylow hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd)
  exact ⟨π,hblocks,(source_solvable_minimal_residual_le_Jhat
    hG T hempty hM hu hmany hcard e hab J hJ hs a).trans hker,hperm⟩

/-- The original odd-core counterexample supplies the classified factors
and the action on them; no decomposition or recognition premise is retained. -/
theorem source_oddCore_counterexample_classified_factors
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G) (_hJ : J ∈ Chapter3.HStar (T : Subgroup G) M),
      J ≤ H ∧ Group.IsSolvable J ∧
      ∃ _hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J),
      ∃ a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T),
      ∃ f : ChapterD.RatioDecomposition.FactorData a.representation
          (ChapterD.Jhat a.representation)
          (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))),
      ∃ d : ChapterD.RatioDecomposition.Decomposition f.representation,
        d.FittingFull ∧ ∃ π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index,
          (⋃ i, f.ambientBlock d i) = ChapterD.QhatStar a.representation ∧
          pResidual 2 (J ⧸ pCore 2 J) ≤ π.ker ∧ ∀ g i,
          Subgroup.map (MulAut.conj g).toMonoidHom '' f.ambientBlock d i =
            f.ambientBlock d (π g i) ∧
          (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
            (f.ambientFactor d (π g i)).actor ∧
          (f.ambientFactor d i).space.map (a.representation g) =
            (f.ambientFactor d (π g i)).space := by
  obtain ⟨J,hJ,hJH,hs,hU,a,f,d,hd⟩ := source_oddCore_counterexample_decomposition
    hG T hempty hM hu hmany hcard e hab H hH hne
  let := hU
  exact ⟨J,hJ,hJH,hs,hU,a,f,d,hd,source_ratio_factor_permutation
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd⟩

end CFSG.Quasithin.Chapter14.Section06
