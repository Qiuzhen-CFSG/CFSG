module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.CubicExchangedSetup
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Dimensions
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.KernelResidual

/-!
# Cubic actors from the original primitive residual

For the nonsingleton ratio decomposition of the original minimal outside
subgroup, the source classification gives two dihedral factors of a common
prime, either three or five. Each factor's odd kernel is its two-residual,
so its faithful embedding lands in the original quotient's two-residual.
Primitivity at prime three therefore excludes the quintic factor and marks
both actual actors as D₆, with their original embeddings retained.

The literal exchanged-factor consumer now constructs its setup, proves the
residual and quotient orders nine and 72, and gives the required Fitting
containment without an additional cubic-factor marking. The nonsingleton
premise remains explicit: excluding the original singleton branch is still
required for the universal earlier-14.6.12 input.

Source: Aschbacher--Smith 14.6.12(2)--(3), printed p.1031, and the factor
classification D.2.17, printed p.188 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]

variable [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

theorem source_ratio_nonsingleton_cubic_actors
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index)
    (hprim : OddNormalizer.PrimitiveResidual J 3) :
    ∀ k, Nonempty ((f.ambientFactor d k).actor ≃* DihedralGroup 3) := by
  obtain ⟨_,p,m,hpm,hmark,hactors,i,_⟩ :=
    source_ratio_nonsingleton_dihedral hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd hmore
  rcases (ChapterD.CyclicSource.primeDimensionOptions_iff p m).mp hpm with
    ⟨rfl,_⟩ | ⟨rfl,_⟩
  · exact fun k => (hactors k).1
  · obtain ⟨l,hl⟩ := hmark i
    let τ := (f.ambientFactor d i).embedding.groupMap
    have hτ := (f.ambientFactor d i).embedding.group_injective
    have hle : l.kernel.map τ ≤ pResidual 2 (J ⧸ pCore 2 J) := by
      rw [l.kernel_eq_twoResidual]
      exact map_pResidual_le 2 τ
    let q : l.kernel →* pResidual 2 (J ⧸ pCore 2 J) :=
      (τ.comp l.kernel.subtype).codRestrict _ (fun x => hle (mem_map_of_mem τ x.property))
    have hq : Function.Injective q := by
      intro x y hxy
      apply Subtype.ext
      apply hτ
      exact congrArg (fun z : pResidual 2 (J ⧸ pCore 2 J) => (z : J ⧸ pCore 2 J)) hxy
    let := hprim.elementary
    have hp : IsPGroup 3 l.kernel :=
      (IsElementaryAbelian.isPGroup 3 (pResidual 2 (J ⧸ pCore 2 J))).of_injective q hq
    rcases hp.card_eq_or_dvd with h | h
    · rw [hl.card_kernel] at h
      norm_num at h
    · rw [hl.card_kernel] at h
      norm_num at h

/-- The original primitive cubic residual supplies the literal exchanged
setup without an independently asserted marking of the two actors. -/
theorem source_ratio_nonsingleton_cubic_exchanged_setup_of_primitive
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index)
    (hprim : OddNormalizer.PrimitiveResidual J 3) :
    ∃ H0 H1 H2 : Subgroup G,
      OddNormalizer.ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2 := by
  exact source_ratio_nonsingleton_cubic_exchanged_setup
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore
    (source_ratio_nonsingleton_cubic_actors
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore hprim)

/-- These are the exact two orders required by EarlierCubicFactorOrders,
for the same original subgroup and its actual nonsingleton decomposition. -/
theorem source_ratio_nonsingleton_cubic_orders
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index)
    (hprim : OddNormalizer.PrimitiveResidual J 3) :
    Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9 ∧
      Nat.card (J ⧸ pCore 2 J) = 72 := by
  obtain ⟨H0,H1,H2,s⟩ := source_ratio_nonsingleton_cubic_exchanged_setup_of_primitive
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore hprim
  exact ⟨by simpa using s.residual_card,
    by simpa using OddCriticalPair.exchanged_actor_card a (T : Subgroup G) 3 H0 H1 H2 s⟩

/-- The actual original residual-containment consumer now needs only the
primitive cubic hypothesis and the nonsingleton source decomposition. -/
theorem source_ratio_nonsingleton_cubic_residual_le_fittingPreimage_of_primitive
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hmore : 1 < Nat.card d.Index)
    (hprim : OddNormalizer.PrimitiveResidual J 3) :
    residual J ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc := by
  exact source_ratio_nonsingleton_cubic_residual_le_fittingPreimage
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore
    (source_ratio_nonsingleton_cubic_actors
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hmore hprim)

end CFSG.Quasithin.Chapter14.Section06
