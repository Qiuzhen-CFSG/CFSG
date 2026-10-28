module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.Critical
public import Theory.SpecificGroups.QuinticInvolutionCommutator

/-!
# Critical geometry of the original quintic pair

An involution in a marked D10 factor is Sylow and hence starred. Its fixed
codimension is the common cubic ratio of the actual decomposition. Its
order-five commutator forces displacement at least two; the original
quadratic bound gives the reverse inequality. Thus the ratio is exactly two.

The source consumer applies this to the literal QuinticOuterAction. Every
original critical conjugate escapes O2(J), leaves Mc, and has a reciprocal
endpoint restoring all J-normalized labels with one conjugator. This
supplies critical geometry without identifying Jhat with the factor kernel.
The remaining ambient exclusion of the outer action is not proved here.

Source: Aschbacher--Smith 14.6.12--13, printed pp.1031--1032, D.2.17(2),
p.188, and F.9.13--17, pp.322--324 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
namespace SourcePairCompatibility.QuinticGeometry
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

/-- The actual quintic factor forces the minimum cubic ratio to be two. -/
theorem source_quintic_pair_ratio_two
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π) :
    cubicRatio a.representation = 2 := by
  classical
  let F := d.factor w.factor
  let E : F.Carrier ≃* DihedralGroup 5 :=
    (MonoidHom.ofInjective (f.ambientFactor d w.factor).embedding.group_injective).trans w.marking
  let t : F.Carrier := E.symm (DihedralGroup.sr 0)
  have ht : orderOf t = 2 :=
    (E.symm.orderOf_eq (DihedralGroup.sr 0)).trans (DihedralGroup.orderOf_sr _)
  have hc : Nat.card F.Carrier = 10 :=
    (Nat.card_congr E.toEquiv).trans DihedralGroup.nat_card
  have hct : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers,ht]
  have hidx : (zpowers t).index = 5 := by
    have hh := (zpowers t).card_mul_index
    rw [hct,hc] at hh
    omega
  have hpt : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hct)
  let S : Sylow 2 F.Carrier := hpt.toSylow (by rw [hidx]; decide)
  have hstar : zpowers t ∈ ChapterD.QhatStar F.action :=
    (source_ratio_factor_starred_sylow hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd w.factor _).mpr ⟨S,rfl⟩
  have hr : rank (zpowers t) = 1 := by rw [rank,hct]; decide
  have hcod := ChapterD.CyclicSource.starred_codimension F.action hstar hr
  obtain ⟨x,hx⟩ := Theory.SpecificGroups.exists_order_five_commutator_of_quintic_model
    (Or.inl ⟨E⟩) t ht
  have hlow : 2 ≤ fixedCodim F.action (zpowers t) := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact two_le_displacement_of_commutator_order_five F.action F.faithful t x hx
  have hupper : cubicRatio a.representation ≤ 2 :=
    (cubicRatio_le_quadraticRatio _).trans
      (source_rankTwo_quadratic_bound_of_action hG T hempty hM hu hmany hcard e hab J hJ.1 a)
  apply le_antisymm hupper
  have hl : (2 : ENNReal) ≤ fixedCodim F.action (zpowers t) := by exact_mod_cast hlow
  rw [hcod,F.embedding.ratio,f.ratio] at hl
  exact hl

/-- Every original critical endpoint of the quintic pair escapes the core and
has a reciprocal endpoint on the same labels. Kernel equality is not used. -/
theorem source_quintic_pair_critical_reciprocity
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π) :
    cubicRatio a.representation = 2 ∧
    (let D : ChapterF.Section09.Setup G :=
       ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
     let h : D.Hypothesis := source_rankTwo_f9_hypothesis
       hG T hempty hM hu hmany hcard e hab J hJ.1
     3 ≤ h.b ∧ Odd h.b ∧ Nonempty h.CriticalEndpoint ∧
       ∀ i : h.CriticalEndpoint,
         i.representative ∉ Mc ∧ ¬ i.conjugate D.UH ≤ D.QH ∧
         ∃ j : h.CriticalEndpoint, ∀ A : Subgroup G,
           J ≤ normalizer (A : Set G) →
           (i.conjugate A).map (MulAut.conj j.representative).toMonoidHom = A) := by
  have hq := source_quintic_pair_ratio_two hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d hd π w
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis
    hG T hempty hM hu hmany hcard e hab J hJ.1
  obtain ⟨hb,ho,hne⟩ := source_rankTwo_critical_track_bounds
    hG T hempty hM hu hmany hcard e hab J hJ.1
  refine ⟨hq,hb,ho,hne,fun i => ?_⟩
  have hn := source_rankTwo_critical_core_escape_of_ratio_two
    hG T hempty hM hu hmany hcard e hab J hJ.1 a hq i
  exact ⟨source_rankTwo_critical_not_mem_Mc
    hG T hempty hM hu hmany hcard e hab J hJ.1 i,hn,i.reverse_labels hb hn⟩

end SourcePairCompatibility.QuinticGeometry
end CFSG.Quasithin.Chapter14.Section06
