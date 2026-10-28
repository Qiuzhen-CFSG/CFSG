module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.Models
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.ExchangedAction

/-!
# The marked strict-closure action before the missing index

The literal closure image is the generalized Fitting subgroup and is a
product of two PSL₂(16) components. Conjugation therefore embeds the actual
Mc/O₂(Mc) into the automorphism wreath product. The component outer groups
are two-groups, giving Mc = K_z T. Both inner coordinates and the original
inverse-conjugating exchanger are retained in MarkedExchangedWreath.

Source applies the result to the same quintic outer witness in the original
singleton reduction. This is a faithful marked action, not a claim that
its image is the full wreath product. Original-factor alignment and the
final outer contradiction remain open. Source: Aschbacher--Smith,
14.6.14, printed p.1033, without assuming the earlier 14.6.12 index.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer Chapter1 Chapter1.XiEmbedding
namespace Singleton.QuinticNoIndex
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
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)



include hG hempty hM hu hmany hcard e hab hJ hs w

/-- The strict branch has a faithful action on the actual PSL₂(16) square,
with the original component, exchanger, quotient maps and inner action.
No index of the factor join is used. -/
theorem source_quintic_strict_closure_wreath
    (hne : residualClosure J Mc ≠ residual J) :
    ∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
      IsQuasisimple (XiQuotient L) ∧
      residualClosure J Mc = componentOrbit L (T : Subgroup G) ∧
      (Mc ⊓ normalizer (L : Set G)).relIndex Mc = 2 ∧
      ClassicalGroup.IsPSL
        ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 16 ∧
      Mc = residualClosure J Mc ⊔ (T : Subgroup G) ∧
      residualClosure J Mc = (primeToResidual 5 Mc).map Mc.subtype ∧
      residualClosure J Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
      StrictClosureLayer Mc (residualClosure J Mc) ∧
      ∃ s : Mc, (s : G) ∈ (T : Subgroup G) ∧ (s : G) ∉ normalizer (L : Set G) ∧
        (residualClosure J Mc : Set G) = (L : Set G) *
          (L.map (MulAut.conj (s : G)⁻¹).toMonoidHom : Set G) ∧
        MarkedExchangedWreath Mc (residualClosure J Mc) L s
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
  obtain ⟨L,hLM,hL,hq,hcl,hi,hex,hmodel,hr5,hr3,hlayer⟩ :=
    source_quintic_strict_closure_layer hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w hne
  have hTMc : (T : Subgroup G) ≤ Mc := AlternatingThree.sylow_le_partner T hu
  obtain ⟨hgen,s,hsT,hsn,hprod,ha⟩ := exchanged_closure_wreath_rows
    (p := 5) hTMc hLM hL hq
    ⟨T.subtype hTMc,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]⟩
    hex hlayer (Or.inr (Or.inl ⟨rfl,hmodel⟩))
  refine ⟨L,hLM,hL,hq,hcl,hi,hmodel,hgen,hr5,hr3,hlayer,s,hsT,hsn,hprod,?_⟩
  rcases ha with ⟨hfalse,_⟩ | ⟨_,ha⟩ | ⟨hfalse,_⟩
  · omega
  · exact ha
  · omega

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
