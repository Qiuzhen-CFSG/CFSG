module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.StrictClosure
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.Comparison
public import CFSG.Quasithin.Chapter14.Section06.SourceSolvableSelection

/-!
# The strict quintic closure without the factor-join index

The source prime-preserving descent bounds every odd core prime by five.
Consequently the detected exchanged component has the actual PSL₂(16)
quotient: the Borel torus bounds the field parameter, and the other F.9.18
rows are excluded. The literal component product then identifies the closure
with both O^{5′}(Mc) and O^{3′}(Mc); centralizer prime bounds make its image
F*(Mc/O₂(Mc)). No ExchangedFactorSetup or factor-join index is used.

The marked square action is constructed in Wreath, and Source applies it
to the singleton owner's actual factor-kernel reduction. The residual-branch
Mc-normalizer bound, original-factor alignment and outer contradiction
remain open. Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033,
used here before the missing index assertion of 14.6.12(2), p.1031.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer Chapter1 Chapter1.XiEmbedding
open Chapter13.Section08.Components.Models Chapter13.Section08.Components.SourceModels
namespace Singleton.QuinticNoIndex
open SourcePairCompatibility.QuinticGeometryParallel
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


include hG hempty hM hu hmany hcard e hab

/-- Every odd prime core in the original outside family has prime at most five.
The descent preserves its prime and uses no index of the factor join. -/
theorem source_quintic_maximal_prime : MaximalOddPrime (T : Subgroup G) M 5 := by
  intro H hH p hp ho hne
  obtain ⟨J',_,_,_,hp35,_⟩ := source_minimal_outside_of_primeCore
    hG T hempty hM hu hmany hcard e hab H hH p hp ho hne
  rcases hp35 with rfl | rfl <;> omega

include hJ hs w

/-- The detected strict component is PSL₂(16) on the literal image in
Mc/O₂(Mc). The two-parabolic source setup and original five-plane are retained;
no index of Jhat or full wreath action is assumed. -/
theorem source_quintic_strict_closure_model
    (hne : residualClosure J Mc ≠ residual J) :
    ∃ P L : Subgroup G,
      residualClosure J Mc = componentOrbit L (T : Subgroup G) ∧
      Nonempty (SwappedSylowInput KnownSimple.IsKnownSimple 5
        (T : Subgroup G) (residual J) P Mc L) ∧
      ClassicalGroup.IsPSL
        ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 16 := by
  obtain ⟨P,L,hcl,⟨hS⟩,_⟩ := source_quintic_strict_closure_swapped
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w hne
  have hprim := source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  have hmax := source_quintic_maximal_prime hG T hempty hM hu hmany hcard e hab
  have hm := source_swapped_closure_model hG T hempty hM hu hmany hcard e hab
    J hJ.1 hS hprim (Or.inr rfl) hmax
  have hJMc : J ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hu)
  refine ⟨P,L,hcl,⟨hS⟩,?_⟩
  rcases hm.2 with ⟨m,hm,_,hcong,hbin⟩ | ⟨hfalse,_⟩
  · rcases source_binary_component_field_parameter hG T hu hJ.1 hJMc (Or.inr rfl) hmax
      hprim L hS.component.2 hm hbin hcong with ⟨hfalse,_⟩ | ⟨_,rfl⟩
    · omega
    · simpa using hbin
  · omega

/-- In the no-index strict branch the literal closure is both O^{5′}(Mc)
and O^{3′}(Mc), and its image is F*(Mc/O₂(Mc)). These identifications precede
the still missing full outer action and original-factor alignment. -/
theorem source_quintic_strict_closure_layer
    (hne : residualClosure J Mc ≠ residual J) :
    ∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
      IsQuasisimple (XiQuotient L) ∧
      residualClosure J Mc = componentOrbit L (T : Subgroup G) ∧
      (Mc ⊓ normalizer (L : Set G)).relIndex Mc = 2 ∧
      (∃ s ∈ (T : Subgroup G), s ∉ normalizer (L : Set G) ∧
        (residualClosure J Mc : Set G) = (L : Set G) *
          (L.map (MulAut.conj s⁻¹).toMonoidHom : Set G)) ∧
      ClassicalGroup.IsPSL
        ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 16 ∧
      residualClosure J Mc = (primeToResidual 5 Mc).map Mc.subtype ∧
      residualClosure J Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
      StrictClosureLayer Mc (residualClosure J Mc) := by
  obtain ⟨P,L,hcl,⟨hS⟩,hbin⟩ := source_quintic_strict_closure_model
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w hne
  have hprim := source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  have hmax := source_quintic_maximal_prime hG T hempty hM hu hmany hcard e hab
  have hJMc : J ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hu)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu.symm ▸ Set.mem_singleton Mc
  have hsq := hG.twoLocal_sqtk hMc.1.1
  have hTMc : (T : Subgroup G) ≤ Mc := hJ.1.1.2.trans hJMc
  obtain ⟨hi,_⟩ := SwappedSylow.nonnormal_model_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hS.toSwappedInput
  have hi' : (Mc ⊓ normalizer (L : Set G)).relIndex Mc = 2 := by
    rw [←subgroupOf_normalizer_eq hS.component.1] at hi
    rw [inf_relIndex_left]
    exact hi
  have hex := (swapped_closure_product hS).1
  rw [←hcl] at hex
  refine ⟨L,hS.component.1,hS.component.2,hS.quasisimple,hcl,hi',hex,hbin,?_⟩
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hbin
  have hF' : Nat.card F = 2 ^ 4 := hF
  have hd : 5 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    let S : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := default
    exact (by decide : 5 ∣ 2 ^ 4 - 1).trans
      ((binary_psl2_sylow_normalizer_torus_dvd F (by decide) hF' S).trans
        (normalizer (S : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))).card_subgroup_dvd_card)
  obtain ⟨hres,hc5⟩ := exchanged_binary_closure_residual_and_centralizer
    hTMc hS.component.1 hS.component.2 hsq.stronglyQuasithin hex F (by decide : 2 ≤ 4)
    hF' eF 5 (by decide) hd
  obtain ⟨hres3,hc3⟩ := exchanged_binary_closure_residual_and_centralizer
    hTMc hS.component.1 hS.component.2 hsq.stronglyQuasithin hex F (by decide : 2 ≤ 4)
    hF' eF 3 (by decide)
    (Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F 2 (by decide))
  let K := ((residualClosure J Mc).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))
  let ec : XiQuotient L ≃* ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hS.component.1)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hS.component.1))).symm.trans
      (cComponentTwoCoreQuotientEquiv hS.component.2)
  let := hS.quasisimple
  have hcomponent : IsComponent (XiQuotient Mc) (quotientImage Mc L) :=
    ⟨hS.component.2.subnormal.map (QuotientGroup.mk'_surjective _),
      IsQuasisimple.of_mulEquiv ec⟩
  have hKlayer : K ≤ componentLayer (Mc ⧸ pCore 2 Mc) := by
    change quotientImage Mc (residualClosure J Mc) ≤ _
    rw [hcl,quotientImage_componentOrbit_source Mc L (T : Subgroup G) hS.component.1 hTMc]
    exact iSup_le fun t => le_sSup (hcomponent.map_conj (t : XiQuotient Mc))
  have hbound := source_solvable_overgroup_prime_bound hG T hu J hJ.1 (Or.inr rfl) hmax
  have hfit : fittingSubgroup (Mc ⧸ pCore 2 Mc) = ⊥ :=
    fitting_quotient_eq_bot_of_closure_centralizers hJMc hs hbound K hKlayer hc3 (fun _ => hc5)
  have hsub : (residualClosure J Mc).subgroupOf Mc = primeToResidual 3 Mc := by
    rw [hres3,subgroupOf,comap_map_eq_self_of_injective Mc.subtype_injective]
  let : ((residualClosure J Mc).subgroupOf Mc).Normal := hsub ▸ inferInstance
  let : K.Normal := (inferInstance : ((residualClosure J Mc).subgroupOf Mc).Normal).map
    (QuotientGroup.mk' (pCore 2 Mc)) (QuotientGroup.mk'_surjective _)
  exact ⟨hres,hres3,hfit,closure_eq_generalizedFitting_of_centralizer Mc hsq
    (source_no_suzuki_components hG T hu hJ.1 hJMc (Or.inr rfl) hmax hprim)
    K hKlayer hfit hc3⟩

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
