module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.ResidualAction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.ExchangedGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.Automizer
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.InvariantLargeSieve

/-!
# Exchanged components in the strict quintic closure without an index premise

The original two commuting D10 factors supply a four-group in the starred
Sylow. The intrinsic quotient-action equivalence then makes the actual
odd-complement automizer noncyclic. In the strict closure branch, apply
source 1.3.4 to the original primitive five-plane. F.9.18 and the invariant
large-prime sieve exclude an invariant component, leaving an exchanged
component orbit and its literal F.9.18 model alternatives.

No factor-join index or closure classification is assumed. The full
component parameter and outer-action comparisons remain to be proved.
Source: Aschbacher--Smith, 14.6.12 and the comparison of 1.3.4 with F.9.18
in 14.6.14, printed pp.1031,1033. The consumer is QuinticNoIndex.Source.
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

private theorem not_cyclic_sylow_of_dihedral_pair
    {n : ℕ} [NeZero n] (A B : Subgroup G) (hd : Disjoint A B)
    (hc : A ≤ centralizer (B : Set G)) (eA : A ≃* DihedralGroup n)
    (eB : B ≃* DihedralGroup n) (S : Sylow 2 G) : ¬ IsCyclic S := by
  intro hs
  let := hs
  let R : Subgroup (DihedralGroup n) := zpowers (DihedralGroup.sr 0)
  have hR : Nat.card R = 2 := by
    rw [Nat.card_zpowers,DihedralGroup.orderOf_sr]
  let i : R × R →* DihedralGroup n × DihedralGroup n := R.subtype.prodMap R.subtype
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  let f : R × R →* G := (A ⊔ B).subtype.comp
    ((e.toMonoidHom.comp (eA.symm.prodCongr eB.symm).toMonoidHom).comp i)
  have hf : Function.Injective f := (A ⊔ B).subtype_injective.comp
    (e.injective.comp ((eA.symm.prodCongr eB.symm).injective.comp (by
      intro x y hxy
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hxy)
      · exact Subtype.ext (congrArg Prod.snd hxy))))
  have hp : IsPGroup 2 (R × R) := IsPGroup.of_card (n := 2)
    (by rw [Nat.card_prod,hR]; norm_num)
  obtain ⟨S',hS'⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let : IsCyclic S' := isCyclic_of_injective (S'.equiv S).toMonoidHom (S'.equiv S).injective
  let : IsCyclic f.range := Subgroup.isCyclic_of_le hS'
  let : IsCyclic (R × R) := isCyclic_of_injective (MonoidHom.ofInjective hf).toMonoidHom
    (MonoidHom.ofInjective hf).injective
  have hh : (Nat.card R).Coprime (Nat.card R) := coprime_card_of_isCyclic_prod (M := R) (N := R)
  rw [hR] at hh
  norm_num at hh

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

omit hG hempty hM hu hmany hcard e hab hs in
/-- The two actual D10 factors give a noncyclic starred Sylow even before
the permutation kernel is identified with their join. -/
theorem source_quintic_quotient_sylow_not_cyclic :
    ¬ IsCyclic ((T.subtype hJ.1.1.2).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 J))) := by
  obtain ⟨i,j,_,_,_,hd,hc,_⟩ := f.two_factor_moved_decomposition d w.two_factors
  exact not_cyclic_sylow_of_dihedral_pair _ _ hd
    (fun x hx y hy => (hc x hx y hy).symm) (w.dihedral i).some (w.dihedral j).some _

/-- The actual odd complement in the source Xi input has noncyclic Sylow
automizer. The proof retains the quotient action and its exact kernel. -/
theorem source_quintic_automizer_not_cyclic {P : Subgroup G}
    (h : LocalInput 5 (T : Subgroup G) (residual J) P Mc) :
    ¬ IsCyclic (automizer (T : Subgroup G) P) := by
  intro hc
  have hTJ : (T : Subgroup G) ≤ J := hJ.1.1.2
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hprim := source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  have hXi := source_quintic_residual_mem_Xi hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  obtain ⟨P',hP'⟩ := h.sylow
  have hgen : residual J ⊔ (T : Subgroup G) = J := by
    have hh := congrArg (map J.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTJ))
    simpa only [GenerationOne.residual,Subgroup.map_sup,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTJ,←MonoidHom.range_eq_map,range_subtype] using hh
  have hSyl : IsSylowIn 2 (T : Subgroup G) (residual J ⊔ (T : Subgroup G)) := by
    rw [hgen]
    exact ⟨T.subtype hTJ,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ]⟩
  let α := (quotientAut (pCore 2 (residual J))).comp
    ((residual J).normalizerMonoidHom.comp (inclusion hXi.invariant))
  let q := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hTJ)
  let ec := Chapter15.Section04.LocalSetup.complement_automizer_equiv_quotient_action
    hXi hSyl (by decide : Odd 5) h.quotient P'
  have hcy : IsCyclic α.range := by
    have hc' : IsCyclic (automizer (T : Subgroup G)
        ((P' : Subgroup (residual J)).map (residual J).subtype)) := hP'.symm ▸ hc
    let := hc'
    exact isCyclic_of_surjective ec.toMonoidHom ec.surjective
  let := hcy
  have hk : α.ker = q.ker := odd_residual_quotient_action_kernel J T hTJ 5
    (by decide) hprim hXi.invariant
  let er := (QuotientGroup.quotientKerEquivRange α).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivRange q))
  have hcq : IsCyclic q.range := isCyclic_of_surjective er.toMonoidHom er.surjective
  apply source_quintic_quotient_sylow_not_cyclic T J hJ a f d π w
  have he : q.range = ((T.subtype hTJ).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 J)) : Subgroup (J ⧸ pCore 2 J)) := by
    change q.range = ((T : Subgroup G).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
    rw [MonoidHom.range_comp,inclusion_range]
  exact he ▸ hcq

/-- The strict closure selects an actual relative component at prime five,
with its intrinsic Sylow complement and the literal orbit equality. -/
private theorem strict_closure_component_orbit
    (hne : residualClosure J Mc ≠ residual J) :
    ∃ P L : Subgroup G,
      LocalInput 5 (T : Subgroup G) (residual J) P Mc ∧
      ComponentDetection P Mc L ∧
      residualClosure J Mc = componentOrbit L (T : Subgroup G) ∧
      ((componentOrbit L (T : Subgroup G)).subgroupOf Mc).Normal ∧
      ⁅componentOrbit L (T : Subgroup G), P⁆ = componentOrbit L (T : Subgroup G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let hprim := source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  let := hprim.elementary
  have hXi := source_quintic_residual_mem_Xi hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  have hF := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  have hJMc : J ≤ Mc := hF.H_centralizes.trans (InitialSource.centralizer_le_partner T hu)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu.symm ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := hJ.1.1.2.trans hJMc
  have hSylow : IsSylowIn 2 (T : Subgroup G) Mc := by
    refine ⟨T.subtype hTMc,?_⟩
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]
  obtain ⟨er,_⟩ := residual_quotient_equiv (by decide : Odd 5) J
    (IsElementaryAbelian.isPGroup 5 (pResidual 2 (J ⧸ pCore 2 J)))
  have hq : XiOddQuotient 5 (XiQuotient (residual J)) :=
    (show XiOddQuotient 5 (pResidual 2 (J ⧸ pCore 2 J)) from
      Or.inl ⟨inferInstance,source_quintic_residual_plane_card hG T hempty hM hu hmany hcard e hab
        J hJ hs a f d π w⟩).of_mulEquiv er.symm
  let P : Sylow 5 (residual J) := default
  have hi := localInput_of_mem_Xi hXi hSylow
    (sup_le ((residual_le J).trans hJMc) hTMc) (by decide : Odd 5) hq P
  obtain ⟨L,hL,he,hn,hcomm⟩ := localInput_strict_closure_component_orbit hi
    (hG.twoLocal_sqtk hMc.1.1) hSylow hne
  exact ⟨(P : Subgroup (residual J)).map (residual J).subtype,L,hi,hL,he,hn,hcomm⟩

/-- The non-residual branch has an exchanged relative component and the
actual F.9.18 list. An invariant component is excluded by the noncyclic
automizer just constructed, without an index premise for Jhat. -/
theorem source_quintic_strict_closure_swapped
    (hne : residualClosure J Mc ≠ residual J) :
    ∃ P L : Subgroup G,
      residualClosure J Mc = componentOrbit L (T : Subgroup G) ∧
      Nonempty (SwappedSylowInput KnownSimple.IsKnownSimple 5
        (T : Subgroup G) (residual J) P Mc L) ∧
      NonnormalF918Models (XiQuotient L) := by
  obtain ⟨P,L,hi,hL,hcl,hn,hcomm⟩ := strict_closure_component_orbit
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w hne
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu.symm ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := le_sup_right.trans hi.overgroup
  have hSyl : IsSylowIn 2 (T : Subgroup G) Mc :=
    ⟨T.subtype hTMc,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]⟩
  have hTL : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := by
    intro hTL
    have ho : componentOrbit L (T : Subgroup G) = L := le_antisymm
      (iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hTL)
      (le_componentOrbit L (T : Subgroup G))
    have hPL : P ≤ L := (hi.complement_le.trans (le_conjugateSpanBy _ _)).trans_eq (hcl.trans ho)
    rw [ho] at hn hcomm
    let hI : Chapter1.XiEmbedding.InvariantLarge.SylowInput KnownSimple.IsKnownSimple
        5 (T : Subgroup G) (residual J) P Mc L :=
      ⟨hi,hG.twoLocal_sqtk hMc.1.1,hSyl,hL.mem,hn,hL.quasisimple,hTL,hPL,hcomm⟩
    have hm := source_invariant_closure_f918_models hG T hempty hM hu hmany hcard e hab
      J hJ.1 hi hL.mem.1 hL.mem.2 hL.quasisimple hn hPL
    exact source_quintic_automizer_not_cyclic hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w hi (invariant_large_f918_automizer_cyclic hI (by decide) hm)
  let hS : SwappedSylowInput KnownSimple.IsKnownSimple 5
      (T : Subgroup G) (residual J) P Mc L :=
    { toLocalInput := hi
      sqtk := hG.twoLocal_sqtk hMc.1.1
      component := hL.mem
      quasisimple := hL.quasisimple
      orbit_normal := hn
      complement_le_orbit := (hi.complement_le.trans (le_conjugateSpanBy _ _)).trans_eq hcl
      orbit_commutator := hcomm
      noncentral := hL.noncentral_component_core
      not_invariant := hTL
      sylow_two := hSyl }
  exact ⟨P,L,hcl,⟨hS⟩,source_swapped_closure_f918_models
    hG T hempty hM hu hmany hcard e hab J hJ.1 hS⟩

/-- The selected strict closure has its actual two-component product,
intrinsic quotient product, and Mc-normalizer index two. This normalizer
is that of the detected component, not of an assumed residual factor. -/
theorem source_quintic_strict_closure_geometry
    (hne : residualClosure J Mc ≠ residual J) :
    ∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
      IsQuasisimple (XiQuotient L) ∧
      residualClosure J Mc = componentOrbit L (T : Subgroup G) ∧
      (Mc ⊓ normalizer (L : Set G)).relIndex Mc = 2 ∧
      (∃ s ∈ (T : Subgroup G), s ∉ normalizer (L : Set G) ∧
        (residualClosure J Mc : Set G) = (L : Set G) *
          (L.map (MulAut.conj s⁻¹).toMonoidHom : Set G)) ∧
      Nonempty (XiQuotient (residualClosure J Mc) ≃* XiQuotient L × XiQuotient L) ∧
      NonnormalF918Models (XiQuotient L) := by
  obtain ⟨P,L,hcl,⟨hS⟩,hm⟩ := source_quintic_strict_closure_swapped
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w hne
  obtain ⟨hi,_⟩ := SwappedSylow.nonnormal_model_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hS.toSwappedInput
  have hi' : (Mc ⊓ normalizer (L : Set G)).relIndex Mc = 2 := by
    rw [←subgroupOf_normalizer_eq hS.component.1] at hi
    rw [inf_relIndex_left]
    change ((normalizer (L : Set G)).subgroupOf Mc).index = 2
    exact hi
  obtain ⟨hprod,hquot⟩ := swapped_closure_product hS
  rw [←hcl] at hprod hquot
  exact ⟨L,hS.component.1,hS.component.2,hS.quasisimple,hcl,hi',hprod,hquot,hm⟩

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
