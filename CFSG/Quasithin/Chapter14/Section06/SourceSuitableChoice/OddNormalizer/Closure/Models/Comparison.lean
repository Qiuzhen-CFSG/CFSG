module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.F918
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.ExchangedGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.ExchangedLayer

/-!
# The detected strict closure and its proved exchanged models

Apply the original intrinsic component detection, then use the F.9.18 lists
on the actual component-orbit Sylow join. In the exchanged case the Borel
congruence, Suzuki exclusion and maximal-prime field bound give precisely
PSL₂(4), PSL₂(16), or the cubic PSL₃(2) row. The checked residual/layer
argument then identifies the literal O^{p′}(Mc), O^{3′}(Mc) and F*(Mc/O₂(Mc)).
The invariant case retains its actual component and now has the F.9.18 list.

No strict exchanged-model comparison is assumed. The invariant-list sieve,
full automorphism/wreath quotient recognition and parabolic normalizer still
belong to qt-e-suitable-odd-normalizer. This is not the four-way conclusion
SourceClosureAlternatives. The earlier primitive and exchanged-factor inputs
retain qt-e-quintic-recognition and qt-e-14612-singleton. The independent
p=3 exclusion retains qt-e-14615-quintic-exclusion and is not used here.
Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Subgroup Theory.GroupTheory
open Chapter1 Chapter1.XiEmbedding
open Chapter13.Section08.Components.Models Chapter13.Section08.Components.SourceModels
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
include hG hempty hM hunique hmany hcard e hab hH

/-- The actual maximal-prime choice determines the exchanged component rows.
F.9.18, the Borel congruence, Suzuki exclusion and the field bound are all
proved from the source hypotheses; no strict model comparison is assumed. -/
theorem source_swapped_closure_model
    {p : ℕ} {P L : Subgroup G}
    (h : SwappedSylowInput KnownSimple.IsKnownSimple p (T : Subgroup G) (residual H) P Mc L)
    (hprim : PrimitiveResidual H p) (hp : p = 3 ∨ p = 5)
    (hmax : MaximalOddPrime (T : Subgroup G) M p) :
    StrictExchangedModel (T : Subgroup G) Mc (componentOrbit L (T : Subgroup G)) L p := by
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  let ec : XiQuotient L ≃* ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe h.component.1)
      (pCore_map_iso 2 (subgroupOfEquivOfLe h.component.1))).symm.trans
      (cComponentTwoCoreQuotientEquiv h.component.2)
  refine ⟨(swapped_closure_product h).1,?_⟩
  rcases source_swapped_closure_f918_models hG T hempty hM hunique hmany hcard e hab H hH h with
    ⟨m,hm,hbin⟩ | ⟨m,hm,he⟩ | hthree
  · have hcong := swapped_binary_congruence h hm hbin
    have hbin' := hbin.of_mulEquiv ec.symm
    have hparam := source_binary_component_field_parameter hG T hunique hH hHMc hp hmax
      hprim L h.component.2 hm hbin' hcong
    refine Or.inl ⟨m,hm,?_,hcong,hbin'⟩
    rcases hparam with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  · exact (source_no_suzuki_components hG T hunique hH hHMc hp hmax hprim
      L h.component.1 h.component.2 m (by omega) (he.map (ec.symm.trans ·))).elim
  · exact Or.inr ⟨swapped_linear_three_prime h hp hthree,hthree.of_mulEquiv ec.symm⟩

variable [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))

/-- Every strict closure is either one invariant detected component or a
proved exchanged model with the literal residual and generalized-Fitting
identifications. The invariant comparison and the full outer action remain
with the source assembly owner. -/
theorem source_strict_closure_invariant_or_exchanged_layer
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hne : residualClosure H Mc ≠ residual H) :
    ∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
      IsQuasisimple (XiQuotient L) ∧
      residualClosure H Mc = componentOrbit L (T : Subgroup G) ∧
      (((T : Subgroup G) ≤ normalizer (L : Set G) ∧ residualClosure H Mc = L ∧
          F918Models (XiQuotient L)) ∨
        (StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L p ∧
          residualClosure H Mc = (primeToResidual p Mc).map Mc.subtype ∧
          residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
          StrictClosureLayer Mc (residualClosure H Mc))) := by
  obtain ⟨P,L,hi,hL,he,hn,hcomm⟩ := source_strict_closure_component_orbit
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hne
  refine ⟨L,hL.mem.1,hL.mem.2,hL.quasisimple,he,?_⟩
  by_cases hTL : (T : Subgroup G) ≤ normalizer (L : Set G)
  · have ho : componentOrbit L (T : Subgroup G) = L := le_antisymm
      (iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hTL)
      (le_componentOrbit L (T : Subgroup G))
    have hPL : P ≤ L := (hi.complement_le.trans (le_conjugateSpanBy _ _)).trans_eq (he.trans ho)
    have hnL : (L.subgroupOf Mc).Normal := ho ▸ hn
    exact Or.inl ⟨hTL,he.trans ho,source_invariant_closure_f918_models
      hG T hempty hM hunique hmany hcard e hab H hH hi hL.mem.1 hL.mem.2 hL.quasisimple hnL hPL⟩
  · have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hunique.symm ▸ Set.mem_singleton Mc
    have hTMc : (T : Subgroup G) ≤ Mc := le_sup_right.trans hi.overgroup
    have hSylow : IsSylowIn 2 (T : Subgroup G) Mc := by
      refine ⟨T.subtype hTMc,?_⟩
      simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]
    let hs : SwappedSylowInput KnownSimple.IsKnownSimple p (T : Subgroup G) (residual H) P Mc L :=
      { toLocalInput := hi
        sqtk := hG.twoLocal_sqtk hMc.1.1
        component := hL.mem
        quasisimple := hL.quasisimple
        orbit_normal := hn
        complement_le_orbit := (hi.complement_le.trans (le_conjugateSpanBy _ _)).trans_eq he
        orbit_commutator := hcomm
        noncentral := hL.noncentral_component_core
        not_invariant := hTL
        sylow_two := hSylow }
    have hm := source_swapped_closure_model hG T hempty hM hunique hmany hcard e hab
      H hH hs hprim d.prime hmax
    rw [←he] at hm
    exact Or.inr ⟨hm,source_strict_exchanged_closure_layer hG T hempty hM hunique hmany hcard e hab
      H hH a p H0 H1 H2 hprim d hmax hne L hL.mem.1 hL.mem.2 hm⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
