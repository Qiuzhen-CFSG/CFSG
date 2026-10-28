module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.AlternatingSixSuitable
public import Theory.Representation.BinaryOffender.Homogeneous.AlternatingSixOrbit
public import Theory.Representation.AlternatingSixPairedCovers.Exhaustion
public import Theory.GroupTheory.CComponent.ResidualMarking

/-!
# Full original paired A₆ supports and suitability

The original quadratic actor has ratio at most two. The pair of marked
homogeneous covers already consumes its full movement budget, so the
component acts trivially on the remaining quotient. This identifies the
entire [U,K] with the two literal conjugate supports, with natural-or-core
coordinates under one component marking and the specified diagram twist.
Both covers retain Z and their possible fixed radical. The same first
support has the exact normalizer geometry and a single suitable involution.

Source: Aschbacher--Smith14.6.22--24, printed pp.1038--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Subgroup.NormalSylowQuotientAction
open Chapter13.Section08.CriticalGeometry.Reorientation
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- The whole original A₆ support consists of two fully marked natural or
five-dimensional covers. The same first support has its exact geometry and
one original vector satisfying all suitability clauses. -/
theorem source_normal_a6_full_supports_suitable
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hr : (solvableResidual Mc).map Mc.subtype = K)
    [hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))}
    (hI : IsIrrPlusWith a.representation (actorImage Mc K)
      (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.alternatingNatural 6)) :
    let c := originalSection a
    let A := c.subspacePreimage I
    ∃ (s : T) (j : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)),
      let sh : Mc := ⟨s,(terminal_outside hG T hempty hM hunique hmany hcard e).1.2 s.property⟩
      let J := I.map (a.representation (QuotientGroup.mk' (pCore 2 Mc) sh))
      let B := c.subspacePreimage J
      ∃ (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) I)
        (σ' : Representation (ZMod 2) (alternatingGroup (Fin 6)) J),
        Nonempty (BinaryConjugationSection K A (centralInvolutions T)
          (σ.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
        Nonempty (BinaryConjugationSection K B (centralInvolutions T)
          (σ'.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
        BinaryPermutation.SixCover.IsNaturalOrCore σ (alternatingGroup (Fin 6)).subtype ∧
        BinaryPermutation.SixCover.IsNaturalOrCore σ'
          (BinaryAlternatingSix.diagramAut.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype) ∧
        ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = A ⊔ B ∧
        (∀ x ∈ (T : Subgroup G), A.map (MulAut.conj x).toMonoidHom = A ∨
          A.map (MulAut.conj x).toMonoidHom = B) ∧
        A.map (MulAut.conj (s:G)).toMonoidHom = B ∧
        CentralOverlapGeometry T Mc (conjugateSpanBy (localModule T M) Mc) K A
          ((T : Subgroup G) ⊓ normalizer (A : Set G)) ∧
        ∃ u ∈ A, u ^ 2 = 1 ∧ u ≠ 1 ∧
          suitableQuotientCentralizer (terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) u =
            (T : Subgroup G) ⊓ normalizer (A : Set G) ∧
          Suitable (terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  let c := originalSection a
  let A := c.subspacePreimage I
  let D := actorImage Mc K
  let P := actorImage Mc T ⊓ normalizer (D : Set (Mc ⧸ pCore 2 Mc))
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let e₀ : (K ⧸ pCore 2 K) ≃* D :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKM)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKM))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  let j := e₀.trans b.groupEquiv
  obtain ⟨hn,hgen⟩ := terminal_single_component_generated
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hr (Or.inr ⟨j⟩)
  let : D.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  have hres : solvableResidual Mc = K.subgroupOf Mc := by
    rw [←hr]
    exact (comap_map_eq_self_of_injective Mc.subtype_injective _).symm
  have hcent : centralizer (D : Set (Mc ⧸ pCore 2 Mc)) = ⊥ := by
    have hrad := source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv Mc hout
    have hh := (residual_component_marking_properties hrad (K.subgroupOf Mc) hres
      D.subtype (by rw [range_subtype]; rfl)).2
    simpa only [range_subtype] using hh
  have hgenq : D ⊔ P = ⊤ := by
    change (K.subgroupOf Mc).map q ⊔ ((T : Subgroup G).subgroupOf Mc).map q ⊓ normalizer (D : Set _) = ⊤
    rw [normalizer_eq_top,inf_top_eq,←Subgroup.map_sup,←subgroupOf_sup hKM hout.1.2,
      hgen,subgroupOf_self,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  obtain ⟨⟨s,hs⟩,_⟩ := source_normal_a6_seed_stabilizer_index
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn a hI b
  let sh : Mc := ⟨s,hout.1.2 s.property⟩
  let t : P := ⟨q sh,⟨⟨sh,s.property,rfl⟩,by rw [normalizer_eq_top]; trivial⟩⟩
  have ht : I.map (a.representation t.val) ≠ I := by
    intro hh
    exact hs ((c.mem_normalizer_subspacePreimage_iff I sh).mpr hh)
  let J := I.map (a.representation t.val)
  let B := c.subspacePreimage J
  have hJ := hI.isIrrPlus.map_normalizer a.representation (hI.normalizes t.property)
  obtain ⟨W,C,hW,hWO,hκ,hκr,hfull⟩ := hI.alternating_six_pair_data
    a.representation hcent hgenq t b.groupEquiv b.linearEquiv b.intertwines ht
  have hc : subspaceCommutator a.representation W.toSubmodule C.component.range = W.toSubmodule := by
    rw [hκr,hWO]
    exact orbitSpan_full_commutator a.representation hI.normalizes hI.isIrrPlus
  obtain ⟨Q,_,hQ,hq,hbound,_⟩ := source_rankTwo_placed_quadratic_actor
    hG T hempty hM hunique hmany hcard e hab Mc hout hU a
  have hex := C.exhausts_commutator a.representation W
    (Q.map q) hQ hq hbound hc
  have hfullspan : orbitSpan a.representation ⊤ I = W.toSubmodule := by
    apply le_antisymm
    · apply iSup_le
      intro x
      rw [hW]
      rcases hfull x.val with hh | hh
      · rw [hh]; exact le_sup_left
      · rw [hh]; exact le_sup_right
    · rw [hW]
      exact sup_le (le_orbitSpan a.representation ⊤ I)
        (le_iSup (fun x : (⊤ : Subgroup (Mc ⧸ pCore 2 Mc)) => I.map (a.representation x.val))
          ⟨t.val,mem_top _⟩)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hout.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKM).mp hn)
  have hspanK : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTK) (le_conjugateSpanBy _ _)
  have hexhaust : orbitSpan a.representation ⊤ I =
      subspaceCommutator a.representation ⊤ (actorImage Mc (conjugateSpanBy K (T : Subgroup G))) := by
    rw [hspanK]
    change orbitSpan a.representation ⊤ I = subspaceCommutator a.representation ⊤ D
    rw [←hκr]
    exact hfullspan.trans hex.symm
  have hsupport := source_residual_support_eq_seed_span
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a I hexhaust
  rw [hspanK] at hsupport
  have hpairH (x : Mc) : A.map (MulAut.conj (x:G)).toMonoidHom = A ∨
      A.map (MulAut.conj (x:G)).toMonoidHom = B := by
    rw [←c.subspacePreimage_map I x]
    exact (hfull (q x)).imp (congrArg c.subspacePreimage) (congrArg c.subspacePreimage)
  have hconj : A.map (MulAut.conj (s:G)).toMonoidHom = B :=
    (c.subspacePreimage_map I sh).symm
  have hspan : conjugateSpanBy A Mc = A ⊔ B := by
    apply le_antisymm
    · rw [conjugateSpanBy_eq_iSup_conj]
      apply iSup_le
      intro x
      rcases hpairH x with hx | hx
      · rw [hx]; exact le_sup_left
      · rw [hx]; exact le_sup_right
    · apply sup_le (le_conjugateSpanBy _ _)
      rw [←hconj,conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun x : Mc => A.map (MulAut.conj (x:G)).toMonoidHom) sh
  let σ := alternatingSixCoverAction a.representation D hI.isIrrPlus b.groupEquiv
  let σ' := alternatingSixCoverAction a.representation D hJ b.groupEquiv
  let f := j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let qK : K →* D := (q.subgroupMap (K.subgroupOf Mc)).comp
    (subgroupOfEquivOfLe hKM).symm.toMonoidHom
  obtain ⟨d,_⟩ := source_component_seed_coordinates
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hI.isIrrPlus
  obtain ⟨d',_⟩ := source_component_seed_coordinates
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hJ
  let E : Representation.Equiv
      (BinaryConjugationSection.subspaceAction K hKM I (originalSection_irrPlus a K hI.isIrrPlus).choose)
      (σ.comp f) := {
    toLinearEquiv := LinearEquiv.refl _ _
    isIntertwining' k := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change a.representation (qK k).val v.val =
        a.representation (b.groupEquiv.symm (b.groupEquiv (qK k))).val v.val
      rw [b.groupEquiv.symm_apply_apply] }
  let E' : Representation.Equiv
      (BinaryConjugationSection.subspaceAction K hKM J (originalSection_irrPlus a K hJ).choose)
      (σ'.comp f) := {
    toLinearEquiv := LinearEquiv.refl _ _
    isIntertwining' k := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change a.representation (qK k).val v.val =
        a.representation (b.groupEquiv.symm (b.groupEquiv (qK k))).val v.val
      rw [b.groupEquiv.symm_apply_apply] }
  refine ⟨s,j,σ,σ',⟨d.relabel (MonoidHom.id K) E⟩,⟨d'.relabel (MonoidHom.id K) E'⟩,
    IsIrrPlus.alternating_six_natural_or_core a.representation hI.isIrrPlus
      b.groupEquiv b.linearEquiv b.intertwines,
    hI.alternating_six_companion a.representation t b.groupEquiv b.linearEquiv b.intertwines ht,
    hsupport.trans hspan,fun x hx => hpairH ⟨x,hout.1.2 hx⟩,hconj,?_,?_⟩
  · exact source_normal_a6_seed_geometry hG T hempty hM hunique hmany hcard e hab hsolv
      K hKM hK hn hgen a hI b
  · exact source_exists_on_normal_a6_seed hG T hempty hM hunique hmany hcard e hab hsolv
      K hKM hK hn hgen a hI b

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
