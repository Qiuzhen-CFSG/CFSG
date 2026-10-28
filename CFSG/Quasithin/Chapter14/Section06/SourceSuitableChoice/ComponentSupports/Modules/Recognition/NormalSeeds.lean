module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.SingleLinearThree
public import Theory.GroupTheory.Commutator.NormalSpan

/-!
# Natural seeds and full orbit exhaustion for normal terminal components

For any relatively normal linear-three component, reduce to the actual
outside subgroup J = KT. The placed quadratic actor detects this component
on U_J/Z. Recognition, the orbit bound and exclusion of the four-dimensional
cover construct natural and dual sections whose sum is [U_J,K].

Relative normality of K transports this identity to the unchanged terminal
span: [U_Mc,K] is the Mc-conjugate span of the same natural seed. Both marked
sections retain the original kernel Z, central intersection, Sylow exchange
and index two. This proves seed existence and orbit exhaustion for the normal
pair without assuming that U_J = U_Mc or that the two components are conjugate.

The natural types of all original irreducible sections and invariance of the
seed pair under the other component remain necessary for individual full
supports; NormalPairSections applies the existing consumer after those types
are supplied. Original14.6.18 is the explicit hsolv input.
Source: Aschbacher--Smith F.9.18 and14.6.22, printed pp.325--326,1038.
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


/-- Recognition and the detecting actor construct a three-dimensional
homogeneous seed on the literal generated group, including its orbit bound. -/
theorem source_generated_normal_l3_natural_seed
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) (hgen : K ⊔ (T : Subgroup G) = H)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H),
      let _ := hU
      ∃ a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T),
      ∃ (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))))
        (hI : IsIrrPlusWith a.representation (actorImage H K)
          (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I),
        Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
          (centralQuotientRepresentation a.representation (actorImage H K) I hI.isIrrPlus.choose)
          (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)) ∧
        Module.finrank (ZMod 2) I = 3 ∧
        quadraticRatio (invariantSubspace a.representation (actorImage H K)
          (orbitSpan a.representation
            (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
          (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2 := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.2
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hH.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  have hspan : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTK) (le_conjugateSpanBy _ _)
  obtain ⟨hU,a,B,I,hB,hI,_,hA,hfaith,_⟩ := source_component_span_inputs
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
    (by rw [hspan,hgen])
  let := hU
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  let D := actorImage H K
  let : D.Normal := hn.map (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK
  let : IsQuasisimple D := hD.2
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  let ec : (K ⧸ pCore 2 K) ≃* D :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  let j := ec.symm.trans eK
  have hz : center D = ⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr j ⟨k,hk⟩).property
    change j k ∈ center BinaryLinearThree.Group at hh
    rw [show center BinaryLinearThree.Group = ⊥ from Matrix.PSL3Two.center_eq_bot,mem_bot] at hh
    exact j.injective (hh.trans j.map_one.symm)
  have ho := quotient_componentOrbit H K T hKH hH.1.2
  rw [hspan] at ho hfaith
  have hIQ : IsIrrPlusWith a.representation D
      (actorImage H T ⊓ normalizer (D : Set (H ⧸ pCore 2 H))) I := by
    rw [ho] at hI
    change IsIrrPlusWith a.representation D (actorImage H T) I at hI
    simpa only [normalizer_eq_top,inf_top_eq] using hI
  have hs : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    have hsH := Chapter3.sqtk_of_mem_H hG hH.1.1
    refine ⟨?_,hsH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsH.stronglyQuasithin p hp ho)
  have hm : ClassicalGroup.IsPSL D 3 2 :=
    ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,⟨j.trans Matrix.PSL3Two.equiv⟩⟩
  let A := B.map (QuotientGroup.mk' (pCore 2 H))
  have hAN : A ≤ normalizer (D : Set (H ⧸ pCore 2 H)) := by
    rw [normalizer_eq_top]; exact le_top
  obtain ⟨b⟩ := ChapterD.central_linear_three_of_detecting_actor a.representation
    hD.1 hz hs hm hAN hA hfaith hIQ.isIrrPlus
  have hAP := le_inf (source_internal_actor_le_sylow T hH.1.2 B hB) hAN
  have hP : IsPGroup 2 (actorImage H T ⊓ normalizer (D : Set (H ⧸ pCore 2 H)) :
      Subgroup (H ⧸ pCore 2 H)) := by
    rw [normalizer_eq_top,inf_top_eq]
    exact (quotientSylow H T hH.1.2).isPGroup'
  have hsmall := ChapterD.linear_three_orbit_bound_of_detecting_actor
    a.representation hz hP hAP hA hfaith hIQ b
  exact ⟨hU,a,I,hIQ,⟨b⟩,(source_l3_natural_seed_sections
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK a hIQ b hsmall).1,hsmall⟩


/-- A relatively normal linear-three component supplemented by T has its
full natural and dual supports on the literal U_H/Z. -/
theorem source_generated_normal_l3_sections
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) (hgen : K ⊔ (T : Subgroup G) = H)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ∃ (j : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (A B : Subgroup G),
      Nonempty (BinaryConjugationSection K A (centralInvolutions T)
        (BinaryLinearThree.W.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      Nonempty (BinaryConjugationSection K B (centralInvolutions T)
        (BinaryLinearThree.W.dual.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      ⁅conjugateSpanBy (localModule T M) H,K⁆ = A ⊔ B ∧
      A ⊓ B = centralInvolutions T ∧
      (∃ s : T, B = A.map (MulAut.conj (s:G)⁻¹).toMonoidHom) ∧
      conjugateSpanBy A (T : Subgroup G) = A ⊔ B ∧
      (normalizer (A : Set G)).relIndex (T : Subgroup G) = 2 ∧
      H ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hH.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  have hspanK : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTK) (le_conjugateSpanBy _ _)
  obtain ⟨hU,a,I,hI,⟨b⟩,_,hsmall⟩ := source_generated_normal_l3_natural_seed
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hgen eK
  let := hU
  let A := (originalSection a).subspacePreimage I
  obtain ⟨_,j,B,⟨d⟩,⟨ddual⟩,_,_,hAB,hconj,hspanA,hindex⟩ := source_l3_natural_seed_sections
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK a hI b hsmall
  rw [inf_eq_left.mpr hTK] at hconj hspanA hindex
  have hWK : K ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    (le_inf d.normalized ddual.normalized).trans (normalizer_inf_normalizer_le_normalizer_sup A B)
  have hWT : (T : Subgroup G) ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    rw [←hspanA]
    exact le_normalizer_conjugateSpanBy _ _
  have hWH : H ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    rw [←hgen]
    exact sup_le hWK hWT
  have hspanH : conjugateSpanBy A H = A ⊔ B := by
    apply le_antisymm (conjugateSpanBy_le le_sup_left hWH)
    rw [←hspanA]
    exact conjugateSpanBy_mono le_rfl hH.1.2
  have hexhaust := (source_normal_l3_full_orbit_exhaustion
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn
    (by rw [hspanK,hgen]) a hI b hsmall).2.2
  have hfull := source_residual_support_eq_seed_span
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK a I hexhaust
  rw [hspanK] at hfull
  exact ⟨j,A,B,⟨d⟩,⟨ddual⟩,hfull.trans hspanH,hAB,hconj,hspanA,hindex,hWH⟩

/-- Every normal linear-three component supplies literal natural/dual seeds
inside the original support, and their Mc-orbit exhausts that support. The
reduced span U_(KT) is kept distinct from U_Mc. -/
theorem terminal_normal_l3_natural_sections_span
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : (K.subgroupOf Mc).Normal)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ∃ (j : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (A B : Subgroup G),
      Nonempty (BinaryConjugationSection K A (centralInvolutions T)
        (BinaryLinearThree.W.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      Nonempty (BinaryConjugationSection K B (centralInvolutions T)
        (BinaryLinearThree.W.dual.comp (j.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      A ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆ ∧
      B ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆ ∧
      A ⊓ B = centralInvolutions T ∧
      (∃ s : T, B = A.map (MulAut.conj (s:G)⁻¹).toMonoidHom) ∧
      conjugateSpanBy A (T : Subgroup G) = A ⊔ B ∧
      (normalizer (A : Set G)).relIndex (T : Subgroup G) = 2 ∧
      ⁅conjugateSpanBy (localModule T M) (K ⊔ (T : Subgroup G)),K⁆ = A ⊔ B ∧
      ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = conjugateSpanBy A Mc := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  let J := K ⊔ (T : Subgroup G)
  have hJMc : J ≤ Mc := sup_le hKM hout.1.2
  have hKJ : K ≤ J := le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨Chapter3.mem_HOver_of_sylow_interval T hTJ hJMc hout.1,
      fun hle => source_component_not_le hG T hempty hM hunique hmany hcard e hab hsolv
        Mc hout K hKM hK (hKJ.trans hle)⟩
  have hKMn := (normal_subgroupOf_iff_le_normalizer hKM).mp hn
  have hnJ : (K.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKJ).mpr (hJMc.trans hKMn)
  obtain ⟨j,A,B,hA,hB,hfull,hAB,hconj,hspan,hindex,_⟩ := source_generated_normal_l3_sections
    hG T hempty hM hunique hmany hcard e hab hsolv J hJ K hKJ
      (hK.subgroupOf_of_le hKJ hJMc) hnJ rfl eK
  have hsmall : ⁅conjugateSpanBy (localModule T M) J,K⁆ ≤
      ⁅conjugateSpanBy (localModule T M) Mc,K⁆ :=
    commutator_mono (conjugateSpanBy_mono le_rfl hJMc) le_rfl
  have hUJ : conjugateSpanBy (localModule T M) J ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab J hJ).UH_le_H.trans hJMc
  have hfullMc : ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = conjugateSpanBy A Mc := by
    rw [←conjugateSpanBy_nested_of_le (localModule T M) J Mc hJMc,
      commutator_conjugateSpanBy_of_normalized_right _ Mc K hUJ hKMn,hfull,
      ←hspan,conjugateSpanBy_nested_of_le A (T : Subgroup G) Mc hout.1.2]
  exact ⟨j,A,B,hA,hB,le_sup_left.trans (hfull.symm.le.trans hsmall),
    le_sup_right.trans (hfull.symm.le.trans hsmall),hAB,hconj,hspan,hindex,hfull,hfullMc⟩


end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
