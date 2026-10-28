module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.ResidualSupport
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.PairedSupportConsumer
public import Theory.GroupTheory.Commutator.PerfectSupportExtraction

/-!
# Individual supports from whole-normalizer invariance

For the actual natural--dual seed pair, invariance under the whole relative
component normalizer lets the other component act through the trivial
invertible commutant. Perfectness lifts this fixation through Z. The full
component list and the checked residual-span exhaustion then identify
[U,K] with the joined seed support by the relative three-subgroups lemma.

Apply this extraction to the same original seeds supplied by ResidualSupport.
Their full-support identity is equivalent to invariance of their join under
Mc intersect N_G(K). The final theorem feeds both extracted supports into
the literal waiting paired-component contradiction, deriving its catalogue
premise and retaining all four natural/dual sections over centralInvolutions T.

Whole-normalizer invariance is an explicit remaining premise; the saved
Sylow-normalizer homogeneity does not discharge it. Its proof, the normal
PSL2(4) exclusion and suitable-vector assembly remain with
qt-e-suitable-component-supports. Original14.6.18 remains hsolv, for
qt-e-14625-source. These conditional results do not complete14.6.22--24.
Source: Aschbacher--Smith14.6.21--24, printed pp.1037--1039.
-/


public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
universe u
variable {G : Type u} [Group G] [Finite G]
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

/-- A normalized marked natural--dual section is fixed by the other component,
including the original central kernel. It need not yet be the full support. -/
theorem source_cross_of_normalized_natural_dual_section
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K C : Subgroup G) (hKH : K ≤ H) (hCH : C ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hC : (C.subgroupOf H).IsCComponent)
    (hne : K ≠ C)
    (W : Subgroup G)
    (hWU : W ≤ conjugateSpanBy (localModule T M) H)
    (hCW : C ≤ normalizer (W : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (d : BinaryConjugationSection K W
      (centralInvolutions T) (BinaryLinearThree.NaturalDual.action.comp
        (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) :
    ⁅W,C⁆ = ⊥ := by
  obtain ⟨hU,a,_⟩ := source_rankTwo_bounded_placed_action
    hG T hempty hM hunique hmany hcard e hab H hH
  let := hU
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWU
  let : Group.IsPerfect (C.subgroupOf H) := hC.perfect
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hCH).toMonoidHom) (subgroupOfEquivOfLe hCH).surjective
  have hCZ : C ≤ centralizer (centralInvolutions T : Set G) := hCH.trans
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes
  apply (originalSection a).centralizes_of_embedded_trivial_commutant d hKH hCH
    hWU hCW hCZ
  · intro c k
    let q := QuotientGroup.mk' (pCore 2 H)
    let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    have hne' : actorImage H C ≠ actorImage H K := by
      intro he
      have hh := congrArg (Subgroup.map H.subtype) (hC.eq_of_map_quotient_eq hK (pCore 2 H) he)
      rw [map_subgroupOf_eq_of_le hCH,map_subgroupOf_eq_of_le hKH] at hh
      exact hne hh.symm
    have hc := (source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
      H hH C hCH hC).commutator_eq_bot_of_ne
        (source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
          H hH K hKH hK) hne'
    have he := (commutator_eq_bot_iff_le_centralizer.mp hc)
      (show q (inclusion hCH c) ∈ actorImage H C from ⟨inclusion hCH c,c.property,rfl⟩)
      (q (inclusion hKH k))
      (show q (inclusion hKH k) ∈ actorImage H K from ⟨inclusion hKH k,k.property,rfl⟩)
    change a.representation (q (inclusion hCH c)) * a.representation (q (inclusion hKH k)) =
      a.representation (q (inclusion hKH k)) * a.representation (q (inclusion hCH c))
    rw [←a.representation.map_mul,←a.representation.map_mul,he]
  · intro f hf
    apply BinaryLinearThree.NaturalDual.centralizer_eq_one f
    intro g v
    obtain ⟨k,hk⟩ := (eK.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K))) g
    change eK ((QuotientGroup.mk' (pCore 2 K)) k) = g at hk
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,hk] using hf k v


/-- Extract the individual full support from the original residual exhaustion.
The remaining invariance hypothesis concerns the joined seed span under the
whole relative component normalizer, rather than its Sylow intersection. -/
theorem source_full_support_of_normalized_seed_span
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K C : Subgroup G) (hKH : K ≤ H) (hCH : C ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hC : (C.subgroupOf H).IsCComponent)
    (hne : K ≠ C)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (A B : Subgroup G)
    (d : BinaryConjugationSection K A (centralInvolutions T)
      (BinaryLinearThree.W.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (ddual : BinaryConjugationSection K B (centralInvolutions T)
      (BinaryLinearThree.W.dual.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (hA : A ≤ ⁅conjugateSpanBy (localModule T M) H,K⁆)
    (hB : B ≤ ⁅conjugateSpanBy (localModule T M) H,K⁆)
    (hAB : A ⊓ B ≤ centralInvolutions T)
    (hexhaust : ⁅conjugateSpanBy (localModule T M) H,conjugateSpanBy K (T : Subgroup G)⁆ =
      conjugateSpanBy A H)
    (hWN : H ⊓ normalizer (K : Set G) ≤ normalizer ((A ⊔ B : Subgroup G) : Set G)) :
    ⁅conjugateSpanBy (localModule T M) H,K⁆ = A ⊔ B := by
  let U := conjugateSpanBy (localModule T M) H
  have hUK : ⁅U,K⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp
    (hKH.trans (le_normalizer_conjugateSpanBy _ _))
  have hWU : A ⊔ B ≤ U := (sup_le hA hB).trans hUK
  have h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let : IsElementaryAbelian 2 U :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hU : IsMulCommutative U := inferInstance
  obtain ⟨c,_,_,_⟩ := d.exists_join_section ddual
    ((hA.trans hUK).trans ((le_centralizer_iff_isMulCommutative.mpr hU).trans
      (centralizer_le (hB.trans hUK)))) hAB
  have hCK : C ≤ normalizer (K : Set G) := by
    have hh := (map_mono ((le_cComponentLayer hC).trans (cComponentLayer_le_normalizer hK))
      (f := H.subtype)).trans (le_normalizer_map H.subtype)
    simpa only [map_subgroupOf_eq_of_le hCH,map_subgroupOf_eq_of_le hKH] using hh
  have hcross := source_cross_of_normalized_natural_dual_section
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K C hKH hCH hK hC hne
    (A ⊔ B) hWU ((le_inf hCH hCK).trans hWN) eK c
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  apply commutator_eq_of_exhausted_pair_span H U K C
    (conjugateSpanBy K (T : Subgroup G)) A (A ⊔ B) hKH (le_conjugateSpanBy _ _)
    (le_normalizer_conjugateSpanBy _ _) le_sup_left hWU (sup_le hA hB) hWN
    (le_sup_left.trans (commutator_eq_bot_iff_le_centralizer.mp hcross)) ?_ hexhaust
  intro g hg
  let D := K.map (MulAut.conj g).toMonoidHom
  have hDH : D ≤ H := by
    rintro _ ⟨k,hk,rfl⟩
    exact (mem_normalizer_iff.mp (H.le_normalizer hg) k).mp (hKH hk)
  have hmap : ((K.subgroupOf H).map (MulAut.conj (⟨g,hg⟩ : H)).toMonoidHom).map H.subtype = D := by
    rw [map_map]
    change (K.subgroupOf H).map ((MulAut.conj g).toMonoidHom.comp H.subtype) = D
    rw [←map_map,map_subgroupOf_eq_of_le hKH]
  have hD : (D.subgroupOf H).IsCComponent := by
    rw [←hmap,show ∀ J : Subgroup H, (J.map H.subtype).subgroupOf H = J from
      fun J => comap_map_eq_self_of_injective H.subtype_injective J]
    exact hK.map_equiv _
  exact source_component_pair_exhausts hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K C hKH hCH hK hC hne D hDH hD

/-- Apply the extraction to the same natural/dual pair whose full residual
span was constructed from the original hypotheses. The displayed implication
retains the one remaining whole-normalizer invariance premise. -/
theorem terminal_nonnormal_natural_sections_support_criterion
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (A B : Subgroup G),
      Nonempty (BinaryConjugationSection K A (centralInvolutions T)
        (BinaryLinearThree.W.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      Nonempty (BinaryConjugationSection K B (centralInvolutions T)
        (BinaryLinearThree.W.dual.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) ∧
      A ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆ ∧
      B ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆ ∧
      A ⊓ B = centralInvolutions T ∧
      (∃ s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G),
        B = A.map (MulAut.conj (s:G)⁻¹).toMonoidHom) ∧
      conjugateSpanBy A ((T : Subgroup G) ⊓ normalizer (K : Set G)) = A ⊔ B ∧
      (normalizer (A : Set G)).relIndex ((T : Subgroup G) ⊓ normalizer (K : Set G)) = 2 ∧
      ⁅conjugateSpanBy (localModule T M) Mc,conjugateSpanBy K (T : Subgroup G)⁆ =
        conjugateSpanBy A Mc ∧
      (⁅conjugateSpanBy (localModule T M) Mc,K⁆ = A ⊔ B ↔
        Mc ⊓ normalizer (K : Set G) ≤ normalizer ((A ⊔ B : Subgroup G) : Set G)) := by
  obtain ⟨eK,A,B,⟨d⟩,⟨ddual⟩,hA,hB,hAB,hconj,hspan,hindex,hexhaust⟩ :=
    terminal_nonnormal_natural_sections_residual_span
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨t,ht,hnt,_,_,_⟩ := terminal_nonnormal_component_pair
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let C := K.map (MulAut.conj t⁻¹).toMonoidHom
  have hti : t⁻¹ ∈ Mc := hout.1.2 ((T : Subgroup G).inv_mem ht)
  have hCM : C ≤ Mc := by
    rintro _ ⟨k,hk,rfl⟩
    exact (mem_normalizer_iff.mp (Mc.le_normalizer hti) k).mp (hKM hk)
  have hmap : ((K.subgroupOf Mc).map (MulAut.conj (⟨t⁻¹,hti⟩ : Mc)).toMonoidHom).map Mc.subtype = C := by
    rw [map_map]
    change (K.subgroupOf Mc).map ((MulAut.conj t⁻¹).toMonoidHom.comp Mc.subtype) = C
    rw [←map_map,map_subgroupOf_eq_of_le hKM]
  have hC : (C.subgroupOf Mc).IsCComponent := by
    rw [←hmap,show ∀ D : Subgroup Mc, (D.map Mc.subtype).subgroupOf Mc = D from
      fun D => comap_map_eq_self_of_injective Mc.subtype_injective D]
    exact hK.map_equiv _
  have hne : K ≠ C := by
    intro he
    exact hnt ((normalizer (K : Set G)).inv_mem_iff.mp
      (mem_normalizer_iff_map_conj_eq.mpr he.symm))
  refine ⟨eK,A,B,⟨d⟩,⟨ddual⟩,hA,hB,hAB,hconj,hspan,hindex,hexhaust,?_,?_⟩
  · intro he
    rw [←he]
    exact (source_component_support_placement hG T hempty hM hunique hmany hcard e hab hsolv
      Mc hout K hKM hK).2.2
  · exact source_full_support_of_normalized_seed_span
      hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K C hKM hCM hK hC hne
      eK A B d ddual hA hB hAB.le hexhaust

/-- The waiting critical-pair contradiction after replacing full-support
premises by the precise whole-normalizer invariance and residual-span premises.
The full original component list is derived from the two distinct components. -/
theorem source_no_paired_components_of_normalized_seed_spans
    (K C : Subgroup G) (hKM : K ≤ Mc) (hCM : C ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hC : (C.subgroupOf Mc).IsCComponent)
    (hne : K ≠ C)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eC : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group)
    (A B Aplus Bplus : Subgroup G)
    (d : BinaryConjugationSection K A (centralInvolutions T)
      (BinaryLinearThree.W.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (ddual : BinaryConjugationSection K B (centralInvolutions T)
      (BinaryLinearThree.W.dual.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (dplus : BinaryConjugationSection C Aplus (centralInvolutions T)
      (BinaryLinearThree.W.comp (eC.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C)))))
    (dplusDual : BinaryConjugationSection C Bplus (centralInvolutions T)
      (BinaryLinearThree.W.dual.comp (eC.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C)))))
    (hA : A ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hB : B ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hAplus : Aplus ≤ ⁅conjugateSpanBy (localModule T M) Mc,C⁆)
    (hBplus : Bplus ≤ ⁅conjugateSpanBy (localModule T M) Mc,C⁆)
    (hAB : A ⊓ B ≤ centralInvolutions T)
    (hABplus : Aplus ⊓ Bplus ≤ centralInvolutions T)
    (hexhaust : ⁅conjugateSpanBy (localModule T M) Mc,conjugateSpanBy K (T : Subgroup G)⁆ =
      conjugateSpanBy A Mc)
    (hexhaustPlus : ⁅conjugateSpanBy (localModule T M) Mc,conjugateSpanBy C (T : Subgroup G)⁆ =
      conjugateSpanBy Aplus Mc)
    (hWN : Mc ⊓ normalizer (K : Set G) ≤ normalizer ((A ⊔ B : Subgroup G) : Set G))
    (hWNplus : Mc ⊓ normalizer (C : Set G) ≤ normalizer ((Aplus ⊔ Bplus : Subgroup G) : Set G)) : False := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hs := source_full_support_of_normalized_seed_span
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K C hKM hCM hK hC hne
    eK A B d ddual hA hB hAB hexhaust hWN
  have hsplus := source_full_support_of_normalized_seed_span
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout C K hCM hKM hC hK hne.symm
    eC Aplus Bplus dplus dplusDual hAplus hBplus hABplus hexhaustPlus hWNplus
  have hall (J : Subgroup Mc) (hJ : J.IsCComponent) :
      J = K.subgroupOf Mc ∨ J = C.subgroupOf Mc := by
    have he : (J.map Mc.subtype).subgroupOf Mc = J :=
      comap_map_eq_self_of_injective Mc.subtype_injective J
    have hh := source_component_pair_exhausts
      hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K C hKM hCM hK hC hne
      (J.map Mc.subtype) (map_subtype_le J) (he.symm ▸ hJ)
    rcases hh with hh | hh
    · exact Or.inl (he.symm.trans (congrArg (fun D : Subgroup G => D.subgroupOf Mc) hh))
    · exact Or.inr (he.symm.trans (congrArg (fun D : Subgroup G => D.subgroupOf Mc) hh))
  exact source_no_paired_components_of_full_supports
    hG T hempty hM hunique hmany hcard e hab hsolv K C hKM hCM hK hC hne hall
    eK eC A B Aplus Bplus d ddual dplus dplusDual hs hsplus hAB hABplus

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
