module
public import Theory.Representation.BinaryTensorThree.PerfectSupports
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.SingleFactorConstituents
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.IndividualSupports

/-!
# Full original supports in the exchanged terminal branch

Single-factor constituents force the two quotient components to centralize
each other's full moved spaces, even through nonsplit extensions. The original
conjugation coordinates put the remaining displacement in Z; perfectness lifts
centralization through that kernel. The product Mc = KK^t T then promotes
Sylow-normalizer invariance of the selected seed span to invariance under the
whole Mc intersect N_G(K).

IndividualSupports now identifies [U,K] with the same natural/dual seed pair,
retaining the central intersection, conjugation and residual exhaustion. Apply
this to both exchanged components and feed all four original sections to the
literal paired-component consumer. Thus every terminal component is relatively
normal in Mc.

The normal PSL2(4) exclusion, normal-pair support construction and normal L3(2)
and A6 same-vector suitable assembly remain with qt-e-suitable-component-supports.
Original14.6.18 remains hsolv, with final discharge by qt-e-14625-source.
Source: Aschbacher--Smith F.9.18(5iii.b,7),14.6.21--24,
printed pp.326,1038--1041.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
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

omit hsolv in
/-- Lift full quotient-support centralization through the original central kernel. -/
theorem source_cross_support_of_quotient_fixed
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K C : Subgroup G) (hKH : K ≤ H) (hCH : C ≤ H)
    (hC : (C.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (hfixed : subspaceCommutator a.representation ⊤ (actorImage H K) ≤
      fixedSpace a.representation (actorImage H C)) :
    ⁅⁅conjugateSpanBy (localModule T M) H,K⁆,C⁆ = ⊥ := by
  let U := conjugateSpanBy (localModule T M) H
  let c := originalSection a
  let : Group.IsPerfect (C.subgroupOf H) := hC.perfect
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hCH).toMonoidHom) (subgroupOfEquivOfLe hCH).surjective
  have hWU : ⁅U,K⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp (hKH.trans a.normalizes)
  have hz : centralInvolutions T ≤ centralizer (C : Set G) :=
    (le_centralizer_iff.mp
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes).trans
        (centralizer_le hCH)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply centralizes_of_commutator_le_centralizer C
  rw [commutator_comm ⁅U,K⁆ C]
  apply (c.commutator_le_of_imageSpace_fixed C ⁅U,K⁆ hCH hWU ?_).trans hz
  rw [commutator_comm U K,c.imageSpace_commutator K U hKH le_rfl,c.imageSpace_self]
  rw [subspaceCommutator_comp_map,fixedSpace_comp_map]
  exact hfixed

/-- Every other original component centralizes the whole support [U,K].
Constituent separation is lifted through all extensions and through Z. -/
theorem terminal_nonnormal_cross_support
    (K C : Subgroup G) (hKM : K ≤ Mc) (hCM : C ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hC : (C.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) (hne : K ≠ C) :
    ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,C⁆ = ⊥ := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hU,a,B,_,_,p,t,_,hl,hr,hs⟩ := terminal_nonnormal_constituents_single_factor
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  let N := actorImage Mc (conjugateSpanBy K (T : Subgroup G))
  let : N.Normal := by
    have hh := source_quotient_componentOrbit_normal
      hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK
    rwa [quotient_componentOrbit Mc K T hKM hout.1.2] at hh
  have hCX : C ≤ conjugateSpanBy K (T : Subgroup G) := by
    obtain ⟨s,hs,_,_,hall,_⟩ := terminal_nonnormal_component_pair
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
    rcases hall C hCM hC with he | he
    · exact he ▸ le_conjugateSpanBy K (T : Subgroup G)
    · rw [he]
      exact (map_mono (le_conjugateSpanBy K (T : Subgroup G))).trans
        (mem_normalizer_iff_map_conj_eq.mp
          (le_normalizer_conjugateSpanBy K (T : Subgroup G) ((T : Subgroup G).inv_mem hs))).le
  have hCN : actorImage Mc C ≤ N := map_mono (comap_mono hCX)
  have hne' : actorImage Mc C ≠ actorImage Mc K := by
    intro he
    let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
    have hh := congrArg (Subgroup.map Mc.subtype)
      (hC.eq_of_map_quotient_eq hK (pCore 2 Mc) he)
    rw [map_subgroupOf_eq_of_le hCM,map_subgroupOf_eq_of_le hKM] at hh
    exact hne hh.symm
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  have hf := hs.full_support_centralizes_component a.representation N (actorImage Mc K) p t hl hr
    (source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK)
    (actorImage Mc C)
    (source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv Mc hout C hCM hC)
    hCN hne'
  exact source_cross_support_of_quotient_fixed
    hG T hempty hM hunique hmany hcard e hab Mc hout K C hKM hCM hC a hf

/-- Cross-centralization supplies the missing whole-normalizer invariance.
The original residual product, rather than only the Sylow normalizer, is used. -/
theorem terminal_nonnormal_seed_span_invariant
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal)
    (W : Subgroup G) (hW : W ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hKW : K ≤ normalizer (W : Set G))
    (hSW : (T : Subgroup G) ⊓ normalizer (K : Set G) ≤ normalizer (W : Set G)) :
    Mc ⊓ normalizer (K : Set G) ≤ normalizer (W : Set G) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨t,ht,hnt,hres,_,_⟩ := terminal_nonnormal_component_pair
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
  have hcross := terminal_nonnormal_cross_support
    hG T hempty hM hunique hmany hcard e hab hsolv K C hKM hCM hK hC hn hne
  have hCW : C ≤ normalizer (W : Set G) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcross)).trans
      (centralizer_le hW)).trans (Subgroup.centralizer_le_normalizer _)
  have hCK : C ≤ normalizer (K : Set G) := by
    have hh := (map_mono ((le_cComponentLayer hC).trans (cComponentLayer_le_normalizer hK))
      (f := Mc.subtype)).trans (le_normalizer_map Mc.subtype)
    simpa only [map_subgroupOf_eq_of_le hCM,map_subgroupOf_eq_of_le hKM] using hh
  have hprod := (terminal_nonnormal_residual_structure
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn).2.2
  intro g hg
  obtain ⟨r,hr,s,hs,hgEq⟩ := (show g ∈
      ((solvableResidual Mc).map Mc.subtype : Set G) * ((T : Subgroup G) : Set G) from
      hprod ▸ hg.1)
  obtain ⟨k,hk,c,hc,hrEq⟩ := (show r ∈ (K : Set G) * (C : Set G) from hres ▸ hr)
  have hrK : r ∈ normalizer (K : Set G) := hrEq ▸
    (normalizer (K : Set G)).mul_mem (K.le_normalizer hk) (hCK hc)
  have hrW : r ∈ normalizer (W : Set G) := hrEq ▸
    (normalizer (W : Set G)).mul_mem (hKW hk) (hCW hc)
  have hsK : s ∈ normalizer (K : Set G) := by
    have hh := (normalizer (K : Set G)).mul_mem
      ((normalizer (K : Set G)).inv_mem hrK) hg.2
    rw [←hgEq,inv_mul_cancel_left] at hh
    exact hh
  exact hgEq ▸ (normalizer (W : Set G)).mul_mem hrW (hSW ⟨hs,hsK⟩)

/-- The original selected seeds are the full natural and dual supports. All
normalizer and residual-exhaustion premises of IndividualSupports are discharged. -/
theorem terminal_nonnormal_natural_full_supports
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
      Mc ⊓ normalizer (K : Set G) ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) ∧
      ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = A ⊔ B := by
  obtain ⟨eK,A,B,⟨d⟩,⟨ddual⟩,hA,hB,hAB,hconj,hspan,hindex,hexhaust,hiff⟩ :=
    terminal_nonnormal_natural_sections_support_criterion
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  have hKW : K ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    (le_inf d.normalized ddual.normalized).trans (normalizer_inf_normalizer_le_normalizer_sup A B)
  have hSW : (T : Subgroup G) ⊓ normalizer (K : Set G) ≤
      normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    rw [←hspan]
    exact le_normalizer_conjugateSpanBy _ _
  have hWN := terminal_nonnormal_seed_span_invariant
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn (A ⊔ B) (sup_le hA hB) hKW hSW
  exact ⟨eK,A,B,⟨d⟩,⟨ddual⟩,hA,hB,hAB,hconj,hspan,hindex,hexhaust,hWN,hiff.mpr hWN⟩

/-- The exchanged terminal branch is excluded by the literal waiting
critical-pair consumer, using all four constructed natural/dual sections. -/
theorem terminal_component_normal
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    (K.subgroupOf Mc).Normal := by
  by_contra hn
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
  have hCi : C.subgroupOf Mc = (K.subgroupOf Mc).map (MulAut.conj (⟨t⁻¹,hti⟩ : Mc)).toMonoidHom := by
    rw [←hmap]
    exact comap_map_eq_self_of_injective Mc.subtype_injective _
  have hC : (C.subgroupOf Mc).IsCComponent := by
    rw [hCi]
    exact hK.map_equiv _
  have hnC : ¬ (C.subgroupOf Mc).Normal := by
    intro hcN
    rw [hCi] at hcN
    exact hn ((MulEquiv.normal_map_iff (f := MulAut.conj (⟨t⁻¹,hti⟩ : Mc))).mp hcN)
  have hne : K ≠ C := by
    intro he
    exact hnt ((normalizer (K : Set G)).inv_mem_iff.mp
      (mem_normalizer_iff_map_conj_eq.mpr he.symm))
  obtain ⟨eK,A,B,⟨d⟩,⟨ddual⟩,hA,hB,hAB,_,_,_,hexhaust,hWN,_⟩ :=
    terminal_nonnormal_natural_full_supports
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  obtain ⟨eC,Aplus,Bplus,⟨dplus⟩,⟨dplusDual⟩,hAplus,hBplus,hABplus,_,_,_,hexhaustPlus,hWNplus,_⟩ :=
    terminal_nonnormal_natural_full_supports
      hG T hempty hM hunique hmany hcard e hab hsolv C hCM hC hnC
  exact source_no_paired_components_of_normalized_seed_spans
    hG T hempty hM hunique hmany hcard e hab hsolv K C hKM hCM hK hC hne
    eK eC A B Aplus Bplus d ddual dplus dplusDual hA hB hAplus hBplus hAB.le hABplus.le
    hexhaust hexhaustPlus hWN hWNplus

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
