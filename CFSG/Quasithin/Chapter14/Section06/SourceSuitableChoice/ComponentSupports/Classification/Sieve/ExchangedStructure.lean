module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.LinearTwo
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.ComponentStructure.Source
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.GroupTheory.PairNormalizerIndex

/-!
# The full terminal exchanged-component family

Every remaining component quotient has positive three-rank, including the
normal PSL₂(4) endpoint. Thus any two distinct components exhaust the family
in the radical-free quotient. A nonnormal component and one of its conjugates
therefore give all component models using the proved exchanged L₃(2) sieve.

At the original H=Mc, this supplies the actual residual product K Kᵗ, the
index-two Sylow component normalizer, and Mc=⟨Kᵀ⟩T. In particular the F.9.18
actor construction may use the full original U/Z in this branch. None of
these results assumes the still-open normal PSL₂(4) exclusion.

The normal branch, natural-module recognition and suitable-vector assembly
remain with qt-e-suitable-component-supports. Original 14.6.18 remains an
explicit source input owned by qt-e-14625-source.
Source: Aschbacher--Smith 14.6.20--23, printed pp.1037--1038.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
open Chapter13.Section08.Components.Models
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

/-- Every surviving quotient has positive three-rank, including the still
unexcluded normal field-four endpoint. -/
theorem source_component_quotient_three_rank_pos
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    0 < primeRank 3 (K ⧸ pCore 2 K) := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hn := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
  rcases source_component_four_or_terminal_models hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK with ⟨_,F,_,_,hF,⟨a⟩⟩ | hm
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
      (by simpa only [←Nat.card_eq_fintype_card,show (2 : ℕ)^2 = 4 by norm_num] using hF)
    apply hn
    rw [Nat.card_congr a.toEquiv]
    exact (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
      (F := F) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)).trans (card_subgroup_dvd_card _)
  · change Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) at hm
    rcases hm with ha | ha
    · let a := Classical.choice ha
      apply hn
      rw [Nat.card_congr a.toEquiv,Matrix.PSL3Two.card_SL]
      decide
    · let a := Classical.choice ha
      have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 6)
      rw [←primeRank_congr 3 a,hz] at hh
      omega

/-- Two distinct relative components exhaust the original component family.
This does not assume that the normal field-four endpoint has been excluded. -/
theorem source_component_pair_exhausts
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K C : Subgroup G) (hKH : K ≤ H) (hCH : C ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hC : (C.subgroupOf H).IsCComponent)
    (hne : K ≠ C) (D : Subgroup G) (hDH : D ≤ H) (hD : (D.subgroupOf H).IsCComponent) :
    D = K ∨ D = C := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hR := source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv H hH
  have hQ : solvableRadical (H ⧸ pCore 2 H) = ⊥ := by
    have hh := map_solvableRadical_equiv (QuotientGroup.quotientMulEquivOfEq hR)
    rw [solvableRadical_quotient_solvableRadical,Subgroup.map_bot] at hh
    exact hh.symm
  have hr : primeRank 3 (H ⧸ pCore 2 H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      ((Chapter3.sqtk_of_mem_H hG hH.1.1).stronglyQuasithin 3 Nat.prime_three (by decide))
  have hpos (B : Subgroup (H ⧸ pCore 2 H)) (hB : B.IsCComponent) : 0 < primeRank 3 B := by
    obtain ⟨A,hA,rfl⟩ := hB.exists_map_quotient_eq (pCore 2 H)
    let E := A.map H.subtype
    have hEH : E ≤ H := map_subtype_le A
    have he : E.subgroupOf H = A := comap_map_eq_self_of_injective H.subtype_injective A
    have hp := source_component_quotient_three_rank_pos
      hG T hempty hM hunique hmany hcard e hab hsolv H hH E hEH (he.symm ▸ hA)
    let a := equivMapOfInjective A H.subtype H.subtype_injective
    let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    rw [←primeRank_congr 3 ((cComponentTwoCoreQuotientEquiv hA).symm.trans aq)] at hp
    exact hp
  have hne' : (K.subgroupOf H).map q ≠ (C.subgroupOf H).map q := by
    intro he
    have hh := congrArg (Subgroup.map H.subtype) (hK.eq_of_map_quotient_eq hC _ he)
    rw [map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hCH] at hh
    exact hne hh
  have hall := (hK.map_quotient (pCore 2 H)).eq_or_eq_of_rank_two
    (p := 3) hQ hr hpos (hC.map_quotient (pCore 2 H)) hne' (hD.map_quotient (pCore 2 H))
  rcases hall with he | he
  · left
    have hh := congrArg (Subgroup.map H.subtype) (hD.eq_of_map_quotient_eq hK _ he)
    simpa only [map_subgroupOf_eq_of_le hDH,map_subgroupOf_eq_of_le hKH] using hh
  · right
    have hh := congrArg (Subgroup.map H.subtype) (hD.eq_of_map_quotient_eq hC _ he)
    simpa only [map_subgroupOf_eq_of_le hDH,map_subgroupOf_eq_of_le hCH] using hh

/-- An exchanged component forces every component to have the binary
linear-three model, without a premise about normal-component recognition. -/
theorem source_nonnormal_all_component_models
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) :
    ∀ D : Subgroup G, D ≤ H → (D.subgroupOf H).IsCComponent → ComponentQuotientModels D := by
  obtain ⟨a,_⟩ := source_nonnormal_component_linear_three_diagram
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn
  have hmK : ComponentQuotientModels K := Or.inl ⟨a.trans Matrix.PSL3Two.equiv.symm⟩
  have hg : ∃ g : H, (K.subgroupOf H).map (MulAut.conj g).toMonoidHom ≠ K.subgroupOf H := by
    by_contra! hh
    exact hn (normal_iff_map_conj_eq.mpr hh)
  obtain ⟨g,hg⟩ := hg
  let B := (K.subgroupOf H).map (MulAut.conj g).toMonoidHom
  let C := B.map H.subtype
  have hCH : C ≤ H := map_subtype_le B
  have heC : C.subgroupOf H = B := comap_map_eq_self_of_injective H.subtype_injective B
  have hC : (C.subgroupOf H).IsCComponent := heC.symm ▸ hK.map_equiv (MulAut.conj g)
  have hne : K ≠ C := by
    intro he
    exact hg (heC.symm.trans (congrArg (fun X : Subgroup G => X.subgroupOf H) he.symm))
  let b : K ≃* C := (subgroupOfEquivOfLe hKH).symm.trans
    (((MulAut.conj g).subgroupMap (K.subgroupOf H)).trans
      (equivMapOfInjective B H.subtype H.subtype_injective))
  intro D hDH hD
  rcases source_component_pair_exhausts hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K C hKH hCH hK hC hne D hDH hD with rfl | rfl
  · exact hmK
  · exact hmK.transport b

/-- The terminal exchanged branch discharges both the individual models and
the residual-generation input, on the unchanged Mc. -/
theorem terminal_nonnormal_residual_structure
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    cComponentLayer Mc = solvableResidual Mc ∧
      solvableResidual Mc = pResidual 2 Mc ∧
      (Mc : Set G) = ((solvableResidual Mc).map Mc.subtype : Set G) *
        ((T : Subgroup G) : Set G) := by
  have hm := source_nonnormal_all_component_models hG T hempty hM hunique hmany hcard e hab hsolv
    Mc (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK hn
  exact ⟨(terminal_residual_models_of_component_models
    hG T hempty hM hunique hmany hcard e hab hsolv hm).1,
    terminal_residual_structure_of_component_models
      hG T hempty hM hunique hmany hcard e hab hsolv hm⟩

/-- The exchanged pair is the full terminal component family, with the exact
inverse-conjugation product and index-two Sylow component normalizer. -/
theorem terminal_nonnormal_component_pair
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (K : Set G) ∧
      ((solvableResidual Mc).map Mc.subtype : Set G) =
        (K : Set G) * (K.map (MulAut.conj t⁻¹).toMonoidHom : Set G) ∧
      (∀ D : Subgroup G, D ≤ Mc → (D.subgroupOf Mc).IsCComponent →
        D = K ∨ D = K.map (MulAut.conj t⁻¹).toMonoidHom) ∧
      ((T : Subgroup G) ⊓ normalizer (K : Set G)).relIndex (T : Subgroup G) = 2 := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hm := source_nonnormal_all_component_models hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK hn
  have halt := (terminal_alternatives_of_component_models
    hG T hempty hM hunique hmany hcard e hab hsolv hm K hKM hK).2.2
  rcases halt with ⟨he,_⟩ | ⟨_,t,ht,hnt,he⟩ | ⟨_,C,hCM,hC,hne,hnK,_⟩
  · have hh := congrArg (fun X : Subgroup G => X.subgroupOf Mc) he
    rw [show ((solvableResidual Mc).map Mc.subtype).subgroupOf Mc = solvableResidual Mc from
      comap_map_eq_self_of_injective Mc.subtype_injective _] at hh
    exact (hn (hh ▸ inferInstance)).elim
  · let C := K.map (MulAut.conj t⁻¹).toMonoidHom
    have hti : t⁻¹ ∈ Mc := hout.1.2 ((T : Subgroup G).inv_mem ht)
    have hCM : C ≤ Mc := by
      rintro _ ⟨k,hk,rfl⟩
      exact (mem_normalizer_iff.mp (Mc.le_normalizer hti) k).mp (hKM hk)
    have hmap : ((K.subgroupOf Mc).map (MulAut.conj (⟨t⁻¹,hti⟩ : Mc)).toMonoidHom).map Mc.subtype = C := by
      rw [map_map]
      change (K.subgroupOf Mc).map
        ((MulAut.conj t⁻¹).toMonoidHom.comp Mc.subtype) = C
      rw [←map_map,map_subgroupOf_eq_of_le hKM]
    have hC : (C.subgroupOf Mc).IsCComponent := by
      rw [←hmap,show ∀ B : Subgroup Mc, (B.map Mc.subtype).subgroupOf Mc = B from
        fun B => comap_map_eq_self_of_injective Mc.subtype_injective B]
      exact hK.map_equiv _
    have hne : K ≠ C := by
      intro hh
      have hninv : t⁻¹ ∈ normalizer (K : Set G) := mem_normalizer_iff_map_conj_eq.mpr hh.symm
      exact hnt ((normalizer (K : Set G)).inv_mem_iff.mp hninv)
    have hall := source_component_pair_exhausts hG T hempty hM hunique hmany hcard e hab hsolv
      Mc hout K C hKM hCM hK hC hne
    refine ⟨t,ht,hnt,he,hall,?_⟩
    rw [inf_relIndex_left]
    apply normalizer_relIndex_eq_two_of_pair (T : Subgroup G) K C
      (fun s hs => ?_) t⁻¹ ((T : Subgroup G).inv_mem ht) hne.symm
    have hsM : s ∈ Mc := hout.1.2 hs
    let E := K.map (MulAut.conj s).toMonoidHom
    have hEM : E ≤ Mc := by
      rintro _ ⟨k,hk,rfl⟩
      exact (mem_normalizer_iff.mp (Mc.le_normalizer hsM) k).mp (hKM hk)
    have hmapE : ((K.subgroupOf Mc).map (MulAut.conj (⟨s,hsM⟩ : Mc)).toMonoidHom).map Mc.subtype = E := by
      rw [map_map]
      change (K.subgroupOf Mc).map ((MulAut.conj s).toMonoidHom.comp Mc.subtype) = E
      rw [←map_map,map_subgroupOf_eq_of_le hKM]
    apply hall E hEM
    rw [←hmapE,show ∀ B : Subgroup Mc, (B.map Mc.subtype).subgroupOf Mc = B from
      fun B => comap_map_eq_self_of_injective Mc.subtype_injective B]
    exact hK.map_equiv _
  · exact (hn hnK).elim

/-- In the exchanged branch F.9.18's generation premise holds at Mc itself,
so its module is the entire original U/Z rather than a smaller span. -/
theorem terminal_nonnormal_generated
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) = Mc := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨t,ht,_,he,_,_⟩ := terminal_nonnormal_component_pair
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  have hR : (solvableResidual Mc).map Mc.subtype ≤ conjugateSpanBy K (T : Subgroup G) := by
    intro r hr
    have hh : r ∈ (K : Set G) * (K.map (MulAut.conj t⁻¹).toMonoidHom : Set G) := he ▸ hr
    obtain ⟨k,hk,c,⟨j,hj,rfl⟩,rfl⟩ := hh
    exact (conjugateSpanBy K (T : Subgroup G)).mul_mem
      ((le_conjugateSpanBy K _) hk)
      ((mem_normalizer_iff.mp ((le_normalizer_conjugateSpanBy K (T : Subgroup G))
        ((T : Subgroup G).inv_mem ht)) j).mp ((le_conjugateSpanBy K _) hj))
  apply le_antisymm
  · exact sup_le (conjugateSpanBy_le hKM (hout.1.2.trans Mc.le_normalizer)) hout.1.2
  · have hproduct := (terminal_nonnormal_residual_structure
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn).2.2
    intro m hm
    have hh : m ∈ ((solvableResidual Mc).map Mc.subtype : Set G) * ((T : Subgroup G) : Set G) :=
      hproduct ▸ hm
    obtain ⟨r,hr,t,ht,rfl⟩ := hh
    exact (conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G)).mul_mem
      (mem_sup_left (hR hr)) (mem_sup_right ht)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
