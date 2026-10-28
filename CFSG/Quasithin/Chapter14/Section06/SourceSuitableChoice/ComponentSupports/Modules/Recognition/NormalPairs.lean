module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.FullSupports
public import CFSG.Quasithin.ChapterD.Section02.LinearThreePairSupports
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.ComponentStructure
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Residuals

/-!
# Normal terminal pairs: tensors and full-support lifting

The original quotient of a pair of distinct relative C-components has
product coordinates preserving both inclusions. In source case (3), the
literal residual product and the two L3(2) markings identify its solvable
residual with O²(Mc) and give Mc = KK+T. Thus the original placed quadratic
actor is faithful on the entire pair. The tensor stability and diagram
arguments exclude tensor constituents on every subquotient of the original
U/Z, without replacing either component by a conjugate of the other.

If both components' noncentral simple types are natural, tensor recognition
forces constituent separation. The representation theorem lifts this through
nonsplit extensions, and perfectness lifts through the original kernel Z.
For the selected natural and dual seeds, this supplies whole-Mc invariance
and applies the literal IndividualSupports full-support criterion.

The natural-type premise, seed construction and orbit exhaustion for this
normal pair remain with qt-e-suitable-component-supports. Consequently the
last two theorems are conditional support consumers, not a completed proof
of14.6.22. The normal PSL2(4) exclusion, A6 marking and same-vector suitable
assembly also remain there. Original14.6.18 is the explicit hsolv input,
owned by qt-e-14625-source; final14.6.24 assembly stays with
qt-e-suitable-existence. The previously completed exchanged and single-L3
branches are reused without alteration.
Source: Aschbacher--Smith D.3.7, F.9.18 and14.6.21(3)--23,
printed pp.197--199,325--326,1037--1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
universe u v
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


/-- The original pair has product coordinates with both literal inclusions. -/
theorem source_component_pair_coordinates
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K C : Subgroup G) (hKH : K ≤ H) (hCH : C ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hC : (C.subgroupOf H).IsCComponent)
    (hne : K ≠ C) :
    ∃ p : actorImage H (K ⊔ C) ≃* (actorImage H K × actorImage H C),
      ∀ k c, (p.symm (k,c)).val = k.val * c.val := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hR : solvableRadical (H ⧸ pCore 2 H) = ⊥ := by
    have hh := map_solvableRadical_equiv (QuotientGroup.quotientMulEquivOfEq
      (source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv H hH))
    rw [solvableRadical_quotient_solvableRadical,Subgroup.map_bot] at hh
    exact hh.symm
  have hne' : actorImage H K ≠ actorImage H C := by
    intro he
    have hh := congrArg (Subgroup.map H.subtype)
      (hK.eq_of_map_quotient_eq hC (pCore 2 H) he)
    rw [map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hCH] at hh
    exact hne hh
  have hk := hK.map_quotient (pCore 2 H)
  have hc := hC.map_quotient (pCore 2 H)
  obtain ⟨f,hf⟩ := hk.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hR
    (hk.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hc hne')
  have he : actorImage H (K ⊔ C) = actorImage H K ⊔ actorImage H C := by
    change ((K ⊔ C).subgroupOf H).map q = _
    rw [subgroupOf_sup hKH hCH,Subgroup.map_sup]
    rfl
  exact ⟨(MulEquiv.subgroupCongr he).trans f.symm,hf⟩

/-- Original case (3) supplies the full residual and Sylow generation,
using the actual product marking and both component quotient maps. -/
theorem terminal_normal_pair_residual_coordinates
    (K C : Subgroup G) (hKM : K ≤ Mc) (hCM : C ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hC : (C.subgroupOf Mc).IsCComponent)
    (hne : K ≠ C) (hnK : (K.subgroupOf Mc).Normal)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eC : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group)
    (hr : ((solvableResidual Mc).map Mc.subtype : Set G) = (K : Set G) * (C : Set G)) :
    (solvableResidual Mc).map Mc.subtype = K ⊔ C ∧
    actorImage Mc (K ⊔ C) = solvableResidual (Mc ⧸ pCore 2 Mc) ∧
    solvableResidual Mc = pResidual 2 Mc ∧
    (K ⊔ C) ⊔ (T : Subgroup G) = Mc ∧
    ∃ p : actorImage Mc (K ⊔ C) ≃* (actorImage Mc K × actorImage Mc C),
      ∀ k c, (p.symm (k,c)).val = k.val * c.val := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hTH : (T : Subgroup G) ≤ Mc := hout.1.2
  have hCK : C ≤ normalizer (K : Set G) :=
    hCM.trans ((normal_subgroupOf_iff_le_normalizer hKM).mp hnK)
  have hr' : (solvableResidual Mc).map Mc.subtype = K ⊔ C :=
    SetLike.coe_injective (hr.trans (coe_mul_of_right_le_normalizer_left K C hCK).symm)
  have hRi : solvableResidual Mc = (K ⊔ C).subgroupOf Mc := by
    apply map_injective Mc.subtype_injective
    rwa [map_subgroupOf_eq_of_le (sup_le hKM hCM)]
  have he : actorImage Mc (K ⊔ C) = solvableResidual (Mc ⧸ pCore 2 Mc) := by
    change ((K ⊔ C).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) = _
    rw [←hRi,map_solvableResidual_eq _ (QuotientGroup.mk'_surjective _)]
  obtain ⟨p,hp⟩ := source_component_pair_coordinates
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K C hKM hCM hK hC hne
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  let k := ((QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKM)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKM))).symm.trans
      (cComponentTwoCoreQuotientEquiv hK)).symm.trans eK
  let c := ((QuotientGroup.congr _ _ (subgroupOfEquivOfLe hCM)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hCM))).symm.trans
      (cComponentTwoCoreQuotientEquiv hC)).symm.trans eC
  have hm : ResidualQuotientModels (solvableResidual (Mc ⧸ pCore 2 Mc)) :=
    Or.inr (Or.inr ⟨(MulEquiv.subgroupCongr he).symm.trans (p.trans (k.prodCongr c))⟩)
  have hres := (terminal_residual_structure_of_models
    hG T hempty hM hunique hmany hcard e hab hsolv hm).1
  have hgen := congrArg (Subgroup.map Mc.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [←hres,Subgroup.map_sup,hr',Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
    ←MonoidHom.range_eq_map,range_subtype] at hgen
  exact ⟨hr',he,hres,hgen,p,hp⟩


/-- A tensor constituent for any original normal span containing K is
invariant under the whole quotient, contradicting its actual diagram action. -/
theorem source_no_tensor_constituent_on_normal_span
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) V)
    (N : Subgroup (H ⧸ pCore 2 H)) [N.Normal] (hKN : actorImage H K ≤ N)
    (A : Subgroup (H ⧸ pCore 2 H)) (hA : IsElementaryTwo A)
    (hfaith : A ⊓ centralizer (N : Set (H ⧸ pCore 2 H)) = ⊥)
    (hbudget : fixedCodim σ A ≤ 2 * rank A)
    (U : Subrepresentation (σ.comp N.subtype))
    (eN : N ≃* BinaryTensorThree.Factor × BinaryTensorThree.Factor)
    (b : Representation.Equiv U.toRepresentation
      (BinaryTensorThree.baseRepresentation.comp eN.toMonoidHom)) : False := by
  have hstable := BinaryTensorThree.marked_tensor_constituent_invariant
    σ N A hA hfaith hbudget U eN b
  let U' : Subrepresentation σ := {
    toSubmodule := U.toSubmodule
    apply_mem_toSubmodule g v hv := by
      rw [←hstable g]
      exact ⟨v,hv,rfl⟩ }
  have hKq := source_quotient_component
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  obtain ⟨eK,⟨bK⟩⟩ := BinaryTensorThree.exists_component_right_tensor_marking
    U'.toRepresentation N (actorImage H K) hKN (hKq.subgroupOf hKN) eN b
  exact source_no_invariant_tensor_factor
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK U'.toRepresentation eK bK

/-- In original case (3), every subquotient of the original U/Z has no tensor
constituent for the whole pair. The same placed quadratic actor supplies its
budget and faithfulness; no constituent invariance or marking is assumed. -/
theorem terminal_normal_pair_no_tensor_constituents
    (K C : Subgroup G) (hKM : K ≤ Mc) (hCM : C ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hC : (C.subgroupOf Mc).IsCComponent)
    (hne : K ≠ C) (hnK : (K.subgroupOf Mc).Normal)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eC : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group)
    (hr : ((solvableResidual Mc).map Mc.subtype : Set G) = (K : Set G) * (C : Set G)) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
        (B : Subgroup Mc),
        B ≤ (((sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ Mc).pCoreIn 2).subgroupOf Mc ∧
        QuadraticMember a.representation (B.map (QuotientGroup.mk' (pCore 2 Mc))) ∧
        ∃ p : actorImage Mc (K ⊔ C) ≃* (actorImage Mc K × actorImage Mc C),
          (∀ k c, (p.symm (k,c)).val = k.val * c.val) ∧
          ∀ (S : Subrepresentation a.representation) (L : Subrepresentation S.toRepresentation)
            (U : Subrepresentation (L.quotientRepresentation.comp (actorImage Mc (K ⊔ C)).subtype))
            (eN : actorImage Mc (K ⊔ C) ≃* BinaryTensorThree.Factor × BinaryTensorThree.Factor),
            ¬ Nonempty (Representation.Equiv U.toRepresentation
              (BinaryTensorThree.baseRepresentation.comp eN.toMonoidHom)) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hr',hN,hres,hgen,p,hp⟩ := terminal_normal_pair_residual_coordinates
    hG T hempty hM hunique hmany hcard e hab hsolv K C hKM hCM hK hC hne hnK eK eC hr
  obtain ⟨hU,a,B,hB,hA,hq,hcost,_,hfaith⟩ := source_rankTwo_bounded_placed_action
    hG T hempty hM hunique hmany hcard e hab Mc hout
  let := hU
  have hres' : residual Mc = K ⊔ C := by
    rw [GenerationOne.residual,←hres,hr']
  rw [hres'] at hfaith
  let N := actorImage Mc (K ⊔ C)
  let : N.Normal := by
    change (actorImage Mc (K ⊔ C)).Normal
    rw [hN]
    infer_instance
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  refine ⟨hU,a,B,hB,⟨hA,hq,hcost⟩,p,hp,?_⟩
  rintro S L U eN ⟨b⟩
  let A := B.map (QuotientGroup.mk' (pCore 2 Mc))
  have hd : fixedCodim L.quotientRepresentation A ≤ 2 * rank A := by
    have hS := fixedCodim_subrepresentation_le a.representation S A
    have hL := fixedCodim_quotient_add_subrepresentation_le S.toRepresentation L A
    change fixedCodim a.representation A ≤ 2 * rank A at hcost
    omega
  exact source_no_tensor_constituent_on_normal_span
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK L.quotientRepresentation
    N (map_mono (comap_mono le_sup_left)) A hA hfaith hd U eN b


/-- Natural types on both original normal components force full
cross-centralization, through every extension and the original central kernel.
The remaining natural-type input is weaker than a full-support decomposition. -/
theorem terminal_normal_pair_cross_support_of_natural_types
    (K C : Subgroup G) (hKM : K ≤ Mc) (hCM : C ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hC : (C.subgroupOf Mc).IsCComponent)
    (hne : K ≠ C) (hnK : (K.subgroupOf Mc).Normal) (hnC : (C.subgroupOf Mc).Normal)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eC : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group)
    (hr : ((solvableResidual Mc).map Mc.subtype : Set G) = (K : Set G) * (C : Set G))
    [hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    (htypes : ∀ (S : Subrepresentation a.representation) (L : Subrepresentation S.toRepresentation),
      IsIrreducible L.quotientRepresentation →
      ChapterD.NaturalLinearThreeTypes L.quotientRepresentation (actorImage Mc K) ∧
      ChapterD.NaturalLinearThreeTypes L.quotientRepresentation (actorImage Mc C)) :
    ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,C⁆ = ⊥ := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hr',hN,hres,_,p,hp⟩ := terminal_normal_pair_residual_coordinates
    hG T hempty hM hunique hmany hcard e hab hsolv K C hKM hCM hK hC hne hnK eK eC hr
  obtain ⟨B,_,hA,hq,hcost,hfaith⟩ := source_rankTwo_placed_quadratic_actor
    hG T hempty hM hunique hmany hcard e hab Mc hout hU a
  have hres' : residual Mc = K ⊔ C := by rw [GenerationOne.residual,←hres,hr']
  rw [hres'] at hfaith
  let A := B.map (QuotientGroup.mk' (pCore 2 Mc))
  let D := actorImage Mc K
  let E := actorImage Mc C
  let N := actorImage Mc (K ⊔ C)
  let : N.Normal := by
    change (actorImage Mc (K ⊔ C)).Normal
    rw [hN]
    infer_instance
  let : D.Normal := hnK.map (QuotientGroup.mk' (pCore 2 Mc)) (QuotientGroup.mk'_surjective _)
  let : E.Normal := hnC.map (QuotientGroup.mk' (pCore 2 Mc)) (QuotientGroup.mk'_surjective _)
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK
  have hE := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv Mc hout C hCM hC
  let : IsQuasisimple D := hD.2
  let : IsQuasisimple E := hE.2
  have hDN : D ≤ N := map_mono (comap_mono le_sup_left)
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  apply source_cross_support_of_quotient_fixed hG T hempty hM hunique hmany hcard e hab
    Mc hout K C hKM hCM hC a
  apply ChapterD.natural_normal_pair_full_supports_centralize a.representation N D E p hp htypes
  rintro S L U b ⟨f⟩
  have hbudget : fixedCodim L.quotientRepresentation A ≤ 2 * rank A := by
    have hs := fixedCodim_subrepresentation_le a.representation S A
    have hl := fixedCodim_quotient_add_subrepresentation_le S.toRepresentation L A
    change fixedCodim a.representation A ≤ 2 * rank A at hcost
    omega
  exact source_no_tensor_constituent_on_normal_span
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK L.quotientRepresentation N hDN
    A hA hfaith hbudget U b f

/-- Apply the normal-pair separation to the literal full-support criterion.
Only the original natural seeds, their orbit exhaustion and the constituent
types remain; whole-Mc invariance is a conclusion. -/
theorem terminal_normal_pair_full_support_of_natural_types
    (K C : Subgroup G) (hKM : K ≤ Mc) (hCM : C ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hC : (C.subgroupOf Mc).IsCComponent)
    (hne : K ≠ C) (hnK : (K.subgroupOf Mc).Normal) (hnC : (C.subgroupOf Mc).Normal)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eC : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group)
    (hr : ((solvableResidual Mc).map Mc.subtype : Set G) = (K : Set G) * (C : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    (htypes : ∀ (S : Subrepresentation a.representation) (L : Subrepresentation S.toRepresentation),
      IsIrreducible L.quotientRepresentation →
      ChapterD.NaturalLinearThreeTypes L.quotientRepresentation (actorImage Mc K) ∧
      ChapterD.NaturalLinearThreeTypes L.quotientRepresentation (actorImage Mc C))
    (A B : Subgroup G)
    (d : BinaryConjugationSection K A (centralInvolutions T)
      (BinaryLinearThree.W.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (ddual : BinaryConjugationSection K B (centralInvolutions T)
      (BinaryLinearThree.W.dual.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (hA : A ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hB : B ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hAB : A ⊓ B ≤ centralInvolutions T)
    (hexhaust : ⁅conjugateSpanBy (localModule T M) Mc,conjugateSpanBy K (T : Subgroup G)⁆ =
      conjugateSpanBy A Mc)
    (hspan : conjugateSpanBy A (T : Subgroup G) = A ⊔ B) :
    Mc ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) ∧
      ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = A ⊔ B := by
  have hcross := terminal_normal_pair_cross_support_of_natural_types
    hG T hempty hM hunique hmany hcard e hab hsolv
    K C hKM hCM hK hC hne hnK hnC eK eC hr a htypes
  have hKW : K ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    (le_inf d.normalized ddual.normalized).trans (normalizer_inf_normalizer_le_normalizer_sup A B)
  have hW : (A ⊔ B : Subgroup G) ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆ := sup_le hA hB
  have hCW : C ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcross)).trans
      (centralizer_le hW)).trans (Subgroup.centralizer_le_normalizer _)
  have hTW : (T : Subgroup G) ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    rw [←hspan]
    exact le_normalizer_conjugateSpanBy _ _
  have hgen := (terminal_normal_pair_residual_coordinates
    hG T hempty hM hunique hmany hcard e hab hsolv K C hKM hCM hK hC hne hnK eK eC hr).2.2.2.1
  have hWM : Mc ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    rw [←hgen]
    exact sup_le (sup_le hKW hCW) hTW
  exact ⟨hWM,source_full_support_of_normalized_seed_span
    hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K C hKM hCM hK hC hne
    eK A B d ddual hA hB hAB hexhaust (inf_le_left.trans hWM)⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
