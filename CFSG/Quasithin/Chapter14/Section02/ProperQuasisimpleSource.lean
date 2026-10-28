module
public import CFSG.Quasithin.Chapter14.Section02.ProperCommutator
public import CFSG.Quasithin.Chapter14.Section02.ProperSpan
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115.Transport
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender

/-!
# Original marked catalogue entry for the proper completion

The displayed core-centralizer chain in 14.2.15 supplies every literal
hypothesis of 1.1.5 for X=K₁YS and Mc. The full known-simple theorem then
marks the canonical quasisimple residual L by the original central involution:
L=[L,z], L is outside Mc, and its conjugation action belongs to the complete
1.1.5 catalogue. Existing A.3.12 non-enlargement excludes the Bender containing
row, since it would force K₁=L and contradict the original noncentrality of L.

This is the source entry to the remaining comparison in 14.2.15. The higher
rank parabolic and exceptional fixed-centralizer exclusions are not asserted.
The earlier selected-component placement remains explicit for its 14.2.9--10
producer.

Source: Aschbacher--Smith, 14.2.15, printed pp.985--986; 1.1.5(3) and A.3.12.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The original central line supplies the literal 1.1.5 marking on the proper completion. -/
theorem source_proper_completion_hypotheses115
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (_hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (X S : Subgroup G) (hST : S ≤ (T : Subgroup G)) (hSX : S ≤ X)
    (hZS : centralInvolutions T ≤ S)
    (hcore : X.pCoreIn 2 ≠ ⊥) (P : Sylow 2 X)
    (hP : (P : Subgroup X).map X.subtype = S)
    (hCT : (T : Subgroup G) ⊓ centralizer (X.pCoreIn 2 : Set G) ≤ S)
    {z : G} (hzZ : z ∈ centralInvolutions T) (hz : orderOf z = 2) :
    Chapter1.Lemma115Hypotheses X P Mc z := by
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu.symm ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc :=
    (le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)).trans hMc.2
  have hQMcT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hQX : X.pCoreIn 2 ≤ X ⊓ Mc := le_inf (pCoreIn_le 2 X)
    (((pCoreIn_le_sylow X P).trans_eq hP).trans (hST.trans hTMc))
  have hQI : X.pCoreIn 2 ≤ (X ⊓ Mc).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X) hQX
      (inf_le_left.trans (X.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hspan : zpowers z = centralInvolutions T :=
    eq_of_le_of_card_ge (zpowers_le.mpr hzZ) (by rw [Nat.card_zpowers,hz,hZ])
  have hCz : centralizer ({z} : Set G) ≤ Mc := by
    rw [←centralizer_closure,←zpowers_eq_closure,hspan]
    exact hMc.2
  refine ⟨hcore,?_,?_,hz,hP.symm ▸ hZS hzZ,?_,hCz⟩
  · exact ⟨Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T Mc hMc.1 hTMc),
      Chapter1.mem_H_of_isTwoLocal hMc.1.1,hP.symm ▸ (hST.trans hTMc)⟩
  · intro x hx
    exact hSX (hCT ⟨hQMcT hx.1,centralizer_le hQI hx.2⟩)
  · intro s hs
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hzZ).2.2 s (hST (hP ▸ hs))

/-- The complete original 1.1.5 catalogue for the canonical quasisimple residual. -/
theorem source_proper_quasisimple_modelAction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hZS : centralInvolutions T ≤ S)
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    IsQuasisimple L → ∃ z : G, z ∈ centralInvolutions T ∧ orderOf z = 2 ∧
      L = ⁅L,zpowers z⁆ ∧ ¬L ≤ Mc ∧
      ∃ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧
        ModelAction115 L α := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change IsQuasisimple L → ∃ z : G, z ∈ centralInvolutions T ∧ orderOf z = 2 ∧
    L = ⁅L,zpowers z⁆ ∧ ¬L ≤ Mc ∧
    ∃ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧ ModelAction115 L α
  intro hq
  let := hq
  have hcorea : X.pCoreIn 2 ≠ ⊥ := fun hh =>
    hcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hh)
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH
    K S hST hi hN hplacement hcore
  have hCT := (source_proper_completion_core_control hG T hempty hM hu hmany
    hcard e H hH K S hST hi hN hplacement hcore).2
  obtain ⟨hL,_,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcorea hs
  obtain ⟨P,hP⟩ := hs
  have hcZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hZne : centralInvolutions T ≠ ⊥ := by intro hh; rw [hh,card_bot] at hcZ; omega
  let : Nontrivial (centralInvolutions T) := (nontrivial_iff_ne_bot _).mpr hZne
  obtain ⟨z,hzne⟩ := exists_ne (1 : centralInvolutions T)
  have hz : orderOf (z : G) = 2 := orderOf_eq_prime
    ((mem_omegaOneCenterAmbient_iff _ _).mp z.property).2.1
    (fun hh => hzne (Subtype.ext hh))
  have h115 := source_proper_completion_hypotheses115 hG T hempty hM hu hmany hcard e
    X S hST le_sup_right hZS hcorea P hP hCT z.property hz
  have hq' : IsQuasisimple (L.subgroupOf X) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hL.1).symm
  have hcomponent : IsComponent X (L.subgroupOf X) := ⟨hL.2.subnormal,hq'⟩
  obtain ⟨hcomm,hout,α,hα,hm⟩ := Chapter1.lemma_1_1_5_three_knownSimple hG X P Mc z
    h115 (L.subgroupOf X) hcomponent
  rw [map_subgroupOf_eq_of_le hL.1] at hcomm hout
  let d : L ≃* L.subgroupOf X := (subgroupOfEquivOfLe hL.1).symm
  exact ⟨z,z.property,hz,hcomm,hout,MulAut.congr d.symm α,fun x => hα (d x),
    hm.of_mulEquiv d⟩

/-- The Bender-containing row is impossible for the literal selected K₁. -/
theorem source_proper_completion_not_bender
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : (K ⊔ sourceResidual M Mc ⊔ S).pCoreIn 2 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S)) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    ¬ ClassificationModels.IsBenderModel L := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change ¬ ClassificationModels.IsBenderModel L
  intro hc
  obtain ⟨hL,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcore hs
  have hKX : K ≤ X := le_sup_left.trans le_sup_left
  have hSX : S ≤ X := le_sup_right
  obtain ⟨P,hP⟩ := hs
  have hPS : (P : Subgroup X) = S.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSX]
  have hlocal : K.subgroupOf X ∈ Chapter1.L X P := by
    rw [hPS]
    exact (Chapter1.mem_LIn_iff_subgroupOf hSX hKX).mp ⟨hKX,hK⟩
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_bender_containing_component P
    hlocal.1 hL.2 (comap_mono hKL) (hc.of_mulEquiv (subgroupOfEquivOfLe hL.1))
  have he' : K = L := by
    have hh := congrArg (Subgroup.map X.subtype) he
    rwa [map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hL.1] at hh
  have hKC : K ≤ centralizer (centralInvolutions T : Set G) :=
    (le_sup_left.trans_eq hgen).trans
      (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  exact source_proper_completion_component_noncentral hG T hempty hM hu hmany hcard e
    H hH K S hST hgen hK hSN hcore ⟨P,hP⟩ (he'.ge.trans hKC)

/-- The original quasisimple branch enters the marked catalogue with its Bender row eliminated. -/
theorem source_proper_quasisimple_catalogue_entry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hZS : centralInvolutions T ≤ S)
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    IsQuasisimple L → ¬ClassificationModels.IsBenderModel L ∧
      ∃ z : G, z ∈ centralInvolutions T ∧ orderOf z = 2 ∧
      L = ⁅L,zpowers z⁆ ∧ ¬L ≤ Mc ∧
      ∃ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧
        ModelAction115 L α := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change IsQuasisimple L → ¬ClassificationModels.IsBenderModel L ∧ ∃ z : G,
    z ∈ centralInvolutions T ∧ orderOf z = 2 ∧ L = ⁅L,zpowers z⁆ ∧ ¬L ≤ Mc ∧
    ∃ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) ∧ ModelAction115 L α
  intro hq
  have hcorea : X.pCoreIn 2 ≠ ⊥ := fun hh =>
    hcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hh)
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH
    K S hST hi hN hplacement hcore
  exact ⟨source_proper_completion_not_bender hG T hempty hM hu hmany hcard e
    H hH K S hST hgen hK hSN hcorea hs,
    source_proper_quasisimple_modelAction hG T hempty hM hu hmany hcard e
      H hH K S hST hi hN hplacement hK hSN hZS hcore hq⟩

end CFSG.Quasithin.Chapter14.Section02
