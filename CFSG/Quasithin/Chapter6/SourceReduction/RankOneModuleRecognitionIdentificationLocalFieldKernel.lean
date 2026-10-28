module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldReduced
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The faithful field-plane action and its actual components

For the arranged Sylow P, the natural action has order at most eight.
The image of P intersect L has order four, and the field witness fixes U
without fixing the natural layer. Thus P is contained in L C_G(U).

The kernel on the literal C_G(U)-closure quotient centralizes U and the
quotient, so its two-residual centralizes the original natural layer.
Faithfulness makes L normalize this residual. The Sylow supplement and
uniqueness over LP kill the residual in the characteristic-two centralizer.
Reducedness gives the reverse containment, identifying the kernel with
O₂(C_G(U)). Components of this faithful action then lift to actual
C-components with their intrinsic quotients and quotient maps preserved.

The companion Chapter12 module discharges uniqueness from the chosen
module and applies the existing B.5 component restriction to these lifts.
No LocalAnalysis or later recognition statement is assumed.
Source: Aschbacher--Smith, 6.2.4(4) and 6.2.7, printed pp.680,683.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem natural_two_actor_bound
    {F X : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [Group X] [Finite X] (C : Subgroup X) [C.Normal]
    (e : C ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) X (Fin 2 → F)) (hρ : Function.Injective ρ)
    (he : ∀ (c : C) v, ρ (c : X) v = Matrix.mulVec (e c).val v)
    (hF : Nat.card F = 2 ^ 2) (A : Subgroup X) (hA : IsPGroup 2 A) : Nat.card A ≤ 8 := by
  let α : A →* MulAut C := (MulAut.conjNormal : X →* MulAut C).comp A.subtype
  have hker : α.ker = ⊥ := by
    by_contra hn
    have hk : IsPGroup 2 α.ker := hA.to_subgroup _
    obtain ⟨k,hkpos,hkcard⟩ := hk.nontrivial_iff_card.mp
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hn)
    have hdiv : 2 ∣ Nat.card α.ker := hkcard ▸ dvd_pow_self 2 (by omega : k ≠ 0)
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := α.ker) 2 hdiv
    have hx2 : ((x : A) : X) ^ 2 = 1 := by
      have hh := pow_orderOf_eq_one x
      rw [hx] at hh
      exact congrArg (fun a : α.ker => ((a : A) : X)) hh
    have hc : ((x : A) : X) ∈ centralizer (C : Set X) := by
      intro c hc
      have hh := congrArg (fun f : MulAut C => (f ⟨c,hc⟩ : X)) x.property
      change ((x : A) : X) * c * ((x : A) : X)⁻¹ = c at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hx1 := Representation.SL2NaturalOffenders.centralizing_square_one_eq_one C e ρ hρ he hx2 hc
    have hxone : x = 1 := Subtype.ext (Subtype.ext hx1)
    rw [hxone, orderOf_one] at hx
    contradiction
  let β := (MulAut.congr (e.trans (Theory.PSL2.sl2QuotientEquiv F))).toMonoidHom.comp α
  have hi : Function.Injective β := (MulAut.congr _).injective.comp
    ((MonoidHom.ker_eq_bot_iff α).mp hker)
  have hd : Nat.card A ∣ 120 := by
    exact (card_dvd_of_injective β hi).trans
      (by simpa using Theory.PSL2.BinaryAutomorphismOrder.aut_card_dvd hF)
  obtain ⟨k,hk⟩ := hA.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) 15 := hk ▸ (by decide : Nat.Coprime 2 15).pow_left k
  exact Nat.le_of_dvd (by decide) (hcop.dvd_of_dvd_mul_right hd)



variable {G : Type*} [Group G] [Finite G]

/-- The arranged field-plane centralizer and L contain the full ambient Sylow. -/
theorem local_field_sylow_cover
    {L B U : Subgroup G} [IsElementaryAbelian 2 B]
    (hnat : IsNaturalModule L B 2)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (P : Sylow 2 G) (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    (hfield : IsInvolutoryFieldFixedSpace L (P : Subgroup G) B U 2)
    (hUne : U ≠ ⊥) : (P : Subgroup G) ≤ L ⊔ centralizer (U : Set G) := by
  have hn := hnat
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnat
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  have hm : IsConjugationModel L B (Representation.specialLinearNatural (k := F) 2) := ⟨e,f,hf⟩
  obtain ⟨j,E,hE⟩ := NaturalAction.marking e f hf
  let C := ChapterE.inducedAutomizer B L
  let : C.Normal := NaturalAction.induced_normal hNL
  let ρ : Representation (ZMod 2) (ChapterE.Automizer B) (Fin 2 → F) :=
    E.conjRingEquiv.toMonoidHom.comp (ChapterE.automizerRepresentation B)
  have hρ : Function.Injective ρ := E.conjRingEquiv.injective.comp
    (ChapterE.automizerRepresentation_injective B)
  have hnat : ∀ (c : C) v, ρ (c : ChapterE.Automizer B) v = Matrix.mulVec (j c).val v := by
    intro c v
    change E (ChapterE.automizerRepresentation B c (E.symm v)) = _
    rw [hE,E.apply_symm_apply]
  let N := normalizer (B : Set G)
  let a := B.normalizerMonoidHom.rangeRestrict
  let I := ChapterE.inducedAutomizer B (P : Subgroup G)
  let S := (P : Subgroup G) ⊓ L
  let D := (P : Subgroup G) ⊓ (L ⊔ centralizer (U : Set G))
  let I₀ := ChapterE.inducedAutomizer B S
  let I₁ := ChapterE.inducedAutomizer B D
  have hi : Nat.card I ≤ 8 := natural_two_actor_bound C j ρ hρ hnat hF I
    (P.isPGroup'.comap_subtype.map _)
  have hS : S ≤ D := le_inf inf_le_left (inf_le_right.trans le_sup_left)
  have h01 : I₀ ≤ I₁ := map_mono (comap_mono hS)
  have h1i : I₁ ≤ I := map_mono (comap_mono inf_le_left)
  have h0C : I₀ ≤ C := map_mono (comap_mono inf_le_right)
  obtain ⟨Q,hQ⟩ := NormalSylowQuotientAction.intersection_sylow P L (hPB.trans hNL)
  let Q' := Q.mapSurjective (NaturalAction.layerAction_surjective hm.normalizes)
  let Q'' := Q'.mapSurjective (f := j.toMonoidHom) j.surjective
  have hQc : Nat.card Q'' = 4 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 Q'').symm.toEquiv,
      Nat.card_congr Multiplicative.toAdd,hF]
    decide
  have h0c : Nat.card I₀ = 4 := by
    have hs : I₀ = (Q' : Subgroup C).map C.subtype := by
      change I₀ = ((Q : Subgroup L).map (NaturalAction.layerAction hm.normalizes)).map C.subtype
      rw [←NaturalAction.induced_map_layerAction hm.normalizes,hQ,subgroupOf_map_subtype]
    rw [hs,card_map_of_injective C.subtype_injective]
    change Nat.card Q' = 4
    rw [←card_map_of_injective (f := j.toMonoidHom) (K := (Q' : Subgroup C)) j.injective]
    exact hQc
  have hfield0 := hfield
  obtain ⟨t,htP,htB,hU,htfield⟩ := hfield0
  have htH : (t : G) ∈ centralizer (U : Set G) := by
    intro u hu
    exact mem_centralizer_singleton_iff.mp (hU.le hu).2
  have htne : (t : G) ∉ centralizer (B : Set G) := by
    intro ht
    have hBU : B ≤ U := by
      rw [hU]
      exact le_inf le_rfl (fun b hb => mem_centralizer_singleton_iff.mpr (ht b hb))
    obtain ⟨δ,hδ,hker,_⟩ := field_fixedSpace_displacement hn hfield hUne
    obtain ⟨u,hu⟩ := ne_bot_iff_exists_ne_one.mp hUne
    obtain ⟨b,hb⟩ := hδ u
    have hk : b ∈ δ.ker := by rw [hker]; exact hBU b.property
    exact hu (hb.symm.trans hk)
  have htout : a ⟨t,htB⟩ ∉ C := by
    rintro ⟨l,hl,he⟩
    have hlH : (l : G) ∈ centralizer (U : Set G) := by
      intro u hu
      have hh := congrArg (fun z : ChapterE.Automizer B => (z.val ⟨u,(hU.le hu).1⟩ : G)) he
      change (l : G) * u * (l : G)⁻¹ = (t : G) * u * (t : G)⁻¹ at hh
      rw [←htH u hu,mul_inv_cancel_right] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hlC := (field_fixedSpace_inner_centralizer hn hfield hUne).le ⟨hl,hlH⟩
    apply htne
    intro b hb
    have hh := congrArg (fun z : ChapterE.Automizer B => (z.val ⟨b,hb⟩ : G)) he
    change (l : G) * b * (l : G)⁻¹ = (t : G) * b * (t : G)⁻¹ at hh
    have hcb : b * (l : G) = (l : G) * b := hlC.2 b hb
    rw [←hcb,mul_inv_cancel_right] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have htI : a ⟨t,htB⟩ ∈ I₁ := mem_map_of_mem a
    (show (⟨t,htB⟩ : N) ∈ D.subgroupOf N from ⟨htP,mem_sup_right htH⟩)
  have hlt : 4 < Nat.card I₁ := by
    by_contra hh
    have he := eq_of_le_of_card_ge h01 (by omega)
    exact htout (h0C (he.ge htI))
  have hI : I₁ = I := by
    have hp : IsPGroup 2 I₁ := (P.isPGroup'.to_le (show D ≤ P from inf_le_left)).comap_subtype.map _
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    have hk3 : 3 ≤ k := by
      by_contra hk3
      have hk2 : k ≤ 2 := by omega
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hk2
      rw [←hk] at hh
      omega
    apply eq_of_le_of_card_ge h1i
    exact hi.trans (hk ▸ Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hk3)
  intro p hp
  have hpI : a ⟨p,hPB hp⟩ ∈ I := mem_map_of_mem a hp
  rw [←hI] at hpI
  obtain ⟨d,hd,he⟩ := hpI
  have hpd : (⟨p,hPB hp⟩ : N) * d⁻¹ ∈ a.ker := by
    change a _ = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hc : p * (d : G)⁻¹ ∈ centralizer (B : Set G) := by
    have hh : (⟨p,hPB hp⟩ : N) * d⁻¹ ∈ B.normalizerMonoidHom.ker := congrArg Subtype.val hpd
    rwa [normalizerMonoidHom_ker] at hh
  have hh : p * (d : G)⁻¹ ∈ L ⊔ centralizer (U : Set G) :=
    mem_sup_right ((centralizer_le (hU.le.trans inf_le_left)) hc)
  have hprod := (L ⊔ centralizer (U : Set G)).mul_mem hh hd.2
  change p * (d : G)⁻¹ * (d : G) ∈ L ⊔ centralizer (U : Set G) at hprod
  simpa only [inv_mul_cancel_right] using hprod


private theorem local_unique_rechosen_sylow
    {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (P : Sylow 2 G) (hPB : (P : Subgroup G) ≤ normalizer (layer L R : Set G)) :
    ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (P : Subgroup G) ≤ N → N = M := by
  let B := layer L R
  let D := normalizer (B : Set G)
  obtain ⟨m,hm⟩ := MulAction.exists_smul_eq D (P.subtype hPB) (T.subtype h.sylow_normalizes_layer)
  let e := MulAut.conj (m : G)
  have hPm : (P : Subgroup G).map e.toMonoidHom = (T : Subgroup G) := by
    have he := congrArg (fun S : Sylow 2 D => (S : Subgroup D).map D.subtype) hm
    change (((P : Subgroup G).subgroupOf D).map (MulAut.conj m).toMonoidHom).map D.subtype = _ at he
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_normalizes_layer] at he
    rw [←he]
    have hc : D.subtype.comp (MulAut.conj m).toMonoidHom = e.toMonoidHom.comp D.subtype := rfl
    rw [map_map,hc,←map_map,map_subgroupOf_eq_of_le hPB]
  have hmM : (m : G) ∈ M := hE.normalizer_le m.property
  have hLm : L.map e.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp
    (((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal) hmM)
  have hMm : M.map e.toMonoidHom = M := mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hmM)
  intro N hN hLN
  have hNM : N.map e.toMonoidHom = M := hu _ (Theory.GroupTheory.isMaximalTwoLocal_map e hN) (by
    have hh := map_mono (f := e.toMonoidHom) hLN
    rwa [Subgroup.map_sup,hLm,hPm] at hh)
  exact map_injective e.injective (hNM.trans hMm.symm)

namespace LocalFieldQuotientAction
variable {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}

/-- Source 6.2.4(4): the kernel on the literal field-plane closure quotient
is the two-core of its full centralizer. -/
theorem action_kernel_eq_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U = 4)
    (hout : ¬ Centralizer U ≤ normalizer (layer L R : Set G)) :
    (action (layer L R) U).ker = pCore 2 (Centralizer U) := by
  let := h.layer_elementary
  let B := layer L R
  let H := Centralizer U
  let J := conjugateSpanBy B H
  let K := commutatorPreimage H J U
  let Y := (pResidual 2 K).map K.subtype
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; contradiction
  have hUB : U ≤ B := hfield.choose_spec.2.2.1.le.trans inf_le_left
  have hBH : B ≤ H := B.le_centralizer.trans (centralizer_le hUB)
  have hHN : H ≤ normalizer (U : Set G) := Subgroup.centralizer_le_normalizer _
  have hKH : K ≤ H := commutatorPreimage_le H J U
  have hHK : H ≤ normalizer (K : Set G) := commutatorPreimage_normalized H J U H hHN
    H.le_normalizer (le_normalizer_conjugateSpanBy B H) hHN
  have hYK : Y ≤ K := map_subtype_le _
  have hHY : H ≤ normalizer (Y : Set G) := hHK.trans
    (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
  have hYC : Y ≤ centralizer (B : Set G) := residual_centralizes_of_two_layer K B U
    ((IsElementaryAbelian.isPGroup 2 B).to_le hUB) hKH
    ((commutator_mono le_rfl (le_conjugateSpanBy B H)).trans
      (commutator_commutatorPreimage_le H J U hHN))
  have hNL : normalizer (B : Set G) ≤ normalizer (L : Set G) :=
    hE.normalizer_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)
  have hLN : L ≤ normalizer (B : Set G) := normalizer_commutator_ge_right R L
  have hLC : ⁅L,centralizer (B : Set G)⁆ ≤ L.pCoreIn 2 := by
    apply le_trans (le_inf ?_ ?_) (natural_centralizer_eq_core hnat).le
    · exact le_normalizer_iff_commutator_le_left.mp
        ((Subgroup.centralizer_le_normalizer _).trans hNL)
    · exact le_normalizer_iff_commutator_le_right.mp
        (hLN.trans (normalizer_le_normalizer_centralizer B))
  have hQH : L.pCoreIn 2 ≤ H :=
    ((natural_centralizer_eq_core hnat).ge.trans inf_le_right).trans (centralizer_le hUB)
  have hLY : L ≤ normalizer (Y : Set G) := normalizes_residual_of_commutator_le_two
    L H K (L.pCoreIn 2) hHK hQH (isPGroup_pCoreIn 2 L)
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    ((commutator_mono le_rfl hYC).trans hLC)
  have hML := (normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal
  obtain ⟨P,_,hBP,hPL,hPB,hfieldP,hSyl⟩ := field_fixedSpace_sylow_arrangement
    T L M B U n h.sylow_normalizes_layer hE.normalizer_le hML hE.ti hnat hfield hUne
  have hcover : (P : Subgroup G) ≤ L ⊔ H := local_field_sylow_cover hnatural.2.1 hNL
    P hPB (hnatural.1 ▸ hfieldP) hUne
  have hself : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2 :=
    (field_fixedSpace_even_local P (h.simpleQTKE.evenCharacteristic P) hBP hPB hfieldP hUne).2.1
  have hHM : ¬ H ≤ M := by
    intro hh
    exact hout (fun x hx => hE.localCentralizer_le_normalizer hUne hUB ⟨hh hx,hx⟩)
  have hYbot : Y = ⊥ := normal_eq_bot_of_unique_core (L ⊔ (P : Subgroup G)) H M Y
    (local_unique_rechosen_sylow h hE hu P hPB) hHM hself (hYK.trans hKH) hHY
    (sup_le hLY (hcover.trans (sup_le hLY hHY)))
  have hres : pResidual 2 K = ⊥ :=
    (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hYbot
  have hp : IsPGroup 2 K := (isPGroup_quotient_pResidual (G := K) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 K)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk',hres])
  have hkc : K ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes hp hKH hHK
  apply le_antisymm
  · rw [action_ker B U hBH]
    have hh := subgroupOf_mono H hkc
    simpa only [pCoreIn,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
  · let a := (action B U).rangeRestrict
    have hm : (pCore 2 H).map a ≤ pCore 2 (action B U).range :=
      le_sSup ⟨Subgroup.Normal.map inferInstance a (action B U).rangeRestrict_surjective,
        pCore_isPGroup.map a⟩
    have hc := action_range_core h hnatural hE hfactor hfield hUc.ge
    rw [hc] at hm
    intro x hx
    have hxone : a x = 1 := hm (mem_map_of_mem a hx)
    exact congrArg Subtype.val hxone

end LocalFieldQuotientAction


namespace LocalFieldQuotientAction
variable {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}

/-- Every component of the original faithful quotient lifts to a genuine
C-component of C_G(U), with its intrinsic quotient and action map unchanged. -/
theorem action_component_lift
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U = 4)
    (hout : ¬ Centralizer U ≤ normalizer (layer L R : Set G))
    (J : Subgroup (action (layer L R) U).range) (hJ : IsComponent _ J) :
    ∃ K : Subgroup (Centralizer U), K.IsCComponent ∧
      K.map (action (layer L R) U).rangeRestrict = J ∧
      ∃ e : (K ⧸ pCore 2 K) ≃* J, ∀ k : K,
        ((e (QuotientGroup.mk' (pCore 2 K) k) : J) : (action (layer L R) U).range) =
          (action (layer L R) U).rangeRestrict k := by
  let H := Centralizer U
  let a := action (layer L R) U
  let q := QuotientGroup.mk' (pCore 2 H)
  let e : (H ⧸ pCore 2 H) ≃* a.range :=
    (QuotientGroup.quotientMulEquivOfEq
      (action_kernel_eq_core h hnatural hE hfactor hu hfield hUc hout).symm).trans
      (QuotientGroup.quotientKerEquivRange a)
  have he : e.toMonoidHom.comp q = a.rangeRestrict := by ext x; rfl
  have hJq := hJ.map_equiv e.symm
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  obtain ⟨K,hK,hmap⟩ := hJq.isCComponent.exists_map_quotient_eq (pCore 2 H)
  have hKJ : (K.map q).map e.toMonoidHom = J := by
    rw [hmap,map_map]
    have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id a.range := by
      apply MonoidHom.ext
      intro x
      exact e.apply_symm_apply x
    rw [hid,map_id]
  have himage : K.map a.rangeRestrict = J := by rw [←he,←map_map,hKJ]
  let eK : (K ⧸ pCore 2 K) ≃* J :=
    (cComponentTwoCoreQuotientEquiv hK).trans
      (((K.map q).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hKJ))
  refine ⟨K,hK,himage,eK,?_⟩
  intro k
  rfl

end LocalFieldQuotientAction

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
