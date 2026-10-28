module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.Sections
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.SporadicLargeSylow
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.ComponentFixer
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.Mathieu.M24.Properties.Order

/-!
# Sporadic containers of the original exceptional sections

All three exceptional quotients force 20160 to divide the ambient order.
For the J₂ quotient the stronger order obstruction leaves J₂, Held and
Rudvalis. In the latter two groups the local normalizer orders force the
smaller group's two-core to vanish. The original full Sylow would then
act faithfully on J₂, whose automorphism group has two-part at most 256;
the ambient two-part is larger. Thus a J₂ section equals its sporadic
container. The literal local component and its Sylow normalization are
retained throughout.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, and 13.6.27, p.934.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional

theorem all_local_bounds {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H)
    (ht : ∀ N : Subgroup H, IsMaximalTwoLocal N → (T : Subgroup H) ≤ N →
      ¬ 20160 ∣ Nat.card N)
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsMaximalTwoLocal N)
    (hSN : (S : Subgroup H) ≤ N) : ¬ 20160 ∣ Nat.card N := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H S T
  have hm := (Theory.Quasithin.maximalTwoLocal_overgroup_conj_iff g S N).mpr ⟨hN,hSN⟩
  rw [hg] at hm
  have hh := ht _ hm.1 hm.2
  rwa [card_map_of_injective (MulAut.conj g).injective] at hh

theorem not_section_of_local_bounds {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] (e : G ≃* H)
    (hb : ∀ (T : Sylow 2 H) (N : Subgroup H), IsMaximalTwoLocal N →
      (T : Subgroup H) ≤ N → ¬ 20160 ∣ Nat.card N)
    (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B))
    (hcore : pCore 2 B ≠ ⊥) : False := by
  let U := (pCore 2 B).map B.subtype
  have hU : U ≠ ⊥ := fun he => hcore
    ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hloc : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩
  have hnorm := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  have hBN : B ≤ normalizer (U : Set G) := B.le_normalizer.trans hnorm
  have hSN : (S : Subgroup G) ≤ normalizer (U : Set G) := hn.trans hnorm
  obtain ⟨N,hNN,hN⟩ := Finite.exists_le_maximal hloc
  have hd : 20160 ∣ Nat.card N := (section_card_dvd h).trans
    (card_dvd_of_le (hBN.trans hNN))
  have hnm := hb (S.mapSurjective e.surjective) (N.map e.toMonoidHom)
    (Theory.Quasithin.isMaximalTwoLocal_map e hN)
    (show (S : Subgroup G).map e.toMonoidHom ≤ N.map e.toMonoidHom from
      map_mono (hSN.trans hNN))
  rw [card_map_of_injective e.injective] at hnm
  exact hnm hd

private theorem held_candidate_bound (i : Fin 3) :
    ¬ 20160 ∣ Nat.card (Held.TwoLocalCandidates.subgroup i) := by
  have hmax34 (j : Bool) :
      ¬ 7 ∣ Nat.card (Held.LocalPairs.PairCoverage.localOvergroup j) := by
    let f := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.SixPoint.quotientAction j
    have hc := f.ker.card_mul_index
    rw [index_ker] at hc
    have hquot : Nat.card (Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.LocalQuotient j) ∣ 2160 := by
      rw [← hc]
      have hd : Nat.card f.range ∣ 720 := by
        simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
          using f.range.card_subgroup_dvd_card
      exact Nat.mul_dvd_mul
        (Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three j) hd
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2)
      (G := Held.LocalPairs.PairCoverage.localOvergroup j)).exists_card_eq
    intro hd
    rw [← (pCore 2 (Held.LocalPairs.PairCoverage.localOvergroup j)).card_mul_index,hn] at hd
    have hh := (((by decide : Nat.Coprime 7 2).pow_right n).dvd_of_dvd_mul_left hd).trans hquot
    norm_num at hh
  fin_cases i
  · exact fun hd => hmax34 false ((by decide : 7 ∣ 20160).trans hd)
  · exact fun hd => hmax34 true ((by decide : 7 ∣ 20160).trans hd)
  · change ¬ 20160 ∣ Nat.card Held.TwoLocalCandidates.max5
    rw [Held.InvolutionFixedData.TwoB.max5_card]
    decide

theorem held_local_bound (S : Sylow 2 Held.He) (N : Subgroup Held.He)
    (hN : IsMaximalTwoLocal N) (hSN : (S : Subgroup Held.He) ≤ N) :
    ¬ 20160 ∣ Nat.card N := by
  obtain ⟨T,hcatalogue⟩ := Held.TwoLocalCandidates.MaximalNormalizerCatalogue.exists_sylow_catalogue
  apply all_local_bounds T _ S N hN hSN
  intro M hM hTM
  obtain ⟨R,hR,hn,he,hRM⟩ := exists_normal_elementary_normalizer_of_sylow_le T hM hTM
  obtain ⟨i,g,hg⟩ := hcatalogue R hR hn he (hRM ▸ hM)
  rw [hRM,hg,card_map_of_injective (MulAut.conj g).injective]
  exact held_candidate_bound i

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The exceptional section excludes M₁₁ by its original quotient order. -/
theorem not_mathieu_eleven {B : Subgroup G}
    (h : IsModel (B ⧸ pCore 2 B)) (e : G ≃* Sporadic.Mathieu.M11) : False := by
  have hd := ambient_card_dvd h
  rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m11_order] at hd
  norm_num at hd

omit [Finite G] in
/-- The exceptional section excludes M₁₂ by its original quotient order. -/
theorem not_mathieu_twelve {B : Subgroup G}
    (h : IsModel (B ⧸ pCore 2 B)) (e : G ≃* Sporadic.Mathieu.M12) : False := by
  have hd := ambient_card_dvd h
  rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m12_order] at hd
  norm_num at hd

omit [Finite G] in
/-- The additional J₁ row cannot contain any of the exceptional sections. -/
theorem not_janko_one {B : Subgroup G}
    (h : IsModel (B ⧸ pCore 2 B)) (e : G ≃* Janko1.Model) : False := by
  have hd := ambient_card_dvd h
  rw [Nat.card_congr e.toEquiv, Janko1.card_model] at hd
  norm_num at hd

omit [Finite G] in
private theorem jankoTwo_quotient_card {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    Nat.card (B ⧸ pCore 2 B) = 604800 := by
  obtain ⟨e⟩ := h
  exact (Nat.card_congr e.toEquiv).trans
    Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier

omit [Finite G] in
private theorem jankoTwo_ambient_card_dvd {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    604800 ∣ Nat.card G := by
  rw [← jankoTwo_quotient_card h]
  exact (card_quotient_dvd_card _).trans B.card_subgroup_dvd_card

private theorem jankoTwo_aut_card_dvd :
    Nat.card (MulAut Sporadic.LeechRelated.J2.Carrier) ∣ 256 * 4725 := by
  have hi : Nat.card (MulAut.innerSubgroup Sporadic.LeechRelated.J2.Carrier) ∣ 604800 := by
    rw [← Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    exact card_dvd_of_surjective (MulAut.conj : Sporadic.LeechRelated.J2.Carrier →*
      MulAut Sporadic.LeechRelated.J2.Carrier).rangeRestrict
      (MulAut.conj : Sporadic.LeechRelated.J2.Carrier →*
        MulAut Sporadic.LeechRelated.J2.Carrier).rangeRestrict_surjective
  have ho : Nat.card (MulAut.Outer Sporadic.LeechRelated.J2.Carrier) ∣ 2 := by
    have hp := Nat.card_pos (α := MulAut.Outer Sporadic.LeechRelated.J2.Carrier)
    have hb := Sporadic.LeechRelated.J2.outer_card_le_two
    have hh : Nat.card (MulAut.Outer Sporadic.LeechRelated.J2.Carrier) = 1 ∨
      Nat.card (MulAut.Outer Sporadic.LeechRelated.J2.Carrier) = 2 := by omega
    rcases hh with hh | hh <;> simp [hh]
  rw [← (MulAut.innerSubgroup Sporadic.LeechRelated.J2.Carrier).card_mul_index]
  change Nat.card (MulAut.innerSubgroup Sporadic.LeechRelated.J2.Carrier) *
    Nat.card (MulAut.Outer Sporadic.LeechRelated.J2.Carrier) ∣ 256 * 4725
  simpa only [show 256 * 4725 = 604800 * 2 from rfl] using Nat.mul_dvd_mul hi ho

private theorem jankoTwo_sylow_bound (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier))
    (hc : pCore 2 B = ⊥) (hE : IsEvenCharacteristicAt S) :
    Nat.card S ∣ 256 := by
  obtain ⟨e⟩ := h
  let eB : B ≃* Sporadic.LeechRelated.J2.Carrier :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans e
  let : IsSimpleGroup B := (IsModel.isSimple (Or.inl ⟨eB⟩))
  let := local_perfect hB
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S hE hB hn
  let f := B.normalizerMonoidHom.comp (inclusion hn)
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hf]
    refine ⟨a.property, ?_⟩
    change inclusion hn a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha
  have hd : Nat.card S ∣ 256 * 4725 :=
    (card_dvd_of_injective f hinj).trans
      ((Nat.card_congr (MulAut.congr eB).toEquiv).symm ▸ jankoTwo_aut_card_dvd)
  have hcop : Nat.Coprime (Nat.card S) 4725 := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 4725).pow_left n
  exact hcop.dvd_of_dvd_mul_right hd

theorem held_twoPower : 512 ∣ Nat.card Held.He := by
  open Held.LocalPairs.SylowGeometry.Calculations in
  have hp := representative_isPGroup
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hl := Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.representative_card_ge_of_orbit_labels
    Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel_eq_card_orbit
  have hn9 : 9 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact (by decide : 2 ^ 9 ≤ 1024).trans (hn ▸ hl)
  have hd : 512 ∣ Nat.card Held.LocalPairs.SylowGeometry.Calculations.representative := by
    rw [hn]
    exact pow_dvd_pow 2 hn9
  exact hd.trans (card_subgroup_dvd_card _)

/-- The original Sylow-normalized J₂ section cannot occur in Held. -/
theorem not_held_of_jankoTwo (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier))
    (e : G ≃* Held.He) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hd : 512 ∣ Nat.card G := (Nat.card_congr e.toEquiv).symm ▸ held_twoPower
    have hs := S.pow_dvd_card_of_pow_dvd_card (n := 9) hd
    have hb := jankoTwo_sylow_bound S B hB hn h hc
      (MainConverse.SporadicLocal.he_evenCharacteristic_of_equiv e S)
    have hh : 512 ∣ 256 := hs.trans hb
    norm_num at hh
  · exact not_section_of_local_bounds e held_local_bound S B hn (Or.inl h) hc

/-- The original Sylow-normalized J₂ section cannot occur in Rudvalis. -/
theorem not_rudvalis_of_jankoTwo (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier))
    (e : G ≃* Rudvalis.Model) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hd : 512 ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv, Rudvalis.model_card]
      decide
    have hs := S.pow_dvd_card_of_pow_dvd_card (n := 9) hd
    have hb := jankoTwo_sylow_bound S B hB hn h hc
      (MainConverse.evenCharacteristic_of_model_equiv e
        MainConverse.SporadicLocal.ru_evenCharacteristic S)
    have hh : 512 ∣ 256 := hs.trans hb
    norm_num at hh
  · apply not_section_of_local_bounds e _ S B hn (Or.inl h) hc
    intro T N hN hTN hd
    exact Rudvalis.SylowOvergroups.not_nine_dvd_card_twoLocal T N hN.1 hTN
      ((by decide : 9 ∣ 20160).trans hd)

/-- A J₂ section in an actual Theorem C sporadic containing model equals
that model. No proper-embedding theorem is assumed. -/
theorem eq_top_of_jankoTwo_sporadic (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier))
    (name : ClassificationModels.SporadicName) (hne : name ≠ .j3)
    (he : Nonempty (G ≃* name.Carrier)) : B = ⊤ := by
  obtain ⟨e⟩ := he
  have hd := jankoTwo_ambient_card_dvd h
  cases name with
  | m11 => exact (not_mathieu_eleven (Or.inl h) e).elim
  | m12 => exact (not_mathieu_twelve (Or.inl h) e).elim
  | m22 =>
    rw [Nat.card_congr e.toEquiv] at hd
    change 604800 ∣ Nat.card Sporadic.Mathieu.M22 at hd
    rw [Sporadic.Mathieu.m22_order] at hd
    norm_num at hd
  | m23 =>
    rw [Nat.card_congr e.toEquiv] at hd
    change 604800 ∣ Nat.card Sporadic.Mathieu.M23 at hd
    rw [Sporadic.Mathieu.m23_order] at hd
    norm_num at hd
  | m24 =>
    rw [Nat.card_congr e.toEquiv] at hd
    change 604800 ∣ Nat.card Sporadic.Mathieu.M24 at hd
    rw [Sporadic.Mathieu.m24_order] at hd
    norm_num at hd
  | j2 =>
    apply B.eq_top_of_card_eq
    apply le_antisymm (Nat.card_le_card_of_injective B.subtype B.subtype_injective)
    rw [Nat.card_congr e.toEquiv]
    change Nat.card Sporadic.LeechRelated.J2.Carrier ≤ Nat.card B
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier,
      ← jankoTwo_quotient_card h]
    exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 B))
      (QuotientGroup.mk'_surjective _)
  | j3 => exact (hne rfl).elim
  | j4 =>
    rw [Nat.card_congr e.toEquiv] at hd
    change 604800 ∣ Nat.card Janko4.Model at hd
    rw [Janko4.Cardinality.model_card] at hd
    norm_num at hd
  | hs =>
    rw [Nat.card_congr e.toEquiv] at hd
    have hh := hd.trans Sporadic.LeechRelated.HS.card_carrier_dvd
    norm_num at hh
  | he => exact (not_held_of_jankoTwo S B hB hn h e).elim
  | ru => exact (not_rudvalis_of_jankoTwo S B hB hn h e).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
