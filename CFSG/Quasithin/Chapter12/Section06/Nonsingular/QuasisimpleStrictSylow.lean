module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleSylowBound
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.CComponent.CharacteristicTwo

/-!
# Strict Sylow bounds in the quasisimple nonsingular branch

If a Sylow subgroup of the original G_v were ambient Sylow, even
characteristic would make G_v characteristic two. Its actual C-component
K_v therefore could not be quasisimple. Equality in the source bound
|S:T_v| ≤ |T:T_v| = 4 would make S ambient Sylow, so the index is at most
two. In particular the original T_v is normal in the selected S.

Intersect S with the relatively normal K_v and pass through a surjective
model map. The simultaneous normalizer of the original L_v and V_v images
still has Sylow index at most two. In HS the moved image has order at least
sixteen, whereas a Sylow-normalized elementary subgroup has order at most
eight. In Ru its normalizer contains the original A₆ section, so its order
is divisible by nine, excluding full Sylow containment. Thus in both rows
the simultaneous normalizer and the moved-subgroup normalizer have index
exactly two in a selected quotient Sylow.

The final theorem applies these restrictions at the actual preferred
escaping point, preserving V, C_V(L), conjugation and the central projection.
The index-two HS/Ru cases and J₄ still require exclusion; blocks, splitting
and fixed-space elimination also remain. Neither 12.6.2 nor 12.6.23 is
asserted. Earlier invariance and TI retain producer qt-d-1222-source and
final discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, 1.1.4(2,6), pp.500--501, and the Sylow bounds
in 12.6.4 and the proof of 12.6.12, pp.824--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- An ambient Sylow in G_v would force characteristic two and exclude its actual quasisimple component. -/
theorem SourceHypothesis.nonsingular_quasisimple_no_ambient_sylow
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) (P : Sylow 2 G) :
    ¬ (P : Subgroup G) ≤ Gv (v : G) := by
  let := hK
  intro hP
  have hv2 : orderOf (v : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian _ v.property)
    (fun he => nonsingular_ne_one D hv (Subtype.ext he))
  have hc := Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le P
    (H.source.simpleQTKE.evenCharacteristic P) (isTwoLocal_involution_centralizer hv2) hP)
  have hcomp := (H.nonsingular_canonical_component D v hv).1
  exact hcomp.not_isQuasisimple_of_characteristic_two hc
    (IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (Kv_le_Gv (v : G))).symm)

/-- The source index-four bound sharpens to two whenever the original K_v is quasisimple. -/
theorem SourceHypothesis.nonsingular_quasisimple_sylow_index_le_two
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) :
    (Tv T (v : G)).relIndex
      ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) ≤ 2 := by
  let A := Tv T (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hS : IsPGroup 2 S₀ := S.isPGroup'.map _
  have hb : A.relIndex S₀ ≤ 4 := by
    simpa only [hi] using Tv_relIndex_le T (v : G) S₀ hS hTS
  have hfour : A.relIndex S₀ ≠ 4 := by
    intro he
    have h1 := (A.subgroupOf S₀).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hTS).toEquiv] at h1
    change Nat.card A * A.relIndex S₀ = Nat.card S₀ at h1
    have h2 := (A.subgroupOf (T : Subgroup G)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ (T : Subgroup G) from inf_le_left)).toEquiv] at h2
    change Nat.card A * A.relIndex (T : Subgroup G) = Nat.card T at h2
    have hecard : Nat.card S₀ = Nat.card T := by rw [←h1,he,←h2]; exact congrArg (Nat.card A * ·) hi.symm
    obtain ⟨P,hSP⟩ := hS.exists_le_sylow
    have heq : S₀ = (P : Subgroup G) := eq_of_le_of_card_ge hSP (by
      rw [hecard,Nat.card_congr (P.equiv T).toEquiv])
    apply H.nonsingular_quasisimple_no_ambient_sylow D v hv hK P
    rw [←heq]
    exact map_subtype_le _
  have hthree : A.relIndex S₀ ≠ 3 := by
    intro he
    obtain ⟨n,hn⟩ := hS.exists_card_eq
    have hd : 3 ∣ 2 ^ n := hn ▸ (he ▸ A.relIndex_dvd_card S₀)
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  change A.relIndex S₀ ≤ 2
  omega

/-- The strict bound passes to the simultaneous normalizer of the literal local images under any surjective model map. -/
theorem SourceHypothesis.nonsingular_quasisimple_local_model_sylow_index_le_two
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    {F : Type*} [Group F] [Finite F]
    (f : Kv (v : G) →* F) (hf : Function.Surjective f) :
    let B := ((Lv L (v : G)).subgroupOf (Kv (v : G))).map f
    let W := ((Vv L V (v : G)).subgroupOf (Kv (v : G))).map f
    ∃ P : Sylow 2 F,
      (normalizer (B : Set F) ⊓ normalizer (W : Set F)).relIndex
        (P : Subgroup F) ≤ 2 := by
  let C := Kv (v : G)
  let B := (Lv L (v : G)).subgroupOf C
  let W := (Vv L V (v : G)).subgroupOf C
  let N := normalizer (B.map f : Set F) ⊓ normalizer (W.map f : Set F)
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hSi : (Tv T (v : G)).relIndex S₀ ≤ 2 := by
    exact H.nonsingular_quasisimple_sylow_index_le_two D v hv hK hi S hTS
  have hSyl : Chapter1.IsSylowIn 2 S₀ (Gv (v : G)) := ⟨S,rfl⟩
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (Kv_le_Gv (v : G)) (Kv_normalIn_Gv (v : G)).isSubnormal
  have hBC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L (v : G)
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  have hWC : Vv L V (v : G) ≤ C := (H.nonsingular_component_rank D v hv).1
  have hnB : Tv T (v : G) ≤ normalizer (Lv L (v : G) : Set G) :=
    (inf_le_inf H.chosen.sylow_normalizes_component le_rfl).trans
      (Mv_le_normalizer_Lv L (v : G))
  have hnW : Tv T (v : G) ≤ normalizer (Vv L V (v : G) : Set G) :=
    normalizes_Vv_of_normalizes _ _ (inf_le_left.trans hTV) hnB
  have hnBC : (Tv T (v : G)).subgroupOf C ≤ normalizer (B : Set C) := by
    rw [←subgroupOf_normalizer_eq hBC]
    exact comap_mono hnB
  have hnWC : (Tv T (v : G)).subgroupOf C ≤ normalizer (W : Set C) := by
    rw [←subgroupOf_normalizer_eq hWC]
    exact comap_mono hnW
  have hn : (Tv T (v : G)).subgroupOf C ≤ N.comap f := by
    apply map_le_iff_le_comap.mp
    exact le_inf ((map_mono hnBC).trans (le_normalizer_map f))
      ((map_mono hnWC).trans (le_normalizer_map f))
  refine ⟨P.mapSurjective hf,?_⟩
  change N.relIndex ((P : Subgroup C).map f) ≤ 2
  rw [←relIndex_comap]
  apply (relIndex_le_of_le_left hn index_ne_zero_of_finite).trans
  change ((Tv T (v : G)).comap C.subtype).relIndex (P : Subgroup C) ≤ 2
  rw [relIndex_comap,hP]
  exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hSi

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original T_v is normal in every selected Sylow of G_v containing it, in the quasisimple branch. -/
theorem SourceHypothesis.nonsingular_quasisimple_Tv_normal_in_sylow
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) :
    ((Tv T (v : G)).subgroupOf
      ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)).Normal := by
  have hb := H.nonsingular_quasisimple_sylow_index_le_two D v hv hK hi S hTS
  let A := (Tv T (v : G)).subgroupOf
    ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
  have hp : A.index ≠ 0 := index_ne_zero_of_finite
  have hi' : A.index = 1 ∨ A.index = 2 := by change A.index ≤ 2 at hb; omega
  exact hi'.elim A.normal_of_index_eq_one A.normal_of_index_eq_two

private theorem SourceHypothesis.nonsingular_hs_ru_no_sylow_normalizes_moved
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hmodel : Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model))
    (S : Sylow 2 ((Kv (v : G)) ⧸ center (Kv (v : G)))) :
    let C := Kv (v : G)
    let W := ((Vv L V (v : G)).subgroupOf C).map (QuotientGroup.mk' (center C))
    ¬ (S : Subgroup (C ⧸ center C)) ≤ normalizer (W : Set (C ⧸ center C)) := by
  let C := Kv (v : G)
  let q := QuotientGroup.mk' (center C)
  let B := ((Lv L (v : G)).subgroupOf C).map q
  let W := ((Vv L V (v : G)).subgroupOf C).map q
  obtain ⟨_,⟨eB⟩,_,hne,he,_,hn⟩ := H.nonsingular_centralQuotient_local_marking D v hv
  let : IsElementaryAbelian 2 W := he
  change ¬ (S : Subgroup (C ⧸ center C)) ≤ normalizer (W : Set (C ⧸ center C))
  intro hS
  rcases hmodel with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    have hN : ((S.mapSurjective (f := e.toMonoidHom) e.surjective) : Subgroup Sporadic.LeechRelated.HS.Carrier) ≤
        normalizer (W.map e.toMonoidHom : Set Sporadic.LeechRelated.HS.Carrier) :=
      (map_mono hS).trans (le_normalizer_map e.toMonoidHom)
    have hu := Sporadic.LeechRelated.HS.normal_elementary_card_le_eight
      (S.mapSurjective (f := e.toMonoidHom) e.surjective) (W.map e.toMonoidHom)
      (IsElementaryAbelian.map e.toMonoidHom) hN
    rw [card_map_of_injective e.injective] at hu
    have hl := H.nonsingular_centralQuotient_moved_card D v hv
    change 16 ≤ Nat.card W at hl
    exact (by decide : ¬ (16 : ℕ) ≤ 8) (hl.trans hu)
  · obtain ⟨e⟩ := hmodel
    let E := W.map e.toMonoidHom
    have hEne : E ≠ ⊥ := fun hh => hne ((map_eq_bot_iff_of_injective _ e.injective).mp hh)
    have h9 : 9 ∣ Nat.card B := by
      apply dvd_trans _ (card_quotient_dvd_card (pCore 2 B))
      rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      decide
    have hBE : B.map e.toMonoidHom ≤ normalizer (E : Set Rudvalis.Model) :=
      (map_mono hn).trans (le_normalizer_map e.toMonoidHom)
    have hN9 : 9 ∣ Nat.card (normalizer (E : Set Rudvalis.Model)) := by
      apply dvd_trans _ (card_dvd_of_le hBE)
      rwa [card_map_of_injective e.injective]
    have hN : ((S.mapSurjective (f := e.toMonoidHom) e.surjective) : Subgroup Rudvalis.Model) ≤
        normalizer (E : Set Rudvalis.Model) :=
      (map_mono hS).trans (le_normalizer_map e.toMonoidHom)
    exact Rudvalis.SylowOvergroups.not_nine_dvd_card_twoLocal
      (S.mapSurjective (f := e.toMonoidHom) e.surjective) _
      ⟨E,hEne,(IsElementaryAbelian.isPGroup 2 W).map e.toMonoidHom,rfl⟩ hN hN9

/-- In the HS and Ru rows both literal normalizers meet a quotient Sylow in index exactly two. -/
theorem SourceHypothesis.nonsingular_hs_ru_local_sylow_index_two
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hmodel : Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model)) :
    let C := Kv (v : G)
    let q := QuotientGroup.mk' (center C)
    let B := ((Lv L (v : G)).subgroupOf C).map q
    let W := ((Vv L V (v : G)).subgroupOf C).map q
    ∃ P : Sylow 2 (C ⧸ center C),
      (normalizer (B : Set (C ⧸ center C)) ⊓
        normalizer (W : Set (C ⧸ center C))).relIndex (P : Subgroup (C ⧸ center C)) = 2 ∧
      (normalizer (W : Set (C ⧸ center C))).relIndex (P : Subgroup (C ⧸ center C)) = 2 := by
  let C := Kv (v : G)
  let q := QuotientGroup.mk' (center C)
  let B := ((Lv L (v : G)).subgroupOf C).map q
  let W := ((Vv L V (v : G)).subgroupOf C).map q
  let N := normalizer (B : Set (C ⧸ center C)) ⊓ normalizer (W : Set (C ⧸ center C))
  let NW := normalizer (W : Set (C ⧸ center C))
  obtain ⟨P,hP⟩ := H.nonsingular_quasisimple_local_model_sylow_index_le_two
    D v hv hK hTV hi q (QuotientGroup.mk'_surjective _)
  have hNW : NW.relIndex (P : Subgroup (C ⧸ center C)) ≤
      N.relIndex (P : Subgroup (C ⧸ center C)) :=
    relIndex_le_of_le_left inf_le_right index_ne_zero_of_finite
  have hne : NW.relIndex (P : Subgroup (C ⧸ center C)) ≠ 1 := by
    intro he
    exact H.nonsingular_hs_ru_no_sylow_normalizes_moved D v hv hmodel P
      (relIndex_eq_one.mp he)
  have hp : NW.relIndex (P : Subgroup (C ⧸ center C)) ≠ 0 := index_ne_zero_of_finite
  change N.relIndex (P : Subgroup (C ⧸ center C)) ≤ 2 at hP
  refine ⟨P,?_,?_⟩
  · change N.relIndex (P : Subgroup (C ⧸ center C)) = 2
    omega
  · change NW.relIndex (P : Subgroup (C ⧸ center C)) = 2
    omega
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Apply the strict Sylow restrictions and exact HS/Ru indices at the original preferred escaping point, together with the genuine covering catalogue. -/
theorem SourceHypothesis.exists_preferred_nonsingular_quasisimple_strict_sylow
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ((Kv (w : G)).subgroupOf (Gv (w : G))).IsCComponent ∧
      IsQuasisimple (Star (Kv (w : G))) ∧ IsSimpleGroup (Star (Kv (w : G))) ∧
      (IsQuasisimple (Kv (w : G)) →
        NonsingularRemainingCoverModels (Kv (w : G)) ∧
        (∃ S : Sylow 2 (Gv (w : G)),
          let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
          Tv T (w : G) ≤ S₀ ∧ (Tv T (w : G)).relIndex S₀ ≤ 2 ∧
            ((Tv T (w : G)).subgroupOf S₀).Normal) ∧
        (let C := Kv (w : G)
         let q := QuotientGroup.mk' (center C)
         let B := ((Lv L (w : G)).subgroupOf C).map q
         let W := ((Vv L V (w : G)).subgroupOf C).map q
         ∃ P : Sylow 2 (C ⧸ center C),
           (normalizer (B : Set (C ⧸ center C)) ⊓
             normalizer (W : Set (C ⧸ center C))).relIndex (P : Subgroup (C ⧸ center C)) ≤ 2) ∧
        (Nonempty (((Kv (w : G)) ⧸ center (Kv (w : G))) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
            Nonempty (((Kv (w : G)) ⧸ center (Kv (w : G))) ≃* Rudvalis.Model) →
          let C := Kv (w : G)
          let q := QuotientGroup.mk' (center C)
          let B := ((Lv L (w : G)).subgroupOf C).map q
          let W := ((Vv L V (w : G)).subgroupOf C).map q
          ∃ P : Sylow 2 (C ⧸ center C),
            (normalizer (B : Set (C ⧸ center C)) ⊓
              normalizer (W : Set (C ⧸ center C))).relIndex (P : Subgroup (C ⧸ center C)) = 2 ∧
            (normalizer (W : Set (C ⧸ center C))).relIndex (P : Subgroup (C ⧸ center C)) = 2)) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,hmodels⟩ :=
    H.exists_preferred_nonsingular_marked_cover_models D hTV hTI v hv he
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,?_⟩
  intro hK
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (w : G)
  exact ⟨(hmodels hK).1,
    ⟨S,hTS,H.nonsingular_quasisimple_sylow_index_le_two D w hw hK hi S hTS,
      H.nonsingular_quasisimple_Tv_normal_in_sylow D w hw hK hi S hTS⟩,
    H.nonsingular_quasisimple_local_model_sylow_index_le_two D w hw hK hTV hi
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _),
    H.nonsingular_hs_ru_local_sylow_index_two D w hw hK hTV hi⟩
end CFSG.Quasithin.Chapter12.Section06
