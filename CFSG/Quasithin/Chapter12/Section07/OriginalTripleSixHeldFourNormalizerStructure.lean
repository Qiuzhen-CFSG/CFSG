module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldFourNormalizerIndex
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldFourNormalizerStructureSextet
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldAlignedLocals

/-! The actual original exceptional-four normalizer has a subgroup of order
23040, obtained by transporting its six-point stabilizer. Its projective
residual therefore has index exactly two. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open TransvectionFive TransvectionFive.UniquenessLinear
open TransvectionFive.UniquenessMathieu.SourceNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem plane_four_normalizer_dvd {z : G} (F : MarkedCentralizer z)
    (hc : (F.fusion F.plane).ncard = 45) (V : Subgroup G) (g : G)
    (i : Fin 6) (hi : V.map (MulAut.conj g).toMonoidHom = planeFour F i) :
    23040 ∣ Nat.card (normalizer (V : Set G)) := by
  let N := normalizer (planeFour F i : Set G)
  let M := planeNormalizer F
  let L := N.subgroupOf M
  have hL : Nat.card (L.map M.subtype) = 23040 :=
    (card_map_of_injective M.subtype_injective).trans (plane_four_normalizer_card F hc i)
  have hLN : L.map M.subtype ≤ N := by
    rintro x ⟨n,hn,rfl⟩
    exact hn
  have hd := card_dvd_of_le hLN
  rw [hL] at hd
  have he : (normalizer (V : Set G)).map (MulAut.conj g).toMonoidHom = N := by
    rw [map_normalizer_eq_of_bijective V (MulAut.conj g).bijective,hi]
  rw [←he,card_map_of_injective (MulAut.conj g).injective] at hd
  exact hd

theorem original_tripleSix_escaping_four_normalizer_card_divisor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    23040 ∣ Nat.card (normalizer (tripleSixPoint D a t : Set G)) := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing,d,hd,hdf,hfree,c,hmark,hwhole,hrecognition,
    hcoreY,hZQ,hQP,hCN,hself,hiff,hYcard,himage,hQP',hCY,hfusion,V,hVc,hVi,hVs,hVf,A,hA,hZA,hAP,hAc,hYA,hselfA,F,hAF,hp45,ht45,hpattern,r,halign⟩ :=
    original_tripleSix_escaping_aligned_locals h structural D a t ht heven hout
  rcases halign with ⟨_,_,i,hi⟩ | ⟨_,_,i,hi⟩
  · exact plane_four_normalizer_dvd F hp45 _ r i hi
  · apply plane_four_normalizer_dvd (oppositeMarking F) _ _ r i hi
    simpa only [MarkedCentralizer.fusion,oppositeMarking_plane] using ht45

theorem original_tripleSix_escaping_four_normalizer_index_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    let W := B ⊔ tripleSixScalarResidual K
    let N := normalizer (B : Set G)
    W.relIndex N = 2 ∧ Nat.card N = 483840 := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let W := B ⊔ tripleSixScalarResidual K
  let N := normalizer (B : Set G)
  obtain ⟨hWc,hi⟩ := original_tripleSix_escaping_four_normalizer_index_dvd_two
    h structural D a t ht heven hout
  obtain ⟨_,hNV,_,_,_,_,_,_,_,hWN,_⟩ :=
    original_tripleSix_escaping_projective_geometry h structural D a t ht heven hout
  have hd := original_tripleSix_escaping_four_normalizer_card_divisor
    h structural D a t ht heven hout
  rw [←hNV] at hd
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) W N bot_le hWN
  rw [relIndex_bot_left,relIndex_bot_left,hWc] at hm
  have hi' : W.relIndex N = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hi with h1 | h2
    · rw [h1,mul_one] at hm
      rw [←hm] at hd
      norm_num at hd
    · exact h2
  refine ⟨hi',?_⟩
  rw [hi'] at hm
  exact hm.symm

/-- The component has its exact central-cover order and index six in its
actual ambient normalizer. No splitting or quotient action is inferred from
these cardinalities. -/
theorem original_tripleSix_escaping_component_normalizer_index_six
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    Nat.card B = 80640 ∧ B.relIndex (normalizer (B : Set G)) = 6 := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  obtain ⟨_,hcenter,hV,hn,⟨e₀⟩⟩ := original_tripleSix_point_identification_at
    h structural D a t ht heven hout
  let := hn
  let e := (QuotientGroup.quotientMulEquivOfEq hV.symm).trans e₀
  have hZc : Nat.card (center B) = 4 := by
    have hc : Nat.card (centerIn B) = 4 := hcenter.symm ▸
      (tripleSixPoint_properties D a t ht).2.2.1
    rw [centerIn_eq_map_center,card_map_of_injective B.subtype_injective] at hc
    exact hc
  have hBc : Nat.card B = 80640 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center B),
      Nat.card_congr e.toEquiv,Matrix.PSL3Four.card_PSL,hZc]
  have hNc := (original_tripleSix_escaping_four_normalizer_index_two
    h structural D a t ht heven hout).2
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) B
    (normalizer (B : Set G)) bot_le B.le_normalizer
  rw [relIndex_bot_left,relIndex_bot_left,hBc,hNc] at hm
  exact ⟨hBc,by change B.relIndex (normalizer (B : Set G)) = 6; omega⟩

end CFSG.Quasithin.Chapter12.Section07
