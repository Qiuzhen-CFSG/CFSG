module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixEscapingSource
public import Theory.SpecificGroups.PSL3Four.CentralCover.TwoPlanes

/-!
# The actual second elementary plane in the escaping component

Final12.7.5 produces the literal component and its central four-cover.
The original U lies in a component Sylow of order256. The other full
root-plane preimage is an actual elementary subgroup of the original G,
with order64. Their intersection is the full Sylow center of order16;
the two planes generate the Sylow and contain all its elementary subgroups.
The Sylow lies in the original Lt because it normalizes U.

Source: Aschbacher--Smith12.7.7, printed p.841. This is original source
geometry; the full/even exclusion and the missing P,Y comparison are not
inputs or conclusions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original escaping component supplies an actual opposite plane
and the exact common Sylow geometry, without an extra model premise. -/
theorem original_tripleSix_escaping_opposite_plane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬ centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    ∃ S : Sylow 2 B, ∃ W : Subgroup G,
      let R := (S : Subgroup B).map B.subtype
      U≤R ∧ W≤R ∧ R≤Lt ∧ Nat.card R=256 ∧
      IsElementaryAbelian 2 W ∧ Nat.card W=64 ∧ W≠U ∧
      U⊔W=R ∧ U⊓W=centerIn R ∧ Nat.card (centerIn R)=16 ∧
      R≤normalizer (U : Set G) ⊓ normalizer (W : Set G) ∧
      (∀ A : Subgroup G, IsElementaryAbelian 2 A → A≤R → A≤U ∨ A≤W) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let Vt := tripleSixPoint D a t
  obtain ⟨hB,hcenter,hV,hn,he⟩ :=
    original_tripleSix_point_identification_at h structural D a t ht heven hout
  let := hn
  obtain ⟨e₀⟩ := he
  let e := (QuotientGroup.quotientMulEquivOfEq hV.symm).trans e₀
  have hLB : Lt≤B := le_conjugateSpanBy Lt H
  have hUL : U≤Lt := (tripleSixPointCentralizerResidual_commutator D a t ht heven).2
  have hUB : U≤B := hUL.trans hLB
  have hVt := tripleSixPoint_properties D a t ht
  have hVB : Vt≤B := hVt.2.1.trans hUB
  have hz : center B=Vt.subgroupOf B := by
    apply Subgroup.map_injective B.subtype_injective
    rw [map_subgroupOf_eq_of_le hVB,←centerIn_eq_map_center]
    exact hcenter
  let f := Matrix.PSL3Four.ElementaryParabolic.centerProjection e
  have hf : Function.Surjective f := Matrix.PSL3Four.ElementaryParabolic.centerProjection_surjective e
  have hk : f.ker=center B := Matrix.PSL3Four.ElementaryParabolic.centerProjection_ker e
  have hkc : Nat.card f.ker=4 := by
    rw [hk,hz,Nat.card_congr (subgroupOfEquivOfLe hVB).toEquiv]
    exact hVt.2.2.1
  let := D.elementary
  let Q := U.subgroupOf B
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.subgroupOf hUB
  have hQc : Nat.card Q=64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv]
    exact (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card
  have hkQ : f.ker≤Q := by rw [hk,hz]; exact subgroupOf_mono B hVt.2.1
  obtain ⟨S,W,hQS,hWS,hSc,hWe,hWc,hne,hgen,hint,hZc,hbound,hnorm⟩ :=
    Matrix.PSL3Four.four_cover_two_planes f hf (hk ▸ le_rfl) hkc Q hkQ hQc
  let R := (S : Subgroup B).map B.subtype
  let W' := W.map B.subtype
  have hQR : U≤R := by
    have hh := map_mono (f := B.subtype) hQS
    rwa [map_subgroupOf_eq_of_le hUB] at hh
  have hWR : W'≤R := map_mono hWS
  have hRnorm : R≤normalizer (U : Set G) ⊓ normalizer (W' : Set G) := by
    apply le_inf
    · have hh := (map_mono (f := B.subtype) (hnorm.trans inf_le_left)).trans
        (Q.le_normalizer_map B.subtype)
      rwa [map_subgroupOf_eq_of_le hUB] at hh
    · exact (map_mono (f := B.subtype) (hnorm.trans inf_le_right)).trans
        (W.le_normalizer_map B.subtype)
  have hRL : R≤Lt := by
    obtain ⟨hLN,_,_⟩ := tripleSixPointResidual_ordinary_block_core D a t ht heven hcenter e
    change Lt=(normalizer (Q : Set B)).map B.subtype at hLN
    rw [hLN]
    exact map_mono (hnorm.trans inf_le_left)
  have hRcenter : centerIn R=((center S).map (S : Subgroup B).subtype).map B.subtype := by
    rw [centerIn_eq_map_center]
    exact ((S : Subgroup B).map_embeddedCenter B.subtype B.subtype_injective).symm
  let := hWe
  refine ⟨S,W',hQR,hWR,hRL,?_,IsElementaryAbelian.map _,?_,?_,?_,?_,?_,hRnorm,?_⟩
  · exact (card_map_of_injective B.subtype_injective).trans hSc
  · exact (card_map_of_injective B.subtype_injective).trans hWc
  · intro heq
    apply hne
    apply Subgroup.map_injective B.subtype_injective
    rw [map_subgroupOf_eq_of_le hUB]
    exact heq
  · have hh := congrArg (Subgroup.map B.subtype) hgen
    simpa only [Q,Subgroup.map_sup,map_subgroupOf_eq_of_le hUB] using hh
  · have hh := congrArg (Subgroup.map B.subtype) hint
    rw [hRcenter]
    simpa only [Q,Subgroup.map_inf _ _ _ B.subtype_injective,map_subgroupOf_eq_of_le hUB] using hh
  · rw [hRcenter,card_map_of_injective B.subtype_injective,
      card_map_of_injective (S : Subgroup B).subtype_injective]
    exact hZc
  · intro A hA hAR
    let := hA
    have hAB : A≤B := hAR.trans (map_subtype_le _)
    let : IsElementaryAbelian 2 (A.subgroupOf B) := IsElementaryAbelian.subgroupOf hAB
    have hAS : A.subgroupOf B≤(S : Subgroup B) := by
      intro x hx
      obtain ⟨y,hy,he⟩ := hAR hx
      exact (Subtype.ext he : y=x) ▸ hy
    rcases hbound (A.subgroupOf B) inferInstance hAS with h | h
    · left
      intro x hx
      exact h (show (⟨x,hAB hx⟩ : B)∈A.subgroupOf B from hx)
    · right
      intro x hx
      exact ⟨⟨x,hAB hx⟩,h hx,rfl⟩

end CFSG.Quasithin.Chapter12.Section07
