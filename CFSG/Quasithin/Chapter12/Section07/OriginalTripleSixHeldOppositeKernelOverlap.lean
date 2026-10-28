module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldSylowPlanes
public import Theory.GroupTheory.ExtraspecialDihedralPlaneSeparation
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# The opposite original plane meets the same marked kernel differently

The source component supplies W inside the original T. For any retained
full dihedral quotient with extraspecial kernel128, W meets that kernel
in a sixteen containing its center. This sixteen differs from U's sixteen.
The quotient is an explicit parameter so later source choices use the same
P and cannot switch to an unrelated existential witness.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

public theorem original_tripleSix_escaping_opposite_kernel_overlap
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G))
    (π : T→*DihedralGroup 4) [IsExtraspecial 2 π.ker] (hP : Nat.card π.ker=128) :
    let P := π.ker.map (T : Subgroup G).subtype
    let H := centralizer ({(t:G)} : Set G)
    let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
    let B := conjugateSpanBy Lt H
    ∃ k∈K, ∃ S : Sylow 2 B, ∃ W : Subgroup G,
      let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
      U≤R ∧ W≤R ∧ R≤(T : Subgroup G) ∧ R≤K ∧ Nat.card R=256 ∧
      IsElementaryAbelian 2 W ∧ Nat.card W=64 ∧ W≠U ∧
      U⊔W=R ∧ U⊓W=centerIn R ∧ Nat.card (centerIn R)=16 ∧
      R≤normalizer (U : Set G)⊓normalizer (W : Set G) ∧
      (∀ A : Subgroup G, IsElementaryAbelian 2 A → A≤R → A≤U ∨ A≤W) ∧
      Nat.card (W⊓P : Subgroup G)=16 ∧ centerIn P≤W ∧
      (U⊓P : Subgroup G)≠W⊓P := by
  obtain ⟨k,hk,S,W,hUR,hWR,hRT,hRK,hRc,hWe,hWc,hne,hgen,hint,hZc,hnorm,hbound⟩ :=
    original_tripleSix_escaping_sylow_planes h structural D a t ht heven hout
  let P := π.ker.map (T : Subgroup G).subtype
  have hWT : W≤(T : Subgroup G) := hWR.trans hRT
  have hjoin : Nat.card (U⊔W : Subgroup G)=256 := hgen ▸ hRc
  let := D.elementary
  let := hWe
  let U₀ := U.subgroupOf T
  let W₀ := W.subgroupOf T
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf D.le_sylow
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.subgroupOf hWT
  have hUc : Nat.card U₀=64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe D.le_sylow).toEquiv]
    exact (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card
  have hW₀c : Nat.card W₀=64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWT).toEquiv).trans hWc
  have hmap (A : Subgroup G) (hAT : A≤(T : Subgroup G)) :
      (A.subgroupOf T⊓π.ker : Subgroup T).map (T : Subgroup G).subtype=A⊓P := by
    rw [Subgroup.map_inf _ _ _ (T : Subgroup G).subtype_injective,map_subgroupOf_eq_of_le hAT]
  have hjmap : (U₀⊔W₀).map (T : Subgroup G).subtype=U⊔W := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le D.le_sylow,map_subgroupOf_eq_of_le hWT]
  have hjc : Nat.card (U₀⊔W₀ : Subgroup T)=256 := by
    rw [←card_map_of_injective (T : Subgroup G).subtype_injective,hjmap,hjoin]
  obtain ⟨hI,_,hZ,_⟩ := extraspecial_dihedral_elementary_overlap π hP W₀ hW₀c
  have hIc : Nat.card (W⊓P : Subgroup G)=16 := by
    rw [←hmap W hWT,card_map_of_injective (T : Subgroup G).subtype_injective]
    exact hI
  have hZW : centerIn P≤W := by
    rw [centerIn_eq_map_center,←map_embeddedCenter π.ker (T : Subgroup G).subtype
      (T : Subgroup G).subtype_injective]
    exact (map_mono hZ).trans_eq (map_subgroupOf_eq_of_le hWT)
  refine ⟨k,hk,S,W,hUR,hWR,hRT,hRK,hRc,hWe,hWc,hne,hgen,hint,hZc,hnorm,hbound,hIc,hZW,?_⟩
  intro he
  apply extraspecial_dihedral_plane_intersections_ne π hP U₀ W₀ hUc hjc
  apply Subgroup.map_injective (T : Subgroup G).subtype_injective
  exact (hmap U D.le_sylow).trans (he.trans (hmap W hWT).symm)

end CFSG.Quasithin.Chapter12.Section07
