module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeKernelOverlap
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldFullAffine
import Theory.Representation.HexacodeAction.AffinePlaneNormalizer
import Theory.GroupTheory.TwoElementaryPlanes

/-!
# Full original Sylow normalization of the opposite component plane

The actual component Sylow is the join of U and its opposite elementary
plane W. Its image in the full affine model is the preimage of the unique
hexacode best offender in the containing two-group. Thus the entire original
T normalizes this Sylow, and preservation of the original two planes makes T
normalize W as well. The supplied dihedral quotient and its whole kernel are
retained unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem original_plane_join_normalized
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G))
    (R W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWR : W≤R) (hRT : R≤(T : Subgroup G)) (hW : Nat.card W=64)
    (hgen : U⊔W=R) (hI : Nat.card (U⊓W : Subgroup G)=16) :
    (T : Subgroup G)≤normalizer (R : Set G) := by
  let M := normalizer (K : Set G)
  let V := Multiplicative hexacode
  let A := V ⋊[hexAffineAction] HexAutomorphisms
  obtain ⟨_,_,_,_,E,hU,_,_⟩ :=
    original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout
  have hTM : (T : Subgroup G)≤M := D.sylow_normalizes_component
  have hUM : U≤M := D.le_component.trans K.le_normalizer
  have hRM : R≤M := hRT.trans hTM
  have hWM : W≤M := hWR.trans hRM
  let S₀ := ((T : Subgroup G).subgroupOf M).map E.toMonoidHom
  let W₀ := (W.subgroupOf M).map E.toMonoidHom
  let R₀ := (R.subgroupOf M).map E.toMonoidHom
  let ι : V→*A := SemidirectProduct.inl
  have hUmap : (U.subgroupOf M).map E.toMonoidHom=ι.range := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      exact ⟨tripleSixPointCoordinates D a (⟨u,hu⟩:U),(hU ⟨u,hu⟩).symm⟩
    · rintro x ⟨v,rfl⟩
      let u := (tripleSixPointCoordinates D a).symm v
      refine ⟨inclusion hUM u,u.property,?_⟩
      change E (inclusion hUM u)=ι v
      rw [hU]
      exact congrArg ι ((tripleSixPointCoordinates D a).apply_symm_apply v)
  have hgen₀ : ι.range⊔W₀=R₀ := by
    rw [←hUmap,←Subgroup.map_sup,←subgroupOf_sup hUM hWM,hgen]
  have hI₀ : Nat.card (W₀⊓ι.range : Subgroup A)=16 := by
    rw [←hUmap,←Subgroup.map_inf _ _ _ E.injective,card_map_of_injective E.injective]
    change Nat.card ((W⊓U).subgroupOf M)=16
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hWM)).toEquiv,inf_comm]
    exact hI
  let : IsElementaryAbelian 2 (W.subgroupOf M) := IsElementaryAbelian.subgroupOf hWM
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.map _
  have hW₀ : Nat.card W₀=64 := by
    rw [card_map_of_injective E.injective,Nat.card_congr (subgroupOfEquivOfLe hWM).toEquiv]
    exact hW
  have hS₀ : IsPGroup 2 S₀ := (T.isPGroup'.comap_of_injective M.subtype M.subtype_injective).map E.toMonoidHom
  have hnorm := Hexacode.affine_normalizes_plane_join S₀ W₀ hS₀
    (map_mono (subgroupOf_mono M (hWR.trans hRT))) hW₀ hI₀
  rw [hgen₀] at hnorm
  have hback := (map_le_iff_le_comap.mp hnorm).trans (le_normalizer_comap E.toMonoidHom)
  rw [comap_map_eq_self_of_injective E.injective] at hback
  rw [←subgroupOf_normalizer_eq hRM] at hback
  intro x hx
  exact hback (show (⟨x,hTM hx⟩:M)∈(T : Subgroup G).subgroupOf M from hx)

/-- The original opposite plane and component Sylow are normalized by all of
T, with the same marked dihedral kernel and both distinct intersections. -/
theorem original_tripleSix_escaping_opposite_plane_normalizer
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
      (T : Subgroup G)≤normalizer (R : Set G)⊓normalizer (W : Set G) ∧
      (∀ A : Subgroup G, IsElementaryAbelian 2 A → A≤R → A≤U ∨ A≤W) ∧
      Nat.card (W⊓P : Subgroup G)=16 ∧ centerIn P≤W ∧
      (U⊓P : Subgroup G)≠W⊓P := by
  obtain ⟨k,hk,S,W,hUR,hWR,hRT,hRK,hRc,hWe,hWc,hne,hgen,hint,hZc,_,hcover,hIc,hZW,hneq⟩ :=
    original_tripleSix_escaping_opposite_kernel_overlap h structural D a t ht heven hout π hP
  let H := centralizer ({(t:G)} : Set G)
  let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
  let B := conjugateSpanBy Lt H
  let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
  let := hWe
  have hI : Nat.card (U⊓W : Subgroup G)=16 := by rwa [hint]
  have hTR := original_plane_join_normalized h structural D a t ht heven hout
    R W hWR hRT hWc hgen hI
  have hTU : (T : Subgroup G)≤normalizer (U : Set G) := by
    rw [(original_tripleSix_escaping_core h structural D a t ht heven hout).2.2.2.1]
    exact D.sylow_normalizes_component
  have hUc : Nat.card U=64 :=
    (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans hexacode_card
  have hTW := normalizes_other_elementary_plane R U W (T : Subgroup G) hWR hWe
    (hUc.trans hWc.symm) hne hcover hTR hTU
  exact ⟨k,hk,S,W,hUR,hWR,hRT,hRK,hRc,hWe,hWc,hne,hgen,hint,hZc,
    le_inf hTR hTW,hcover,hIc,hZW,hneq⟩

end CFSG.Quasithin.Chapter12.Section07
