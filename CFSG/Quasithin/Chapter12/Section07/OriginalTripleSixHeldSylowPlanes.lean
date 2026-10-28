module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositePlane
import Theory.GroupTheory.PGroup.NormalizedSylowConjugation

/-!
# The original pair of elementary planes inside the given Sylow subgroup

Conjugacy by an actual element of K moves the component Sylow into the
original T while retaining the original U. The second plane and all its
intersection and coverage properties move by that same conjugation.
No full affine actor or external Sylow comparison is assumed.

Source: Aschbacher--Smith12.7.7, printed p.841.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual opposite plane can be placed in the given original T by
K-conjugation, preserving U and the entire component-Sylow marking. -/
theorem original_tripleSix_escaping_sylow_planes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬ centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    ∃ k ∈ K, ∃ S : Sylow 2 B, ∃ W : Subgroup G,
      let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
      U≤R ∧ W≤R ∧ R≤(T : Subgroup G) ∧ R≤K ∧ Nat.card R=256 ∧
      IsElementaryAbelian 2 W ∧ Nat.card W=64 ∧ W≠U ∧
      U⊔W=R ∧ U⊓W=centerIn R ∧ Nat.card (centerIn R)=16 ∧
      R≤normalizer (U : Set G) ⊓ normalizer (W : Set G) ∧
      (∀ A : Subgroup G, IsElementaryAbelian 2 A → A≤R → A≤U ∨ A≤W) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  obtain ⟨S,W,hUR,hWR,hRL,hRc,hWe,hWc,hne,hgen,hint,hZc,hnorm,hbound⟩ :=
    original_tripleSix_escaping_opposite_plane h structural D a t ht heven hout
  let R := (S : Subgroup B).map B.subtype
  have hRK : R≤K := hRL.trans ((map_subtype_le _).trans inf_le_left)
  have hp : IsPGroup 2 R := S.isPGroup'.map B.subtype
  obtain ⟨k,hk,hRT⟩ := IsPGroup.exists_conj_le_sylow_of_normalized
    T K R D.sylow_normalizes_component hp hRK
  let c := MulAut.conj k
  have hU : U.map c.toMonoidHom=U := mem_normalizer_iff_map_conj_eq.mp (D.normalizes hk)
  have hK : K.map c.toMonoidHom=K := mem_normalizer_iff_map_conj_eq.mp (K.le_normalizer hk)
  let R' := R.map c.toMonoidHom
  let W' := W.map c.toMonoidHom
  have hcenter : (centerIn R).map c.toMonoidHom=centerIn R' := by
    rw [centerIn_eq_map_center,centerIn_eq_map_center]
    exact R.map_embeddedCenter c.toMonoidHom c.injective
  have hnorm' : R'≤normalizer (U : Set G) ⊓ normalizer (W' : Set G) := by
    apply le_inf
    · have hh := (map_mono (f := c.toMonoidHom) (hnorm.trans inf_le_left)).trans
        (U.le_normalizer_map c.toMonoidHom)
      rwa [hU] at hh
    · exact (map_mono (f := c.toMonoidHom) (hnorm.trans inf_le_right)).trans
        (W.le_normalizer_map c.toMonoidHom)
  let := hWe
  refine ⟨k,hk,S,W',?_,map_mono hWR,hRT,?_,?_,IsElementaryAbelian.map _,?_,?_,?_,?_,?_,hnorm',?_⟩
  · have hh := map_mono (f := c.toMonoidHom) hUR
    rwa [hU] at hh
  · exact (map_mono hRK).trans_eq hK
  · exact (card_map_of_injective c.injective).trans hRc
  · exact (card_map_of_injective c.injective).trans hWc
  · intro hh
    apply hne
    exact Subgroup.map_injective c.injective (hh.trans hU.symm)
  · have hh := congrArg (Subgroup.map c.toMonoidHom) hgen
    simpa only [Subgroup.map_sup,hU] using hh
  · have hh := congrArg (Subgroup.map c.toMonoidHom) hint
    change (U⊓W).map c.toMonoidHom=(centerIn R).map c.toMonoidHom at hh
    rw [Subgroup.map_inf U W c.toMonoidHom c.injective,hU,hcenter] at hh
    exact hh
  · rw [←hcenter,card_map_of_injective c.injective]
    exact hZc
  · intro A hA hAR
    let A₀ := A.map c.symm.toMonoidHom
    let := hA
    have hAe : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.map _
    have hA₀R : A₀≤R := by
      change A≤R' at hAR
      have hh := map_mono (f := c.symm.toMonoidHom) hAR
      change A₀≤(R.map c.toMonoidHom).map c.symm.toMonoidHom at hh
      have hi : c.symm.toMonoidHom.comp c.toMonoidHom=MonoidHom.id G := by
        ext x; exact c.symm_apply_apply x
      rwa [Subgroup.map_map,hi,Subgroup.map_id] at hh
    have hAback : A₀.map c.toMonoidHom=A := by
      change (A.map c.symm.toMonoidHom).map c.toMonoidHom=A
      have hi : c.toMonoidHom.comp c.symm.toMonoidHom=MonoidHom.id G := by
        ext x; exact c.apply_symm_apply x
      rw [Subgroup.map_map,hi,Subgroup.map_id]
    rcases hbound A₀ hAe hA₀R with ha | ha
    · left
      have hh := map_mono (f := c.toMonoidHom) ha
      rwa [hAback,hU] at hh
    · right
      have hh := map_mono (f := c.toMonoidHom) ha
      rwa [hAback] at hh

end CFSG.Quasithin.Chapter12.Section07
