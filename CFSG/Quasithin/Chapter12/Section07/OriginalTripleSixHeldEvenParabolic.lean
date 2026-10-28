module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldEvenPlanes
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldNoncentralPoint
public import Theory.SpecificGroups.PSL3Four.CentralCover.EmbeddedPlane
import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The actual opposite parabolic in the original even branch

The component's second elementary64 plane is placed in the original T.
Its full component normalizer is perfect, with exactly that two-core.
Every proper invariant subgroup lies in the original conjugated central
four-group. That four-group has no nontrivial two-central element, so
adjoining the original T makes the action on the second plane irreducible.

Source: Aschbacher--Smith12.7.7, printed p.841. This proves local geometry;
it does not assume or assert the omitted ambient Held identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal opposite parabolic and original Sylow generate an irreducible
normalizer of the second plane in the even branch. -/
theorem original_tripleSix_escaping_even_parabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G)≤normalizer (K : Set G))
    (hTK : (T : Subgroup G)≤K) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
    let B := conjugateSpanBy Lt H
    Nat.card T=512 ∧ ∃ k∈K, ∃ S : Sylow 2 B, ∃ W : Subgroup G,
      let Bk := B.map (MulAut.conj k).toMonoidHom
      let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
      let L := (normalizer (W.subgroupOf Bk : Set Bk)).map Bk.subtype
      U≤R ∧ W≤R ∧ R≤(T : Subgroup G) ∧ Nat.card R=256 ∧
      IsElementaryAbelian 2 W ∧ Nat.card W=64 ∧ W≠U ∧
      U⊔W=R ∧ U⊓W=centerIn R ∧ Nat.card (centerIn R)=16 ∧
      (T : Subgroup G)≤normalizer (R : Set G)⊓normalizer (W : Set G) ∧
      Group.IsPerfect L ∧ Nat.card L=3840 ∧ L.pCoreIn 2=W ∧ ⁅W,L⁆=W ∧
      centerIn L=(tripleSixPoint D a t).map (MulAut.conj k).toMonoidHom ∧
      Nat.card (centerIn L)=4 ∧ centerIn L⊓centerIn (T : Subgroup G)=⊥ ∧
      L≤normalizer (W : Set G) ∧
      (∀ A : Subgroup G, A≤W → L≤normalizer (A : Set G) → A≤centerIn L ∨ A=W) ∧
      (∀ A : Subgroup G, A≤W → L⊔(T : Subgroup G)≤normalizer (A : Set G) → A=⊥ ∨ A=W) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
  let B := conjugateSpanBy Lt H
  let Vt := tripleSixPoint D a t
  have hTc := (original_tripleSix_escaping_even_planes h structural D a t ht heven hout hTK).1
  obtain ⟨k,hk,S,W,hUR,hWR,hRT,_,hRc,hWe,hWc,hne,hgen,hint,hZc,_,hcover⟩ :=
    original_tripleSix_escaping_sylow_planes h structural D a t ht heven hout
  let c := MulAut.conj k
  let Bk := B.map c.toMonoidHom
  let R := ((S : Subgroup B).map B.subtype).map c.toMonoidHom
  have hRB : R≤Bk := map_mono (map_subtype_le _)
  have hWB : W≤Bk := hWR.trans hRB
  have hUc : Nat.card U=64 :=
    (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card
  have hidx : (R.subgroupOf (T : Subgroup G)).index=2 := by
    have hh := (R.subgroupOf (T : Subgroup G)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hRT).toEquiv,hRc,hTc] at hh
    omega
  have hRn : (R.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hidx
  have hTR : (T : Subgroup G)≤normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRT).mp hRn
  have hTU : (T : Subgroup G)≤normalizer (U : Set G) := hTK.trans D.normalizes
  have hTW : (T : Subgroup G)≤normalizer (W : Set G) :=
    normalizes_other_elementary_plane R U W (T : Subgroup G) hWR hWe
      (hUc.trans hWc.symm) hne hcover hTR hTU
  obtain ⟨hB,hcenter,hV,hn,he⟩ :=
    original_tripleSix_point_identification_at h structural D a t ht heven hout
  let := hn
  obtain ⟨e₀⟩ := he
  let e := (QuotientGroup.quotientMulEquivOfEq hV.symm).trans e₀
  let f := Matrix.PSL3Four.ElementaryParabolic.centerProjection e
  have hf : Function.Surjective f := Matrix.PSL3Four.ElementaryParabolic.centerProjection_surjective e
  have hfk : f.ker=center B := Matrix.PSL3Four.ElementaryParabolic.centerProjection_ker e
  let : Group.IsPerfect Lt := tripleSixPointCentralizerResidual_perfect D a t ht heven
  let : Group.IsPerfect B := conjugateSpanBy_isPerfect Lt H
  let eb := B.equivMapOfInjective c.toMonoidHom c.injective
  let : Group.IsPerfect Bk := Group.IsPerfect.ofSurjective (f := eb.toMonoidHom) eb.surjective
  let fk := f.comp eb.symm.toMonoidHom
  have hfkSurj : Function.Surjective fk := hf.comp eb.symm.surjective
  have hfkKer : fk.ker=center Bk := by
    ext x
    change f (eb.symm x)=1 ↔ x∈center Bk
    rw [←MonoidHom.mem_ker,hfk]
    constructor
    · intro hx
      have hh := (Subgroup.centerCongr eb ⟨eb.symm x,hx⟩).property
      change eb (eb.symm x)∈center Bk at hh
      simpa only [MulEquiv.apply_symm_apply] using hh
    · intro hx
      exact (Subgroup.centerCongr eb.symm ⟨x,hx⟩).property
  have hcenterK : centerIn Bk=Vt.map c.toMonoidHom := by
    rw [centerIn_eq_map_center,←B.map_embeddedCenter c.toMonoidHom c.injective,
      ←centerIn_eq_map_center,hcenter]
  have hU : U.map c.toMonoidHom=U := mem_normalizer_iff_map_conj_eq.mp (D.normalizes hk)
  have hCU : centerIn Bk≤U := by
    rw [hcenterK,←hU]
    exact map_mono (tripleSixPoint_properties D a t ht).2.1
  have hCR : centerIn Bk≤centerIn R := by
    intro x hx
    exact ⟨hUR (hCU hx),fun y hy => hx.2 y (hRB hy)⟩
  have hCW : centerIn Bk≤W := by
    rw [←hint] at hCR
    exact hCR.trans inf_le_right
  have hCc : Nat.card (centerIn Bk)=4 := by
    rw [hcenterK,card_map_of_injective c.injective]
    exact (tripleSixPoint_properties D a t ht).2.2.1
  have hfkc : Nat.card fk.ker=4 := by
    rw [hfkKer]
    have hh := hCc
    rw [centerIn_eq_map_center,card_map_of_injective Bk.subtype_injective] at hh
    exact hh
  have hCZ : centerIn Bk⊓centerIn (T : Subgroup G)=⊥ := by
    let T₀ := T.mapSurjective (f := c.symm.toMonoidHom) c.symm.surjective
    have hz := original_tripleSix_held_point_inf_sylow_center_eq_bot h D a t ht hB T₀
    apply bot_unique
    intro x hx
    obtain ⟨v,hv,hvx⟩ := hcenterK ▸ hx.1
    have hvz : v∈centerIn (T₀ : Subgroup G) := by
      have hh : c.symm x∈(centerIn (T : Subgroup G)).map c.symm.toMonoidHom :=
        mem_map_of_mem c.symm.toMonoidHom hx.2
      have hm : (centerIn (T : Subgroup G)).map c.symm.toMonoidHom=
          centerIn (T₀ : Subgroup G) := by
        rw [centerIn_eq_map_center,centerIn_eq_map_center]
        exact (T : Subgroup G).map_embeddedCenter c.symm.toMonoidHom c.symm.injective
      rw [hm,←hvx] at hh
      change c.symm (c v)∈centerIn (T₀ : Subgroup G) at hh
      rw [c.symm_apply_apply] at hh
      exact hh
    have hv1 := mem_bot.mp (hz ▸ (show v∈Vt⊓centerIn (T₀ : Subgroup G) from ⟨hv,hvz⟩))
    rw [←hvx,hv1,map_one]
    exact one_mem _
  let := hWe
  obtain ⟨hLp,hLc,hLcore,hLcomm,hLC,hLW,hInv⟩ :=
    Matrix.PSL3Four.FullPlaneNormalizer.embedded_plane Bk W fk hfkSurj hfkKer hfkc hWB hCW hWc
  let L := (normalizer (W.subgroupOf Bk : Set Bk)).map Bk.subtype
  have hInv' : ∀ A : Subgroup G, A≤W → L≤normalizer (A : Set G) → A≤centerIn L ∨ A=W := by
    intro A hAW hLA
    rw [hLC]
    exact hInv A hAW hLA
  have hirr : ∀ A : Subgroup G, A≤W → L⊔(T : Subgroup G)≤normalizer (A : Set G) → A=⊥ ∨ A=W := by
    intro A hAW hNA
    rcases hInv' A hAW (le_sup_left.trans hNA) with hAC | heq
    · left
      by_contra hneA
      apply inf_centerIn_ne_bot T.isPGroup' hneA (hAW.trans (hWR.trans hRT)) (le_sup_right.trans hNA)
      apply bot_unique
      rw [←hLC] at hCZ
      exact (inf_le_inf_right _ hAC).trans_eq hCZ
    · exact Or.inr heq
  refine ⟨hTc,k,hk,S,W,hUR,hWR,hRT,hRc,hWe,hWc,hne,hgen,hint,hZc,
    le_inf hTR hTW,hLp,hLc,hLcore,hLcomm,?_,?_,?_,hLW,hInv',hirr⟩
  · exact hLC.trans hcenterK
  · rwa [hLC]
  · rwa [hLC]

end CFSG.Quasithin.Chapter12.Section07
