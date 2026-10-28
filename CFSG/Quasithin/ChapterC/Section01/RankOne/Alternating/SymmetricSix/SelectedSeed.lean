module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SelectedMovement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.EmbeddedSeedAlternative
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Marking
public import Stellmacher.BaumannMap
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.QuotientCubic

/-!
# Keeping the original Baumann group in the selected local seed

The injective embedding of the cubic preimage carries its Baumann subgroup
onto the original Baum(R). Precomposition supplies the literal C.1.18
marking. Adjoining this two-subgroup leaves the same two-residual, so its
image is the previously selected cubic seed. The cubic image is noncentral
in the component's actual two-core quotient.

Source: Aschbacher–Smith C.1.21 and C.1.24(c), printed pp.128–131.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
open GlaubermanNiles
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem baumann_map (H : Type*) [Group H] (f : H →* G) (hf : Function.Injective f)
    (R : Subgroup H) : (ChapterB.baumann R).map f=ChapterB.baumann (R.map f) :=
  baumann_map_injective f hf R

theorem baumann_intrinsic_fixed (R : Subgroup G) : IsBaumannFixed (ChapterB.baumann R) := by
  let S := ChapterB.baumann R
  change ChapterB.baumann (⊤ : Subgroup S)=⊤
  apply (Subgroup.map_injective S.subtype_injective)
  rw [baumann_map _ _ S.subtype_injective,←MonoidHom.range_eq_map,range_subtype]
  exact (ChapterB.lemma_B_2_3_4 R S le_rfl inf_le_left).symm

omit [Finite G] in
theorem selected_baumann_map (R : Subgroup G) (M : Subgroup (G ⧸ pCore 2 G)) :
    (ChapterB.baumann (R.subgroupOf (selectedGroup R M))).map (selectedGroup R M).subtype=
      ChapterB.baumann R := by
  rw [baumann_map _ _ (selectedGroup R M).subtype_injective,
    map_subgroupOf_eq_of_le (le_selectedGroup R M)]

theorem selected_local_residual_map (R : Subgroup G) (hpR : IsPGroup 2 R)
    (M : Subgroup (G ⧸ pCore 2 G)) :
    let H := selectedGroup R M
    let S := ChapterB.baumann (R.subgroupOf H)
    let K := pResidual 2 H ⊔ S
    (pResidual 2 K).map (H.subtype.comp K.subtype)=(pResidual 2 H).map H.subtype := by
  dsimp only
  let H := selectedGroup R M
  let S := ChapterB.baumann (R.subgroupOf H)
  let K := pResidual 2 H ⊔ S
  let C := (pResidual 2 H).subgroupOf K
  let D := S.subgroupOf K
  have hc : IsPPerfect 2 C := (isPPerfect_pResidual 2).of_surjective
    (subgroupOfEquivOfLe (show pResidual 2 H ≤ K from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show pResidual 2 H ≤ K from le_sup_left)).symm.surjective
  have hd : IsPGroup 2 D := (hpR.comap_subtype.to_le
    (show S ≤ R.subgroupOf H from inf_le_left)).comap_subtype
  have hgen : C ⊔ D=⊤ := by
    rw [←subgroupOf_sup (show pResidual 2 H ≤ K from le_sup_left)
      (show S ≤ K from le_sup_right),subgroupOf_self]
  have he := pResidual_eq_of_isPPerfect_sup C D hc hd hgen
  change (pResidual 2 K).map (H.subtype.comp K.subtype)=_
  rw [←map_map,he,map_subgroupOf_eq_of_le (show pResidual 2 H ≤ K from le_sup_left)]

omit [Finite G] in
theorem exists_selected_marking (R : Subgroup G) (M : Subgroup (G ⧸ pCore 2 G)) :
    let H := selectedGroup R M
    let B := ChapterB.baumann (R.subgroupOf H)
    let K := pResidual 2 H ⊔ B
    ∃ e : ChapterB.baumann R ≃* B,
      (H.subtype.comp K.subtype).comp ((inclusion (show B≤K from le_sup_right)).comp e.toMonoidHom)=
        (ChapterB.baumann R).subtype := by
  dsimp only
  let H := selectedGroup R M
  let B := ChapterB.baumann (R.subgroupOf H)
  let S := ChapterB.baumann R
  have hm : B.map H.subtype=S := selected_baumann_map R M
  let f : B →* S := (H.subtype.comp B.subtype).codRestrict S (fun x => hm ▸ mem_map_of_mem _ x.property)
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : S => (z : G)) he
    · intro s
      have hs : (s:G)∈B.map H.subtype := by rw [hm];exact s.property
      obtain ⟨x,hx,he⟩ := hs
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let E := MulEquiv.ofBijective f hf
  refine ⟨E.symm,?_⟩
  ext s
  exact congrArg (fun z : S => (z:G)) (E.apply_symm_apply s)
theorem baumann_ne_bot
    (Q : Subgroup G)
    (hQp : IsPGroup 2 Q) (hQne : Q ≠ ⊥) :
    Q ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) ≠ ⊥ := by
  let _ : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  have hZnontrivial : Nontrivial (Subgroup.center Q) := hQp.center_nontrivial
  have hZne : Subgroup.center Q ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp hZnontrivial
  have hJQ : elementaryAbelianMaxJ Q ≤ Q :=
    sSup_le fun _ hA ↦ hA.1
  have hWQ : omegaOneCenterAmbient (elementaryAbelianMaxJ Q) ≤ Q :=
    (Subgroup.map_subtype_le _).trans hJQ
  have hZB : (Subgroup.center Q).map Q.subtype ≤
      Q ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) := by
    intro z hz
    obtain ⟨zQ, hzQ, rfl⟩ := hz
    refine ⟨zQ.property, ?_⟩
    change (zQ : G) ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzQ) ⟨w, hWQ hw⟩)
  intro hbot
  have hZmap : (Subgroup.center Q).map Q.subtype = ⊥ :=
    le_bot_iff.mp (hZB.trans_eq hbot)
  exact hZne ((Subgroup.map_eq_bot_iff_of_injective
    (Subgroup.center Q) Q.subtype_injective).mp hZmap)

open Theory.SpecificGroups.SymmetricSix.TranspositionCubic Equiv

theorem cubic_not_central_in_component (L Y : Subgroup G) (hL : L.IsSubnormal)
    (hYL : Y ≤ L) (q : G →* Sym) (hQ : pCore 2 G ≤ q.ker)
    (hLq : L.map q=alternatingGroup (Fin 6)) (c : Sym)
    (hc : orderOf c=3) (hY : Y.map q=zpowers c) :
    ¬(Y.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L) := by
  have hk : pCore 2 L ≤ (q.comp L.subtype).ker := by
    rw [←hL.pCore_subgroupOf 2]
    intro x hx
    exact hQ hx
  let f := QuotientGroup.lift (pCore 2 L) (q.comp L.subtype) hk
  have hcY : c∈Y.map q := by rw [hY];exact mem_zpowers c
  obtain ⟨y,hy,hyc⟩ := hcY
  let z : L := ⟨y,hYL hy⟩
  have hca : c∈alternatingGroup (Fin 6) := by
    rw [←hLq];exact ⟨y,hYL hy,hyc⟩
  intro hcent
  have hz := hcent (mem_map_of_mem (QuotientGroup.mk' (pCore 2 L)) (show z∈Y.subgroupOf L from hy))
  have hcc : (⟨c,hca⟩ : alternatingGroup (Fin 6))∈center (alternatingGroup (Fin 6)) := by
    rw [mem_center_iff]
    intro a
    have ha : (a:Sym)∈L.map q := by rw [hLq];exact a.property
    obtain ⟨l,hl,hla⟩ := ha
    have he := congrArg f (mem_center_iff.mp hz (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩))
    simp only [map_mul] at he
    change q l*q y=q y*q l at he
    apply Subtype.ext
    change (a:Sym)*c=c*(a:Sym)
    rw [←hla,←hyc]
    exact he
  rw [alternatingGroup.center_eq_bot (by simp)] at hcc
  have he : c=1 := congrArg Subtype.val (mem_bot.mp hcc)
  rw [he,orderOf_one] at hc
  omega
end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
