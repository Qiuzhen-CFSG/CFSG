module
public import Theory.SpecificGroups.SymmetricSix.TranspositionCubic.CoreMovement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SelectedSeed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SourcePreparation
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.NormalizerGeneration
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePoint

/-!
# The augmentation-core transposition branch of C.1.24(c)

The original five-space supplies the cubic movement used by C.1.18.
B.2.10 constructs the kernel Sylow and the selected cubic preimage has
Sylow index three. Its actual omega-center span is moved, giving the local
class on the original Baumann subgroup. The same cubic generates with its
Baumann normalizer, so C.1.21 propagates the resulting short seed to L.

The module remains the five-dimensional augmentation core throughout.
The natural quotient is used only to select a moving cubic; its fixed
vector lifts by the transposition displacement calculation. No natural
submodule or split central line is assumed. The nonsolvable Chapter 13
application consumes the resulting genuine block's shortness.

Source: Aschbacher–Smith C.1.24(c), pp.130–131; 13.2.2(7), pp.877–878.
This handles the transposition image; the full point-radical image in the
augmentation form of C.1.37 remains with qt-d-1341-nonsolvable-source.
-/

public section
open Subgroup Theory.GroupTheory Equiv Stellmacher Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.TranspositionCubic GlaubermanNiles GlaubermanArgument
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem core_selected_omega_movement (R V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) (M : Subgroup (G ⧸ pCore 2 G))
    (q : G →* Sym) (r c : Sym)
    (hR : R.map q ≤ zpowers r) (hrJ : r ∈ (elementaryAbelianMaxJ R).map q)
    (hcH : c ∈ (selectedGroup R M).map q)
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q g) (e v).toAdd)
    (hc : c^3=1) (hi : r*c*r⁻¹=c⁻¹)
    (hm : ¬fixedSpace (BinaryPermutation.coreRepresentation (Fin 6)) (zpowers r) ≤
      fixedSpace (BinaryPermutation.coreRepresentation (Fin 6)) (zpowers c)) :
    ¬ elementaryAbelianMaxJ (R.subgroupOf (selectedGroup R M)) ≤
      centralizer (normalClosure (omegaOneCenterAmbient
        (R.subgroupOf (selectedGroup R M)) : Set (selectedGroup R M)) : Set (selectedGroup R M)) := by
  let H := selectedGroup R M
  let V' := V.subgroupOf H
  let eV : V' ≃* V := subgroupOfEquivOfLe (hVR.trans (le_selectedGroup R M))
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.subgroupOf (hVR.trans (le_selectedGroup R M))
  have he' : ∀ (g : H) (v : V'), ((eV.trans e) (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) ((q.comp H.subtype) g) ((eV.trans e) v).toAdd := by
    intro g v
    exact he g (eV v)
  have hR' : (R.subgroupOf H).map (q.comp H.subtype) ≤ zpowers r := by
    rw [←map_map,map_subgroupOf_eq_of_le (le_selectedGroup R M)]
    exact hR
  have hrJ' : r ∈ (elementaryAbelianMaxJ (R.subgroupOf H)).map (q.comp H.subtype) := by
    rw [←map_map,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (le_selectedGroup R M)]
    exact hrJ
  have hc' : c ∈ (q.comp H.subtype).range := by
    obtain ⟨x,hx,hxc⟩ := hcH
    exact ⟨⟨x,hx⟩,hxc⟩
  exact core_omega_span_moved V' (R.subgroupOf H) (elementaryAbelianMaxJ (R.subgroupOf H))
    (comap_mono hVR) (q.comp H.subtype) (eV.trans e) he' r c hR' hrJ' hc' hc hi hm

private theorem core_selected_inLocalClass (R V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R)
    (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M=3)
    (hRq : Nat.card (R.map (QuotientGroup.mk' (pCore 2 G)))=2)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)))
    (hf : generalizedFitting G = pCore 2 G)
    (q : G →* Sym) (r c : Sym)
    (hR : R.map q ≤ zpowers r) (hrJ : r ∈ (elementaryAbelianMaxJ R).map q)
    (hcH : c ∈ (selectedGroup R M).map q)
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q g) (e v).toAdd)
    (hc : c^3=1) (hi : r*c*r⁻¹=c⁻¹)
    (hm : ¬fixedSpace (BinaryPermutation.coreRepresentation (Fin 6)) (zpowers r) ≤
      fixedSpace (BinaryPermutation.coreRepresentation (Fin 6)) (zpowers c)) :
    GlaubermanNiles.InLocalClass (inclusion
      (show ChapterB.baumann (R.subgroupOf (selectedGroup R M)) ≤
        pResidual 2 (selectedGroup R M) ⊔ ChapterB.baumann (R.subgroupOf (selectedGroup R M)) from le_sup_right)) := by
  obtain ⟨T,hT,hiT⟩ := selected_sylow R hpR hQR M hM hRq hn
  have hmove := core_selected_omega_movement R V hVR M q r c hR hrJ hcH e he hc hi hm
  rw [←hT] at hmove ⊢
  exact FiveBlockSource.cubic_omega_inLocalClass T hiT (selected_characteristic_two R M hf) hmove
private theorem perfect_twoPerfect {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] : IsPPerfect 2 E := by
  intro N hn hq
  let : N.Normal := hn
  by_contra hne
  let : Nontrivial (E ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (E ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (E ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (E ⧸ N) inferInstance

private theorem surjective_of_marked_transposition {A : Type*} [Group A] (L R : Subgroup A) (q : A →* Sym)
    (hL : L.map q=alternatingGroup (Fin 6)) (r : Sym) (hr : r.IsSwap)
    (hR : R.map q=zpowers r) : Function.Surjective q := by
  have ha : alternatingGroup (Fin 6)≤q.range := hL ▸ map_le_range q L
  have hd : q.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le ha
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact MonoidHom.range_eq_top.mp (index_eq_one.mp hi)
  · have he := Perm.eq_alternatingGroup_of_index_eq_two hi
    have hh : r∈q.range  := map_le_range q R (by rw [hR];exact mem_zpowers r)
    rw [he,Perm.mem_alternatingGroup,hr.sign_eq] at hh
    exact (by decide : (-1 : ℤˣ)≠1) hh |>.elim

theorem normal_characteristic_or_block_of_core_six
    (L V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hL : L.IsCComponent) (hf : generalizedFitting G=pCore 2 G)
    (hfL : generalizedFitting L=pCore 2 L)
    (T : Sylow 2 G) (hQR : pCore 2 G ≤ R) (hRT : R ≤ T)
    (hprod : ∀ g:G,∃l∈L,∃t∈(T:Subgroup G),l*t=g)
    (q : G →* Sym) (hLq : L.map q=alternatingGroup (Fin 6))
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q g) (e v).toAdd)
    (hm : ⁅V,L⁆ ≠ ⊥) (r : Sym) (hr : r.IsSwap) (hR : R.map q=zpowers r) :
    (∃ C : Subgroup (ChapterB.baumann R), C.Characteristic ∧ C≠⊥ ∧
      (C.map (ChapterB.baumann R).subtype).Normal) ∨ IsBlock L := by
  let := hL.perfect
  have hpL : IsPPerfect 2 L := perfect_twoPerfect
  have hres : pResidual 2 G=L := pResidual_eq_of_subnormal_product L (T:Subgroup G) hL.subnormal hpL T.isPGroup' hprod
  let : L.Normal := hres ▸ (inferInstance : (pResidual 2 G).Normal)
  have hq := surjective_of_marked_transposition L R q hLq r hr hR
  have hk := ChapterB.Offenders.SixCorePoint.kernel_centralizer V q e he
  have hpR : IsPGroup 2 R := T.isPGroup'.to_le hRT
  have hRne : R≠⊥ := by
    intro hb
    have hrb : zpowers r=⊥ := by rw [←hR,hb,Subgroup.map_bot]
    have hr1 : r=1 := zpowers_eq_bot.mp hrb
    have hh := hr.orderOf
    rw [hr1,orderOf_one] at hh
    omega
  let S := ChapterB.baumann R
  let : Nontrivial S := (nontrivial_iff_ne_bot _).mpr (baumann_ne_bot R hpR hRne)
  obtain ⟨⟨P,hPn,hP⟩,hcore,hRq,hS⟩ := original_action_preparation V R q hq hk T hQR hRT L hL hm hprod r hr hR
  rcases hS with hSn | hrJ
  · left
    exact ⟨⊤,inferInstance,top_ne_bot,by simpa only [←MonoidHom.range_eq_map,range_subtype] using hSn⟩
  have hQ : pCore 2 G ≤ q.ker := hcore.le.trans inf_le_right
  have hgen : L ⊔ (T:Subgroup G)=⊤ := by
    apply top_unique
    intro g _
    obtain ⟨l,hl,t,ht,rfl⟩ := hprod g
    exact mul_mem (mem_sup_left hl) (mem_sup_right ht)
  obtain ⟨c,M,hML,hM,hn,hMc,hc,hca,hinv,hgn,hcard,hmove,hgenerate⟩ :=
    exists_selected_normalizer_generate L R T q hq hQ hLq T.isPGroup' hgen P hP hpR hQR hcore.symm r hr hR
  let H := selectedGroup R M
  let B := ChapterB.baumann (R.subgroupOf H)
  let K := pResidual 2 H ⊔ B
  let i : K →* G := H.subtype.comp K.subtype
  let Y := (pResidual 2 H).map H.subtype
  have hVR : V ≤ R := (show V ≤ pCore 2 G from
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 V⟩).trans hQR
  have hYq : Y.map q=zpowers c := by
    let π := QuotientGroup.mk' (pCore 2 G)
    let qb := QuotientGroup.lift (pCore 2 G) q hQ
    have heq : qb.comp π=q := by ext x;rfl
    rw [←heq,←map_map,selected_residual_image R hpR M hM hn]
    exact hMc
  have hcH : c∈H.map q := (map_mono (map_subtype_le _)) (by rw [hYq];exact mem_zpowers c)
  have hloc : InLocalClass (inclusion (show B≤K from le_sup_right)) :=
    core_selected_inLocalClass R V hVR hpR hQR M hM hRq hn hf q r c hR.le hrJ hcH e he
      (hc ▸ pow_orderOf_eq_one c) hinv (core_fixed_movement_of_natural r c hr hmove)
  obtain ⟨E,hE⟩ := exists_selected_marking R M
  let emb : S →* K := (inclusion (show B≤K from le_sup_right)).comp E.toMonoidHom
  have hlocal : InLocalClass emb := hloc.precomp_equiv E
  have him : i.range=Y ⊔ S := by
    rw [MonoidHom.range_comp,range_subtype,Subgroup.map_sup,selected_baumann_map]
  have hi : Function.Injective i := H.subtype_injective.comp K.subtype_injective
  have hKgen : i.range ⊔ normalizer (S : Set G)=⊤ := by
    rw [him,sup_assoc,sup_of_le_right S.le_normalizer]
    exact hgenerate
  have hYlocal : (pResidual 2 K).map i=Y := selected_local_residual_map R hpR M
  have hYL : Y≤L := by
    apply (map_pResidual_le 2 H.subtype).trans
    exact sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top L (T:Subgroup G) T.isPGroup' hgen⟩
  have hQY : pCore 2 G≤normalizer (Y : Set G) := core_normalizes_selected_residual R M
  have hne := cubic_not_central_in_component L Y hL.subnormal hYL q hQ hLq c hc hYq
  have hpS : IsPGroup 2 S := hpR.to_le inf_le_left
  obtain ⟨D,hD⟩ := exists_universal_characteristicPair.{u,u} hpS (baumann_intrinsic_fixed R)
  have halt := embedded_local_seed_alternative S L emb i hi hE hlocal D hD hKgen
    (by rw [hYlocal];exact hYL) hL.subnormal hpL hfL
    (by rw [hYlocal];exact hQY) (by rw [hYlocal];exact hne)
  exact halt
end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
