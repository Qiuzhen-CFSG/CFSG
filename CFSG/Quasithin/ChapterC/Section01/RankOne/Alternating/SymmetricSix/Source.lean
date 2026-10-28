module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SelectedSeed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SourcePreparation
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.NormalizerGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.BlockTyping

/-!
# C.1.24(c) for the original natural six-point action

Start with the original component, Sylow product, normal binary module and
marked transposition image of R. B.2.10 supplies the true kernel Sylow and
core intersection. Its centralizing Thompson branch makes Baum(R) normal.
In the other branch, the actual ordinary or triple A₆ cover supplies one
R-invariant cubic. Its preimage has Sylow index three and yields the genuine
local class on the original Baumann group. The same cubic generates G with
its Baumann normalizer. Uniform C.1.18 and C.1.21 propagation give a block,
and the literal natural-module coordinates identify it as an A₆-block.

Neither normality of L nor surjectivity/faithfulness of the given action
map is an extra premise: they are derived from the original product and
marking. A possible central cubic action kernel is retained throughout.
This is the natural-module, marked-transposition branch used in 13.5.6;
no claim is made here for the other module rows of general C.1.24.

Source: Aschbacher–Smith C.1.24(c), printed pp.130–131; its original
Chapter 13 application is 13.5.6.
-/

public section

open Subgroup Theory.GroupTheory Equiv Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.TranspositionCubic GlaubermanNiles GlaubermanArgument
universe u
variable {G : Type u} [Group G] [Finite G]

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

theorem normal_characteristic_or_alternatingBlock_of_natural_six
    (L V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hL : L.IsCComponent) (hf : generalizedFitting G=pCore 2 G)
    (hfL : generalizedFitting L=pCore 2 L)
    (T : Sylow 2 G) (hQR : pCore 2 G ≤ R) (hRT : R ≤ T)
    (hprod : ∀ g:G,∃l∈L,∃t∈(T:Subgroup G),l*t=g)
    (q : G →* Sym) (hLq : L.map q=alternatingGroup (Fin 6))
    (e : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q g) (e v).toAdd)
    (hm : ⁅V,L⁆ ≠ ⊥) (r : Sym) (hr : r.IsSwap) (hR : R.map q=zpowers r) :
    (∃ C : Subgroup (ChapterB.baumann R), C.Characteristic ∧ C≠⊥ ∧
      (C.map (ChapterB.baumann R).subtype).Normal) ∨ IsAlternatingBlock L 6 := by
  let := hL.perfect
  have hpL : IsPPerfect 2 L := perfect_twoPerfect
  have hres : pResidual 2 G=L := pResidual_eq_of_subnormal_product L (T:Subgroup G) hL.subnormal hpL T.isPGroup' hprod
  let : L.Normal := hres ▸ (inferInstance : (pResidual 2 G).Normal)
  have hq := surjective_of_marked_transposition L R q hLq r hr hR
  have hk := natural_six_kernel_eq_centralizer V q e he
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
    selected_inLocalClass R V hVR hpR hQR M hM hRq hn hf q r c hR.le hrJ hcH e he
      (hc ▸ pow_orderOf_eq_one c) hinv hmove
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
  exact halt.imp_right (fun hb => isAlternatingBlock_of_natural_six L V hb q hLq e he hm)
end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
