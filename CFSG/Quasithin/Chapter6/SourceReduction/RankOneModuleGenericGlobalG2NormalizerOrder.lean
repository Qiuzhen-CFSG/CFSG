module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2NormalizerParameters
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Thompson
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterRootAction
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterCentralizer

/-!
# Bounding both original G₂ normalizer indices

The original source core is the full ambient Sylow. Its normalizer is the
intersection of the two factor normalizers and hence preserves both original
parabolics and their whole common Borel. Hall conjugacy splits this normalizer
as the Sylow times its intersection with the marked torus normalizer.

The latter acts faithfully on the Sylow: characteristic two bounds the kernel
by the Sylow, whose intersection with the torus normalizer is trivial. Both
parabolic maps give the six separate root actions. Their mixed-root identities
bound this faithful actor group by (q-1)^2 n. Cancelling the original Borel order
bounds both parabolic indices by n. The preceding Thompson count consequently
gives |G| ≤ n |G₂(F)|, with no extra index or local-action premise.

The Chapter 12 companion applies the same bound to the literal chosen-module
pair. Geometric smallness and completion recognition are subsequent steps;
exhaustive amalgam comparison and original uniqueness remain source obligations.
Source: Aschbacher–Smith F.4.29, F.4.43–44, pp.289,296, and 5.3.1–4,
pp.658–659 (`refs/quasithin.pdf`). Internal imports reuse the checked root
transport and product-count lemmas within this proof family.
-/

public noncomputable section
open scoped Pointwise
open Subgroup Subgroup.OddHall Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  {F : Type} [Field F] [Finite F] [CharP F 2]

private def sylowEquiv
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    unipotent (K := F) ≃* sourceS L H :=
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  let hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  let hUP : unipotent (K := F) ≤ parabolic₁ := le_sup_left.trans borel_le_parabolic₁
  ((subgroupOfEquivOfLe hUP).symm.trans
      (equivMapOfInjective (unipotent.subgroupOf parabolic₁) f hf)).trans
        (MulEquiv.subgroupCongr (source_g2_inverse_sylow_image d h hTH e))

private theorem torus_normalizer_root_actions
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    {D : Subgroup G}
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus)
    (t : G) (htS : t ∈ normalizer (sourceS L H : Set G))
    (htP : t ∈ normalizer (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Set G))
    (htQ : t ∈ normalizer (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 : Set G))
    (htD : t ∈ normalizer (D : Set G)) :
    ∃ ρ : Fin 6 → F ≃+ F, ∀ v : Fin 6 → F,
      ((MulAut.congr (sylowEquiv d h hTH e).symm
        ((sourceS L H).normalizerMonoidHom ⟨t,htS⟩)) (unipotentEquiv v)).val =
        unipotentProduct (fun i => ρ i (v i)) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  have hC := (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH)).ge
  have htor : splitTorus (K := F) ≤ parabolic₁ ⊓ parabolic₂ :=
    le_inf (le_sup_right.trans borel_le_parabolic₁) (le_sup_right.trans borel_le_parabolic₂)
  have hmr (x : P) : x.val∈D ↔ (e.right x).val∈splitTorus := by
    constructor
    · intro hx
      let y : (Q ⊓ P : Subgroup G) := ⟨x.val,hC (hD hx)⟩
      have he := congrArg Subtype.val (e.right_commutes y)
      change (e.right x).val=(e.middle y).val at he
      rw [he]
      exact (hmark y).mp hx
    · intro hx
      let y : ChapterF.GreenBook.LieModels.G2.overlap (F := F) := ⟨(e.right x).val,htor hx⟩
      have he := congrArg Subtype.val (e.symm.right_commutes y)
      change (e.right.symm (e.right x)).val = (e.middle.symm y).val at he
      rw [e.right.symm_apply_apply] at he
      rw [he]
      exact (hmark _).mpr (by simpa only [e.middle.apply_symm_apply] using hx)
  have hml (x : Q) : x.val∈D ↔ (e.left x).val∈splitTorus := by
    constructor
    · intro hx
      let y : (Q ⊓ P : Subgroup G) := ⟨x.val,hC (hD hx)⟩
      have he := congrArg Subtype.val (e.left_commutes y)
      change (e.left x).val=(e.middle y).val at he
      rw [he]
      exact (hmark y).mp hx
    · intro hx
      let y : ChapterF.GreenBook.LieModels.G2.overlap (F := F) := ⟨(e.left x).val,htor hx⟩
      have he := congrArg Subtype.val (e.symm.left_commutes y)
      change (e.left.symm (e.left x)).val = (e.middle.symm y).val at he
      rw [e.left.symm_apply_apply] at he
      rw [he]
      exact (hmark _).mpr (by simpa only [e.middle.apply_symm_apply] using hx)
  let b := MulAut.congr e.right (P.normalizerMonoidHom ⟨t,htP⟩)
  let c := MulAut.congr e.left (Q.normalizerMonoidHom ⟨t,htQ⟩)
  let eU := sylowEquiv d h hTH e
  let cS := (sourceS L H).normalizerMonoidHom ⟨t,htS⟩
  let a : MulAut (unipotent (K := F)) := MulAut.congr eU.symm cS
  have hUP : unipotent (K := F) ≤ parabolic₁ := le_sup_left.trans borel_le_parabolic₁
  have he (x : unipotent (K := F)) : eU (a x)=cS (eU x) := eU.apply_symm_apply _
  have hb (x : unipotent (K := F)) :
      (b ⟨x.val,hUP x.property⟩).val = (a x).val := by
    suffices b ⟨x.val,hUP x.property⟩ = ⟨(a x).val,hUP (a x).property⟩ from congrArg Subtype.val this
    apply e.right.symm.injective
    change e.right.symm (e.right _) = _
    rw [e.right.symm_apply_apply]
    apply Subtype.ext
    change t*(e.right.symm ⟨x.val,hUP x.property⟩).val*t⁻¹ =
      (e.right.symm ⟨(a x).val,hUP (a x).property⟩).val
    exact (congrArg Subtype.val (he x)).symm
  have hagree (x : unipotent (K := F)) :
      (e.right.symm ⟨x.val,hUP x.property⟩).val =
      (e.left.symm ⟨x.val,borel_le_parabolic₂ (mem_sup_left x.property)⟩).val := by
    let z : ChapterF.GreenBook.LieModels.G2.overlap (F := F) :=
      ⟨x.val,hUP x.property,borel_le_parabolic₂ (mem_sup_left x.property)⟩
    exact (congrArg Subtype.val (e.symm.right_commutes z)).trans
      (congrArg Subtype.val (e.symm.left_commutes z)).symm
  have hc (x : unipotent (K := F)) :
      (c ⟨x.val,borel_le_parabolic₂ (mem_sup_left x.property)⟩).val = (a x).val := by
    suffices c ⟨x.val,borel_le_parabolic₂ (mem_sup_left x.property)⟩ =
        ⟨(a x).val,borel_le_parabolic₂ (mem_sup_left (a x).property)⟩ from congrArg Subtype.val this
    apply e.left.symm.injective
    change e.left.symm (e.left _) = _
    rw [e.left.symm_apply_apply]
    apply Subtype.ext
    change t*(e.left.symm ⟨x.val,_⟩).val*t⁻¹ = (e.left.symm ⟨(a x).val,_⟩).val
    rw [←hagree,←hagree]
    exact (congrArg Subtype.val (he x)).symm
  have hbD := torus_action_map P parabolic₁ splitTorus e.right D t htP htD hmr
  have hcD := torus_action_map Q parabolic₂ splitTorus e.left D t htQ htD hml
  have hq : 2 < Nat.card F := by
    rw [(d.g2_local_structure h hTH hp F (Or.inr ⟨e⟩)).1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  exact G2OuterRootNormalization.root_actions hq a b c hb hc hbD hcD

omit [Finite G] in
private theorem normalizes_source_parabolic
    {N S : Subgroup G} {J : Fin 2 → Subgroup G}
    (hNS : N ≤ normalizer (S : Set G))
    (hNJ : ∀ i, N ≤ normalizer (J i : Set G)) (i : Fin 2) :
    N ≤ normalizer (ChapterF.Source.parabolic J S i : Set G) := by
  have hb (j : Fin 2) : N ≤ normalizer (ChapterF.Source.borel (J j) S : Set G) := by
    have hi := (le_inf hNS (hNJ j)).trans inf_normalizer_le_normalizer_inf
    exact (le_inf (hNJ j) (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf ((le_inf (hNJ i) hNS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
    (hb (ChapterF.Source.other i))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Each original parabolic has index at most the original field degree in
its full ambient factor normalizer. -/
theorem Preparation.g2_normalizer_indices
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    ∀ i : Fin 2, (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).relIndex
      (normalizer (![L,residual H] i : Set G)) ≤ n := by
  let S := sourceS L H
  let C := ChapterF.Source.commonBorel ![L,residual H] S
  let P := ChapterF.Source.parabolic ![L,residual H] S
  let N := normalizer (S : Set G)
  let J : Fin 2 → Subgroup G := ![L,residual H]
  let hf := d.hypothesisF11 h hH.1.1.2
  have hST : S = (T : Subgroup G) := d.g2_sourceS_eq_sylow h hH hp F (Or.inr ⟨e⟩)
  have hs := d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)
  have hS (i : Fin 2) : S ≤ J i := hs.2.2.2.2 i
  have hT (i : Fin 2) : (T : Subgroup G) ≤ J i := hST ▸ hS i
  have hcomp : ConcreteAmalgamComparison (sourceParabolicAmalgam J S) := .g2 F (Or.inr ⟨e⟩)
  have hgeom := d.normalizer_geometry h hH (d.g2_right_maximal_all h hH hp F (Or.inr ⟨e⟩))
    (R := S) (hST.trans (inf_eq_left.mpr (hT 0)).symm)
    (hST.trans (inf_eq_left.mpr (hT 1)).symm)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hcomp)
  have hNN : N = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := hgeom.2.1
  have hNJ (i : Fin 2) : N ≤ normalizer (J i : Set G) := by
    rw [hNN]
    fin_cases i
    · exact inf_le_left
    · exact inf_le_right
  have hNP (i : Fin 2) : N ≤ normalizer (P i : Set G) :=
    normalizes_source_parabolic le_rfl hNJ i
  have hNC : N ≤ normalizer (C : Set G) := by
    have hc : P 0 ⊓ P 1 = C := ChapterF.Source.lemma_F_1_3_6 hf
    rw [←hc]
    exact (le_inf (hNP 0) (hNP 1)).trans inf_normalizer_le_normalizer_inf
  have hCN : C ≤ N := by
    have hh := hf.commonBorel_normalizes_localSylow 0
    change C ≤ normalizer ((S ⊓ J 0 : Subgroup G) : Set G) at hh
    rwa [inf_eq_left.mpr (hS 0)] at hh
  obtain ⟨D,hDC,hHall,hmark,hdis,_,_⟩ := d.g2_source_sylow_torus_split h hH.1.1.2 hp F e
  let E := N ⊓ normalizer (D : Set G)
  let eU := sylowEquiv d h hH.1.1.2 e
  let act : E →* MulAut (unipotent (K := F)) :=
    (MulAut.congr eU.symm).toMonoidHom.comp
      (S.normalizerMonoidHom.comp (inclusion inf_le_left))
  have hcore : (normalizer (L : Set G)).pCoreIn 2 ≤ S := by
    rw [hST]
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_normalizes] using
      pCoreIn_le_sylow (normalizer (L : Set G)) (T.subtype h.sylow_normalizes)
  have hchar : normalizer (L : Set G) ⊓
      centralizer ((normalizer (L : Set G)).pCoreIn 2 : Set G) ≤
      (normalizer (L : Set G)).pCoreIn 2 :=
    Chapter1.mem_He_iff.mpr (h.qtke.evenCharacteristic T _ h.maximal h.sylow_normalizes)
  have hai : Function.Injective act := by
    apply (MonoidHom.ker_eq_bot_iff act).mp
    apply bot_unique
    intro x hx
    have heq : S.normalizerMonoidHom (inclusion (show E ≤ N from inf_le_left) x) = 1 :=
      (MulAut.congr eU.symm).injective (show MulAut.congr eU.symm _ = _ from
        (show act x = 1 from hx).trans (map_one (MulAut.congr eU.symm)).symm)
    have hc : x.val ∈ centralizer (S : Set G) := by
      intro s hsS
      have hh := congrArg (fun a : MulAut S => (a ⟨s,hsS⟩).val) heq
      change x.val*s*x.val⁻¹=s at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hxS : x.val ∈ S := hcore (hchar ⟨hNJ 0 x.property.1,centralizer_le hcore hc⟩)
    exact Subtype.ext (disjoint_def.mp hdis hxS x.property.2)
  have hE : Nat.card E ≤ (Nat.card F-1)^2*n :=
    G2NormalizerOrder.card_le_of_root_actions act hai (fun x =>
      torus_normalizer_root_actions d h hH.1.1.2 hp e hDC hmark x.val x.property.1
        (hNP 1 x.property.1) (hNP 0 x.property.1) x.property.2) hs.1
  obtain ⟨R,hR⟩ := hf.sylow_commonBorel
  have hsplit : (N : Set G) = (S : Set G) * (E : Set G) :=
    OddHall.normal_sylow_frattini C S N D hf.commonBorel_solvable S.le_normalizer hNC R hR hDC hHall
  have hcN : Nat.card N = Nat.card S * Nat.card E :=
    split_card S.le_normalizer inf_le_left (hdis.mono_right inf_le_right) hsplit
  have hSC : S ≤ C := le_sup_right
  have hcC : Nat.card C = Nat.card S * (Nat.card F-1)^2 := by
    have heC : C ≃* Atlas.G2.borel (K := F) :=
      ((MulEquiv.subgroupCongr (ChapterF.Source.lemma_F_1_3_6 hf)).symm.trans e.middle).trans
        (MulEquiv.subgroupCongr ChapterF.GreenBook.LieModels.G2.overlap_eq_borel)
    rw [Nat.card_congr heC.toEquiv,←Nat.card_congr eU.toEquiv,card_unipotent,card_borel]
  have hidx : C.relIndex N ≤ n := by
    have hmul : Nat.card C * C.relIndex N = Nat.card N := by
      simpa only [relIndex_bot_left] using relIndex_mul_relIndex ⊥ C N bot_le hCN
    have hbound : Nat.card N ≤ Nat.card C*n := by
      rw [hcN,hcC,mul_assoc]
      exact Nat.mul_le_mul_left _ hE
    rw [←hmul] at hbound
    exact Nat.le_of_mul_le_mul_left hbound Nat.card_pos
  have hprod (i : Fin 2) : normalizer (J i : Set G) = P i ⊔ N := by
    apply le_antisymm
    · intro x hx
      have hh : ∃ l ∈ J i, ∃ b ∈ N, x=l*b := by
        fin_cases i
        · exact hgeom.2.2.2.2.1 x hx
        · exact hgeom.2.2.2.2.2.1 x hx
      obtain ⟨l,hl,b,hb,rfl⟩ := hh
      exact (P i ⊔ N).mul_mem
        ((show J i ≤ P i ⊔ N from (le_sup_left.trans le_sup_left).trans le_sup_left) hl)
        ((show N ≤ P i ⊔ N from le_sup_right) hb)
    · refine sup_le ?_ (hNJ i)
      exact (normal_subgroupOf_iff_le_normalizer
        (show J i ≤ P i from le_sup_left.trans le_sup_left)).mp (hf.local_normal_in_parabolic i)
  intro i
  change (P i).relIndex (normalizer (J i : Set G)) ≤ n
  rw [hprod i,OddHall.relIndex_normalized_sup _ _ (hNP i)]
  exact (relIndex_le_of_le_left (ChapterF.Source.commonBorel_le_parabolic i)
    (show C.relIndex N ≠ 0 from index_ne_zero_of_finite)).trans hidx

/-- The ambient Thompson bound has no remaining normalizer-index premise. -/
theorem Preparation.g2_ambient_order_le
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    Nat.card G ≤ n * Nat.card (Model F) := by
  obtain ⟨e,_,_,_,hb⟩ := d.g2_thompson_counts h hH hp F he
  have hi := d.g2_normalizer_indices h hH hp e
  exact hb.trans (Nat.mul_le_mul_right _ (max_le (hi 0) (hi 1)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

