module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.SourceAction
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.ActorLifting
public import Theory.GroupTheory.SylowThreeNormalizerSection

/-!
# Splitting the root actor over the alpha core

The explicit diagonal three-subgroup of the root actor lifts through a
self-centralizing normal `UT₃(F₄)` subgroup. The Sylow--Frattini normalizer
argument gives a genuine actor lift; generation by the inner image and the
lift then identifies the ambient group with the standard root normalizer
model, preserving the marked root inclusion.

Source: DGS, *Groups and Graphs* (1985), (10.9), p.163; Aschbacher,
*Sporadic Groups* (1994), 46.3(3), p.251, and 46.14, pp.257--258.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace Matrix.PSL3Four.RootNormalizerModel.SourceAction
variable {A : Type*} [Group A] (Q : Subgroup A) [Q.Normal]

def rootEmbedding (e : Q ≃* Root) : Root →* A := Q.subtype.comp e.symm.toMonoidHom

structure SplitAction (e : Q ≃* Root) where
  lift : actor →* A
  action : ∀ a, conjugation Q e (lift a) = a.val
  disjoint : ∀ a, lift a ∈ Q → a = 1
  generation : Q ⊔ lift.range = ⊤

theorem exists_splitAction [Finite A] (e : Q ≃* Root)
    (hc : centralizer (Q : Set A) ≤ Q)
    (himage : (conjugation Q e).range = (MulAut.conj : Root →* MulAut Root).range ⊔ actor) :
    Nonempty (SplitAction Q e) := by
  let f := conjugation Q e
  let K : Subgroup A := f.ker
  let B : Subgroup A := actor.comap f
  let π : B →* actor :=
    (f.comp B.subtype).codRestrict actor (fun x => x.property)
  have hπ : Function.Surjective π := by
    intro a
    have ha : (a : MulAut Root) ∈ f.range := by
      rw [himage]
      exact (le_sup_right : actor ≤ _) a.property
    obtain ⟨n, hn⟩ := ha
    refine ⟨⟨n, ?_⟩, ?_⟩
    · change f n ∈ actor
      exact hn ▸ a.property
    · apply Subtype.ext
      exact hn
  have hK : f.ker = K := rfl
  have hπker : π.ker = K.subgroupOf B := by
    ext x
    constructor
    · intro hx
      have hx' : f (x : A) = 1 := congrArg Subtype.val hx
      change (x : A) ∈ K
      exact hK ▸ MonoidHom.mem_ker.mpr hx'
    · intro hx
      apply Subtype.ext
      change f (x : A) = 1
      exact MonoidHom.mem_ker.mp (hK.symm ▸ hx)
  have hKN : K.Normal := by
    rw [← hK]
    infer_instance
  have hKBnormal : (K.subgroupOf B).Normal := hKN.subgroupOf B
  have hKleB : K ≤ B := by
    intro x hx
    change f x ∈ actor
    have hx' : f x = 1 := MonoidHom.mem_ker.mp (hK ▸ hx)
    rw [hx']
    exact actor.one_mem
  let M := ActorLifting.diagonalActor
  let Y : Subgroup B := M.comap π
  have hMnormal : M.Normal := ActorLifting.diagonalActor_normal
  have hYnormal : Y.Normal := hMnormal.comap π
  have hKY : K.subgroupOf B ≤ Y := by
    intro x hx
    change π x ∈ M
    have hx' : π x = 1 := MonoidHom.mem_ker.mp (hπker ▸ hx)
    rw [hx']
    exact M.one_mem
  have hMp : IsPGroup 3 M := ActorLifting.diagonalActor_isPGroup
  have hKp : IsPGroup 2 (K.subgroupOf B) := by
    have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 6) (by
      rw [Nat.card_congr e.toEquiv]
      exact SylowModel.card_U)
    let kq : K.subgroupOf B →* Q := {
      toFun x := ⟨((x : B) : A),hc ((kernel Q e) ▸ x.property)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    apply hQp.of_injective kq
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun q : Q => (q : A)) hxy))
  let πY : Y →* M :=
    (π.comp Y.subtype).codRestrict M (fun x => x.property)
  have hπY : Function.Surjective πY := by
    intro m
    obtain ⟨b, hb⟩ := hπ ⟨(m : actor), m.1.property⟩
    refine ⟨⟨b, ?_⟩, ?_⟩
    · change π b ∈ M
      rw [hb]
      exact m.property
    apply Subtype.ext
    exact hb
  have hπYker : πY.ker = (K.subgroupOf B).subgroupOf Y := by
    ext y
    constructor
    · intro hy
      have hy' : π (y : B) = 1 := congrArg Subtype.val hy
      change (y : B) ∈ K.subgroupOf B
      have hyK : (y : B) ∈ π.ker := (MonoidHom.mem_ker (f := π)).2 hy'
      exact hπker ▸ hyK
    · intro hy
      apply Subtype.ext
      have hyK : (y : B) ∈ K.subgroupOf B := hy
      have hpy : (y : B) ∈ π.ker := hπker.symm ▸ hyK
      exact (MonoidHom.mem_ker (f := π)).1 hpy
  have hq : IsPGroup 3 (Y ⧸ (K.subgroupOf B).subgroupOf Y) := by
    let KPY := (K.subgroupOf B).subgroupOf Y
    let _ : KPY.Normal := hKBnormal.subgroupOf Y
    have hle : KPY ≤ πY.ker := by rw [hπYker]
    let qmap := QuotientGroup.lift KPY πY hle
    have hqmapker : qmap.ker = ⊥ := by
      rw [QuotientGroup.ker_lift]
      apply (Subgroup.map_eq_bot_iff _).2
      rw [hπYker, QuotientGroup.ker_mk']
    have hqmapinj : Function.Injective qmap :=
      (MonoidHom.ker_eq_bot_iff qmap).mp hqmapker
    apply hMp.of_equiv (MulEquiv.ofBijective qmap ⟨hqmapinj, ?_⟩).symm
    intro m
    obtain ⟨y, hy⟩ := hπY m
    refine ⟨QuotientGroup.mk' KPY y, ?_⟩
    simpa [qmap] using (QuotientGroup.lift_mk' KPY hle y).trans hy
  let X : Sylow 3 Y := Classical.choice (Sylow.nonempty (p := 3) (G := Y))
  let P₃ : Subgroup B := (X : Subgroup Y).map Y.subtype
  have hgen : P₃ ⊔ K.subgroupOf B = Y :=
    SylowThreeNormalizer.sylow_supplement Y (K.subgroupOf B) hKY hq X
  have hYmap : Y.map π = M := by
    apply le_antisymm
    · exact map_le_iff_le_comap.mpr (le_rfl)
    · intro m hm
      obtain ⟨y, hy⟩ := hπY ⟨m, hm⟩
      exact ⟨y, y.property, congrArg Subtype.val hy⟩
  have hKmap : (K.subgroupOf B).map π = ⊥ :=
    ((Subgroup.map_eq_bot_iff (K.subgroupOf B)).2 (by rw [hπker]))
  have hPmap : P₃.map π = M := by
    have hh := congrArg (Subgroup.map π) hgen
    rw [Subgroup.map_sup, hKmap, sup_bot_eq, hYmap] at hh
    exact hh
  have hC : (K.subgroupOf B) ⊓ centralizer (P₃ : Set B) = ⊥ := by
    apply bot_unique
    rintro k ⟨hk, hkC⟩
    have hkCq : (k : A) ∈ centralizer (Q : Set A) := (kernel Q e) ▸ hk
    let rk : Q := ⟨(k : A),hc hkCq⟩
    let q : Root := e rk
    have hqcenter : q ∈ center Root := by
      apply (centerCongr e ⟨rk,?_⟩).property
      exact mem_center_iff.mpr (fun x => Subtype.ext (hkCq x x.property))
    have hfix : ∀ m : M, (m : MulAut Root) q = q := by
      intro m
      have hmP : (m : actor) ∈ P₃.map π := by
        rw [hPmap]
        exact m.property
      obtain ⟨p, hp, hpm⟩ : ∃ p : B, p ∈ P₃ ∧ π p = m := mem_map.mp hmP
      have hcomm : Commute (k : B) p := by
        exact (mem_centralizer_iff.mp hkC p hp).symm
      have hconj : MulAut.conjNormal (p : A) rk = rk := by
        apply Subtype.ext
        change (p : A) * (k : A) * (p : A)⁻¹ = (k : A)
        have hpk : (p : A) * (k : A) = (k : A) * (p : A) :=
          congrArg (fun z : B => (z : A)) hcomm.symm.eq
        rw [hpk]
        simp
      have hfp : f (p : B) = (m : MulAut Root) :=
        congrArg Subtype.val hpm
      have hh := DFunLike.congr_fun hfp q
      dsimp [f, conjugation] at hh
      simp only [MulAut.congr_apply, MulEquiv.trans_apply] at hh
      have hq_rk : e.symm q = rk := by simp [q]
      rw [hq_rk] at hh
      change e (MulAut.conjNormal (p : A) rk) =
        (m : MulAut Root) q at hh
      rw [hconj] at hh
      exact hh.symm
    have hq1 := ActorLifting.diagonalActor_center_fixed q hqcenter hfix
    have hrk1 : rk = 1 := e.injective (hq1.trans e.map_one.symm)
    apply Subtype.ext
    change (k : A) = 1
    exact congrArg (fun z : Q => (z : A)) hrk1
  let πTop : (⊤ : Subgroup B) →* actor :=
    π.comp (⊤ : Subgroup B).subtype
  have hπTop : Function.Surjective πTop := by
    intro a
    obtain ⟨b, hb⟩ := hπ a
    exact ⟨⟨b, trivial⟩, hb⟩
  have hπTopker : πTop.ker = (K.subgroupOf B).subgroupOf (⊤ : Subgroup B) := by
    ext x
    change πTop x = 1 ↔ x ∈ (K.subgroupOf B).subgroupOf (⊤ : Subgroup B)
    change π (x : B) = 1 ↔ (x : B) ∈ K.subgroupOf B
    rw [← MonoidHom.mem_ker, hπker]
  have hnormK : normalizer ((K.subgroupOf B : Subgroup B) : Set B) = ⊤ :=
    normalizer_eq_top_iff.mpr hKBnormal
  have hnormY : normalizer ((Y : Subgroup B) : Set B) = ⊤ :=
    normalizer_eq_top_iff.mpr hYnormal
  let E₃ :=
    SylowThreeNormalizer.normalizerEquiv Y (K.subgroupOf B) X hgen
      (by simp only [hnormK, le_top]) hKp hC (⊤ : Subgroup B)
      (by exact le_top) (by simp only [hnormK, le_top]) (by simp only [hnormY, le_top])
      πTop hπTop hπTopker
  let liftN : actor →*
      (normalizer (P₃ : Set B)).subgroupOf (⊤ : Subgroup B) := E₃.symm.toMonoidHom
  let liftU : actor →* (⊤ : Subgroup B) :=
    ((normalizer (P₃ : Set B)).subgroupOf (⊤ : Subgroup B)).subtype.comp liftN
  let liftB : actor →* B :=
    (⊤ : Subgroup B).subtype.comp liftU
  let lift : actor →* A := B.subtype.comp liftB
  have hact (a : actor) : f (lift a) = a.val := by
    change (πTop (liftU a) : MulAut Root) = a.val
    change (E₃ (E₃.symm a) : MulAut Root) = a.val
    exact congrArg Subtype.val (E₃.apply_symm_apply a)
  have hinner (n : A) (hn : n ∈ Q) :
      f n ∈ (MulAut.conj : Root →* MulAut Root).range := by
    let r : Q := ⟨n, hn⟩
    refine ⟨e r, ?_⟩
    have hfn : f n = MulAut.conj (e r) := by
      apply MulEquiv.ext
      intro x
      change e (r * e.symm x * r⁻¹) = _
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]
    exact hfn.symm
  have hroot (q : Root) :
      f (rootEmbedding Q e q) = MulAut.conj q := by
    apply MulEquiv.ext
    intro x
    change e (MulAut.conjNormal
      (rootEmbedding Q e q) (e.symm x)) = _
    change e (e.symm q * e.symm x *
      (e.symm q)⁻¹) = _
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]
  refine ⟨{
    lift := lift
    action := hact
    disjoint := by
      intro a ha
      obtain ⟨q, hq⟩ := hinner (lift a) ha
      apply ActorLifting.actor_inner_eq_one a q
      exact (hact a).symm.trans hq.symm
    generation := by
      let H : Subgroup A := Q ⊔ lift.range
      have himage : f.range ≤ H.map f := by
        rw [himage]
        apply sup_le
        · rintro _ ⟨q, rfl⟩
          refine ⟨rootEmbedding Q e q, ?_, hroot q⟩
          apply (le_sup_left : Q ≤ H)
          exact (e.symm q).property
        · intro a ha
          exact ⟨lift ⟨a, ha⟩, (le_sup_right : lift.range ≤ H) ⟨_, rfl⟩,
            hact ⟨a, ha⟩⟩
      apply top_unique
      intro n _
      obtain ⟨h, hh, he⟩ := himage (show f n ∈ f.range from ⟨n, rfl⟩)
      have hnk : n * h⁻¹ ∈ f.ker := by
        change f (n * h⁻¹) = 1
        rw [map_mul, map_inv, he, mul_inv_cancel]
      have hnH : n * h⁻¹ ∈ H := by
        apply (le_sup_left : Q ≤ H)
        have hk' : n * h⁻¹ ∈ K := hK ▸ hnk
        exact hc ((kernel Q e) ▸ hk')
      simpa only [inv_mul_cancel_right] using H.mul_mem hnH hh }⟩


namespace SplitAction
variable {Q} {e : Q ≃* Root} (S : SplitAction Q e)

theorem compatible (a : actor) :
    (rootEmbedding Q e).comp a.val.toMonoidHom =
      (MulAut.conj (S.lift a)).toMonoidHom.comp (rootEmbedding Q e) := by
  apply MonoidHom.ext
  intro x
  have h := DFunLike.congr_fun (S.action a) x
  change e (MulAut.conjNormal (S.lift a) (e.symm x)) = a.val x at h
  have he := congrArg e.symm h
  rw [e.symm_apply_apply] at he
  exact (congrArg (fun r : Q => (r : A)) he).symm

def modelMap : Model →* A :=
  SemidirectProduct.lift (rootEmbedding Q e) S.lift S.compatible

theorem modelMap_inl (x : Root) :
    S.modelMap (SemidirectProduct.inl x) = rootEmbedding Q e x :=
  SemidirectProduct.lift_inl _ _ _ _

theorem modelMap_inr (a : actor) :
    S.modelMap (SemidirectProduct.inr a) = S.lift a :=
  SemidirectProduct.lift_inr _ _ _ _

theorem modelMap_injective : Function.Injective S.modelMap := by
  apply S.modelMap.ker_eq_bot_iff.mp
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have hf : rootEmbedding Q e x.left * S.lift x.right = 1 := hx
  have ha : S.lift x.right = (rootEmbedding Q e x.left)⁻¹ := by
    calc
      _ = (rootEmbedding Q e x.left)⁻¹ *
          (rootEmbedding Q e x.left * S.lift x.right) := by group
      _ = _ := by rw [hf, mul_one]
  have hr : x.right = 1 := S.disjoint _ (by
    rw [ha]
    exact Q.inv_mem (e.symm x.left).property)
  have hl : x.left = 1 := by
    apply e.symm.injective
    apply Q.subtype_injective
    simpa only [hr, map_one, mul_one, rootEmbedding, MonoidHom.comp_apply,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] using hf
  exact SemidirectProduct.ext hl hr

theorem modelMap_surjective : Function.Surjective S.modelMap := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [←S.generation]
  apply sup_le
  · intro q hq
    refine ⟨SemidirectProduct.inl (e ⟨q,hq⟩),?_⟩
    rw [S.modelMap_inl]
    exact congrArg (fun r : Q => (r : A)) (e.symm_apply_apply ⟨q,hq⟩)
  · rintro _ ⟨a,rfl⟩
    exact ⟨SemidirectProduct.inr a,S.modelMap_inr a⟩

def modelEquiv : Model ≃* A :=
  MulEquiv.ofBijective S.modelMap ⟨S.modelMap_injective,S.modelMap_surjective⟩

theorem modelEquiv_coordinates (q : Q) :
    S.modelEquiv.symm (q : A) = SemidirectProduct.inl (e q) := by
  apply S.modelEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  change (q : A) = S.modelMap (SemidirectProduct.inl (e q))
  rw [S.modelMap_inl]
  exact (congrArg (fun r : Q => (r : A)) (e.symm_apply_apply q)).symm

end SplitAction

theorem exists_model_equiv [Finite A] (e : Q ≃* Root)
    (hc : centralizer (Q : Set A) ≤ Q)
    (himage : (conjugation Q e).range = (MulAut.conj : Root →* MulAut Root).range ⊔ actor) :
    ∃ f : A ≃* Model, ∀ q : Q, f (q : A) = SemidirectProduct.inl (e q) := by
  obtain ⟨s⟩ := exists_splitAction Q e hc himage
  exact ⟨s.modelEquiv.symm,s.modelEquiv_coordinates⟩

end Matrix.PSL3Four.RootNormalizerModel.SourceAction

