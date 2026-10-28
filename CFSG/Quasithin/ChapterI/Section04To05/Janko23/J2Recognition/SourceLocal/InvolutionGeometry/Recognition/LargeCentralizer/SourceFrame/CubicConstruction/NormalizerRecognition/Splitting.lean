module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.Action
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.ActorLifting
public import Theory.GroupTheory.SylowThreeNormalizerSection

/-!
# Splitting the explicit root actor

The diagonal subgroup of the actor is normal of order nine.  Its inverse
image in the actor preimage has kernel `E`. A Sylow three-subgroup maps
onto this diagonal subgroup, whose fixed points on `E` are trivial. The
Sylow--Frattini normalizer argument therefore lifts the whole actor. The
final generation step uses the literal inner-action image and the marked
root embedding.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3(3), p.251, and 46.14,
pp.257--258.
-/

@[expose] public section

open Subgroup Matrix.PSL3Four
open scoped Pointwise

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

theorem exists_splitAction (P : ReturningPair D)
    (A : RootAction P) :
    Nonempty (SplitAction P A.coordinates) := by
  let N := normalizer (P.R : Set G)
  let f := conjugation P A.coordinates
  let K : Subgroup N := P.E.subgroupOf N
  let B : Subgroup N := RootNormalizerModel.actor.comap f
  let π : B →* RootNormalizerModel.actor :=
    (f.comp B.subtype).codRestrict RootNormalizerModel.actor (fun x => x.property)
  have hπ : Function.Surjective π := by
    intro a
    have ha : (a : MulAut RootNormalizerModel.Root) ∈ f.range := by
      rw [A.image]
      exact (le_sup_right : RootNormalizerModel.actor ≤ _) a.property
    obtain ⟨n, hn⟩ := ha
    refine ⟨⟨n, ?_⟩, ?_⟩
    · change f n ∈ RootNormalizerModel.actor
      exact hn ▸ a.property
    · apply Subtype.ext
      exact hn
  have hK : f.ker = K := by
    simpa [K] using A.conjugation_kernel
  have hπker : π.ker = K.subgroupOf B := by
    ext x
    constructor
    · intro hx
      have hx' : f (x : N) = 1 := congrArg Subtype.val hx
      change (x : N) ∈ K
      exact hK ▸ MonoidHom.mem_ker.mpr hx'
    · intro hx
      apply Subtype.ext
      change f (x : N) = 1
      exact MonoidHom.mem_ker.mp (hK.symm ▸ hx)
  have hKN : K.Normal := by
    rw [← hK]
    infer_instance
  have hKBnormal : (K.subgroupOf B).Normal := hKN.subgroupOf B
  have hKleB : K ≤ B := by
    intro x hx
    change f x ∈ RootNormalizerModel.actor
    have hx' : f x = 1 := MonoidHom.mem_ker.mp (hK ▸ hx)
    rw [hx']
    exact RootNormalizerModel.actor.one_mem
  let M := RootNormalizerModel.ActorLifting.diagonalActor
  let Y : Subgroup B := M.comap π
  have hMnormal : M.Normal := RootNormalizerModel.ActorLifting.diagonalActor_normal
  have hYnormal : Y.Normal := hMnormal.comap π
  have hKY : K.subgroupOf B ≤ Y := by
    intro x hx
    change π x ∈ M
    have hx' : π x = 1 := MonoidHom.mem_ker.mp (hπker ▸ hx)
    rw [hx']
    exact M.one_mem
  have hMp : IsPGroup 3 M := RootNormalizerModel.ActorLifting.diagonalActor_isPGroup
  have hKp : IsPGroup 2 (K.subgroupOf B) := by
    let e₁ := subgroupOfEquivOfLe hKleB
    let e₂ := subgroupOfEquivOfLe (show P.E ≤ N from
      P.E_le_R.trans (show P.R ≤ N from le_normalizer))
    exact (P.E_elementary.isPGroup 2).of_equiv (e₁.trans e₂).symm
  let πY : Y →* M :=
    (π.comp Y.subtype).codRestrict M (fun x => x.property)
  have hπY : Function.Surjective πY := by
    intro m
    obtain ⟨b, hb⟩ := hπ ⟨(m : RootNormalizerModel.actor), m.1.property⟩
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
    have hkE : (k : G) ∈ P.E := by
      exact hk
    let rk : P.R := ⟨(k : G), P.E_le_R hkE⟩
    let q : RootNormalizerModel.Root := A.coordinates rk
    have hqcenter : q ∈ center RootNormalizerModel.Root := by
      obtain ⟨c, hc, hck⟩ := (show (k : G) ∈ (center P.R).map P.R.subtype by
        rw [A.E_center]
        exact hkE)
      have hrk : rk = c := by
        apply Subtype.ext
        exact hck.symm
      have hqeq : q = A.coordinates c := congrArg A.coordinates hrk
      rw [hqeq]
      exact (Subgroup.centerCongr A.coordinates ⟨c, hc⟩).property
    have hfix : ∀ m : M, (m : MulAut RootNormalizerModel.Root) q = q := by
      intro m
      have hmP : (m : RootNormalizerModel.actor) ∈ P₃.map π := by
        rw [hPmap]
        exact m.property
      obtain ⟨p, hp, hpm⟩ : ∃ p : B, p ∈ P₃ ∧ π p = m := mem_map.mp hmP
      have hcomm : Commute (k : B) p := by
        exact (mem_centralizer_iff.mp hkC p hp).symm
      have hconj : P.R.normalizerMonoidHom (p : B) rk = rk := by
        apply Subtype.ext
        change (p : G) * (k : G) * (p : G)⁻¹ = (k : G)
        have hpk : (p : G) * (k : G) = (k : G) * (p : G) :=
          congrArg (fun z : B => (z : G)) hcomm.symm.eq
        rw [hpk]
        simp
      have hfp : f (p : B) = (m : MulAut RootNormalizerModel.Root) :=
        congrArg Subtype.val hpm
      have hh := DFunLike.congr_fun hfp q
      dsimp [f, conjugation] at hh
      simp only [MulAut.congr_apply, MulEquiv.trans_apply] at hh
      have hq_rk : A.coordinates.symm q = rk := by simp [q]
      rw [hq_rk] at hh
      change A.coordinates (P.R.normalizerMonoidHom (p : B) rk) =
        (m : MulAut RootNormalizerModel.Root) q at hh
      rw [hconj] at hh
      exact hh.symm
    have hq1 := RootNormalizerModel.ActorLifting.diagonalActor_center_fixed q hqcenter hfix
    have hrk1 : rk = 1 := A.coordinates.injective (hq1.trans A.coordinates.map_one.symm)
    apply Subtype.ext
    apply Subtype.ext
    change (k : G) = 1
    exact congrArg (fun z : P.R => (z : G)) hrk1
  let πTop : (⊤ : Subgroup B) →* RootNormalizerModel.actor :=
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
  let liftN : RootNormalizerModel.actor →*
      (normalizer (P₃ : Set B)).subgroupOf (⊤ : Subgroup B) := E₃.symm.toMonoidHom
  let liftU : RootNormalizerModel.actor →* (⊤ : Subgroup B) :=
    ((normalizer (P₃ : Set B)).subgroupOf (⊤ : Subgroup B)).subtype.comp liftN
  let liftB : RootNormalizerModel.actor →* B :=
    (⊤ : Subgroup B).subtype.comp liftU
  let lift : RootNormalizerModel.actor →* N := B.subtype.comp liftB
  have hact (a : RootNormalizerModel.actor) : f (lift a) = a.val := by
    change (πTop (liftU a) : MulAut RootNormalizerModel.Root) = a.val
    change (E₃ (E₃.symm a) : MulAut RootNormalizerModel.Root) = a.val
    exact congrArg Subtype.val (E₃.apply_symm_apply a)
  have hinner (n : N) (hn : (n : G) ∈ P.R) :
      f n ∈ (MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range := by
    let r : P.R := ⟨(n : G), hn⟩
    refine ⟨A.coordinates r, ?_⟩
    have hfn : f n = MulAut.conj (A.coordinates r) := by
      apply MulEquiv.ext
      intro x
      change A.coordinates (r * A.coordinates.symm x * r⁻¹) = _
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]
    exact hfn.symm
  have hroot (q : RootNormalizerModel.Root) :
      f (rootEmbedding P A.coordinates q) = MulAut.conj q := by
    apply MulEquiv.ext
    intro x
    change A.coordinates (P.R.normalizerMonoidHom
      (rootEmbedding P A.coordinates q) (A.coordinates.symm x)) = _
    change A.coordinates (A.coordinates.symm q * A.coordinates.symm x *
      (A.coordinates.symm q)⁻¹) = _
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]
  refine ⟨{
    lift := lift
    action := hact
    disjoint := by
      intro a ha
      obtain ⟨q, hq⟩ := hinner (lift a) ha
      apply RootNormalizerModel.ActorLifting.actor_inner_eq_one a q
      exact (hact a).symm.trans hq.symm
    generation := by
      let H : Subgroup N := P.R.subgroupOf N ⊔ lift.range
      have himage : f.range ≤ H.map f := by
        rw [A.image]
        apply sup_le
        · rintro _ ⟨q, rfl⟩
          refine ⟨rootEmbedding P A.coordinates q, ?_, hroot q⟩
          apply (le_sup_left : P.R.subgroupOf N ≤ H)
          exact (A.coordinates.symm q).property
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
        apply (le_sup_left : P.R.subgroupOf N ≤ H)
        have hk' : n * h⁻¹ ∈ K := hK ▸ hnk
        exact P.E_le_R hk'
      simpa only [inv_mul_cancel_right] using H.mul_mem hnH hh }⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition
