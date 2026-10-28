module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.Head

/-!
# Displacement of a commuting twist on two natural modules

Commutation with a transvection and a coordinate cycle forces an endomorphism
of the natural binary SL₃(2) module to be scalar. Applied to all four blocks,
this identifies the commutant on two natural copies. Kernel reduction checks
the sixteen scalar block matrices: a nonidentity commuting involution,
multiplied by any nonidentity component involution, fixes exactly eight of the
sixty-four vectors. Rank-nullity gives displacement exactly three.

This concrete calculation completes the model input for the binary component
transfer near Aschbacher–Smith C.1.31–34, printed pp.135–137, combined manuscript
of 1 March 2004. It assumes neither an FF-module nor an offender.
-/

public section

open Representation Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.ComponentOffender.BestProjection.CentralTwist
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
local notation "W" => BinaryLinearThree.Vector
local notation "P" => W × W
local notation "τ" => Representation.prod BinaryLinearThree.W BinaryLinearThree.W

private def x : SL := ⟨!![1,1,0;0,1,0;0,0,1], by decide⟩
private def cycle : SL := ⟨!![0,0,1;1,0,0;0,1,0], by decide⟩

private lemma natural_matrix (g : SL) :
    LinearMap.toMatrix' (BinaryLinearThree.W g) = g.val :=
  LinearMap.toMatrix'_toLin' g.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem scalar_certificate :
    ∀ m : Matrix (Fin 3) (Fin 3) (ZMod 2),
      m * x.val = x.val * m → m * cycle.val = cycle.val * m →
        m = 0 ∨ m = 1 := by decide +kernel

private theorem scalar_of_commutes (f : Module.End (ZMod 2) W)
    (hf : ∀ g v, f (BinaryLinearThree.W g v) = BinaryLinearThree.W g (f v)) :
    ∃ a : ZMod 2, ∀ v, f v = a • v := by
  have hm (g : SL) : LinearMap.toMatrix' f * g.val = g.val * LinearMap.toMatrix' f := by
    have h : f.comp (BinaryLinearThree.W g) = (BinaryLinearThree.W g).comp f :=
      LinearMap.ext (hf g)
    simpa only [LinearMap.toMatrix'_comp, natural_matrix] using congrArg LinearMap.toMatrix' h
  rcases scalar_certificate (LinearMap.toMatrix' f) (hm x) (hm cycle) with h | h
  · have he : f = 0 := LinearMap.toMatrix'.injective (by simpa only [map_zero] using h)
    exact ⟨0, by intro v; simp [he]⟩
  · have he : f = LinearMap.id := LinearMap.toMatrix'.injective (by simpa using h)
    exact ⟨1, by intro v; simp [he]⟩

private def block (a b c d : ZMod 2) : Module.End (ZMod 2) P :=
  (a • LinearMap.fst (ZMod 2) W W + b • LinearMap.snd (ZMod 2) W W).prod
    (c • LinearMap.fst (ZMod 2) W W + d • LinearMap.snd (ZMod 2) W W)

private theorem block_apply (a b c d : ZMod 2) (v : P) :
    block a b c d v = (a • v.1 + b • v.2, c • v.1 + d • v.2) := rfl

private theorem commutant_blocks (f : Module.End (ZMod 2) P)
    (hf : ∀ g v, f (τ g v) = τ g (f v)) :
    ∃ a b c d : ZMod 2, f = block a b c d := by
  let f11 := (LinearMap.fst (ZMod 2) W W).comp (f.comp (LinearMap.inl (ZMod 2) W W))
  let f12 := (LinearMap.fst (ZMod 2) W W).comp (f.comp (LinearMap.inr (ZMod 2) W W))
  let f21 := (LinearMap.snd (ZMod 2) W W).comp (f.comp (LinearMap.inl (ZMod 2) W W))
  let f22 := (LinearMap.snd (ZMod 2) W W).comp (f.comp (LinearMap.inr (ZMod 2) W W))
  have h11 (g : SL) (v : W) : f11 (BinaryLinearThree.W g v) = BinaryLinearThree.W g (f11 v) := by
    have h := congrArg Prod.fst (hf g (v,0))
    change (f (BinaryLinearThree.W g v, BinaryLinearThree.W g 0)).1 = BinaryLinearThree.W g (f (v,0)).1 at h
    simpa only [f11, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply, map_zero] using h
  have h12 (g : SL) (v : W) : f12 (BinaryLinearThree.W g v) = BinaryLinearThree.W g (f12 v) := by
    have h := congrArg Prod.fst (hf g (0,v))
    change (f (BinaryLinearThree.W g 0, BinaryLinearThree.W g v)).1 = BinaryLinearThree.W g (f (0,v)).1 at h
    simpa only [f12, LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply, map_zero] using h
  have h21 (g : SL) (v : W) : f21 (BinaryLinearThree.W g v) = BinaryLinearThree.W g (f21 v) := by
    have h := congrArg Prod.snd (hf g (v,0))
    change (f (BinaryLinearThree.W g v, BinaryLinearThree.W g 0)).2 = BinaryLinearThree.W g (f (v,0)).2 at h
    simpa only [f21, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply, map_zero] using h
  have h22 (g : SL) (v : W) : f22 (BinaryLinearThree.W g v) = BinaryLinearThree.W g (f22 v) := by
    have h := congrArg Prod.snd (hf g (0,v))
    change (f (BinaryLinearThree.W g 0, BinaryLinearThree.W g v)).2 = BinaryLinearThree.W g (f (0,v)).2 at h
    simpa only [f22, LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.snd_apply, map_zero] using h
  obtain ⟨a,ha⟩ := scalar_of_commutes f11 h11
  obtain ⟨b,hb⟩ := scalar_of_commutes f12 h12
  obtain ⟨c,hc⟩ := scalar_of_commutes f21 h21
  obtain ⟨d,hd⟩ := scalar_of_commutes f22 h22
  refine ⟨a,b,c,d, LinearMap.ext fun v => ?_⟩
  have he : v = (v.1,0) + (0,v.2) := by simp
  rw [he, map_add]
  apply Prod.ext
  · change f11 v.1 + f12 v.2 = _
    rw [ha,hb]
    simp only [block_apply, Prod.fst_add, Prod.snd_add, zero_add, add_zero]
  · change f21 v.1 + f22 v.2 = _
    rw [hc,hd]
    simp only [block_apply, Prod.fst_add, Prod.snd_add, zero_add, add_zero]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 4096 in
private theorem fixed_card_certificate :
    ∀ a b c d : ZMod 2,
      (∀ v : P, block a b c d (block a b c d v) = v) →
      (∃ v : P, block a b c d v ≠ v) →
      ∀ t : SL, t ^ 2 = 1 → t ≠ 1 →
      (Finset.univ.filter (fun v : P => τ t (block a b c d v) = v)).card = 8 := by
  decide +kernel

/-- A nonidentity commuting involution on two natural copies makes every
nonidentity component involution displace exactly three dimensions. -/
theorem doubled_natural_twist_rank
    (f : Module.End (ZMod 2) P)
    (hf : ∀ g v, f (τ g v) = τ g (f v))
    (hff : f.comp f = LinearMap.id) (hfn : f ≠ LinearMap.id)
    (t : SL) (ht : t ^ 2 = 1) (htn : t ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range ((τ t).comp f - LinearMap.id)) = 3 := by
  classical
  obtain ⟨a,b,c,d,rfl⟩ := commutant_blocks f hf
  have hnon : ∃ v : P, block a b c d v ≠ v := by
    by_contra! h
    exact hfn (LinearMap.ext h)
  have hc := fixed_card_certificate a b c d (LinearMap.congr_fun hff) hnon t ht htn
  let D := (τ t).comp (block a b c d) - LinearMap.id
  have hcard : Nat.card (LinearMap.ker D) = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa only [LinearMap.mem_ker, D, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, sub_eq_zero] using hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
  have hker : Module.finrank (ZMod 2) (LinearMap.ker D) = 3 :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using hcard)
  have hdim : Module.finrank (ZMod 2) P = 6 := by
    simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector, Module.finrank_prod]
  have hr := D.finrank_range_add_finrank_ker
  change Module.finrank (ZMod 2) (LinearMap.range D) = 3
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.ComponentOffender.BestProjection.CentralTwist
