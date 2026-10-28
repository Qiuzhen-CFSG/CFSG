module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Setup
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2Transport
public import Theory.Representation.G2OrthogonalCover.BinaryNormalizer

/-!
# The full actor on the binary G₂ Weyl cover

The chosen Weyl module carries an action of `N_G(L)` by conjugation.  In the
binary G₂ row the scalar fixed line is central in this normalizer, and the
normalizer carries the derived Weyl action to itself.  `BinaryNormalizer`
therefore upgrades the coordinate action to an action of the full split
`G₂(2)` model.  This is the actor package used by later fixed-space and
normalizer arguments; it does not assert that the scalar fixed line vanishes.

Source: Aschbacher--Smith B.4.6(1), printed pp.88--90, applied to the
original 12.4 Weyl marking.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02
open Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open Chapter12.Section04.SmallFusion
open ChapterB.QuasisimpleSource
open Atlas.G2.Natural

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

local notation "F" => ZMod 2
local notation "E" => TraceZero F
private abbrev DerivedActor := _root_.commutator (Atlas.G2.Model F)

/-- The trace-zero action of the split binary model is faithful.  This is
obtained from faithfulness of the natural quotient action and its canonical
projection, without identifying the derived actor with the full model. -/
theorem traceZeroAction_injective_binary :
    Function.Injective (Atlas.G2.Natural.traceZeroAction F) := by
  intro g h hgh
  apply Atlas.G2.Natural.action_injective F
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ := Atlas.G2.Natural.mk_surjective F v
  rw [Atlas.G2.Natural.action_mk, Atlas.G2.Natural.action_mk]
  exact congrArg (Atlas.G2.Natural.mk F) (LinearMap.congr_fun hgh x)

set_option maxHeartbeats 400000 in
/-- Package the actual conjugation action of `N_G(L)` as a full binary G₂
actor.  The returned coordinates are the literal chosen-module coordinates,
so the final equation can be used directly on elements of the original `V`.
-/
theorem exists_normalizer_full_g2_actor_marked
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    ∃ (b : V ≃* Multiplicative E)
      (φ : normalizer (L : Set G) →* Atlas.G2.Model F),
      (∀ (m : normalizer (L : Set G)) (x : E),
        (b.symm (Multiplicative.ofAdd
          (Atlas.G2.Natural.traceZeroAction F (φ m) x)) : G) =
          (m : G) * (b.symm (Multiplicative.ofAdd x) : G) * (m : G)⁻¹) ∧
      (∀ l : L, φ ⟨l, L.le_normalizer l.property⟩ =
        (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) : Atlas.G2.Model F)) := by
  classical
  let := D.elementary
  obtain ⟨z, hzOrder, hzGen, hzM, hzMV, _, _⟩ :=
    exists_fixed_involution_setup h D structural e hne
  have hz : z ∈ V := by
    exact (show z ∈ V ⊓ centralizer (L : Set G) from hzGen ▸ mem_zpowers z).1
  have hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z := by
    intro w hwV hwL
    have hw : w ∈ zpowers z := by
      rw [← hzGen]
      exact ⟨hwV, hwL⟩
    rw [mem_zpowers_iff_mem_range_orderOf, hzOrder] at hw
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := hzMV.le
  let b : V ≃* Multiplicative E :=
    D.spaceEquiv.symm.trans e.linearEquiv.toAddEquiv.toMultiplicative
  have hb (l : L) (v : V) :
      b.symm (Multiplicative.ofAdd (Atlas.G2.Natural.OrthogonalCover.action F
        (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) (b v).toAdd)) =
      V.normalizerMonoidHom ⟨l, D.normalizes l.property⟩ v := by
    apply b.injective
    rw [b.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    let w := (D.spaceEquiv.symm v).toAdd
    have he := e.intertwines (QuotientGroup.mk' (pCore 2 L) l) w
    have hw : D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l w)) =
        V.normalizerMonoidHom ⟨l, D.normalizes l.property⟩ v := by
      apply Subtype.ext
      rw [D.spaceEquiv_apply]
      have hv : (w.val.toMul.val : G) = (v : G) :=
        (D.spaceEquiv_apply w).symm.trans
          (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
      change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = _
      rw [hv]
      rfl
    change _ = e.linearEquiv (D.spaceEquiv.symm
      (V.normalizerMonoidHom ⟨l, D.normalizes l.property⟩ v)).toAdd
    rw [← hw, D.spaceEquiv.symm_apply_apply]
    exact he.symm
  have hsurj : Function.Surjective
      (fun l : L => e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) :=
    e.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let zi := b.symm (Multiplicative.ofAdd (identity F))
  let z0 : G := zi.val
  have hz0 : z0 ∈ V := zi.property
  have hz01 : z0 ≠ 1 := by
    intro heq
    have hh : zi = 1 := Subtype.ext heq
    have hh' := congrArg (fun v : V => (b v).toAdd) hh
    have hi : identity F = 0 := by
      change (b (b.symm (Multiplicative.ofAdd (identity F)))).toAdd = (b 1).toAdd at hh'
      rw [b.apply_symm_apply, map_one] at hh'
      exact hh'
    exact Atlas.SplitOctonion.unit_ne_zero (congrArg Subtype.val hi)
  have hz0L : z0 ∈ centralizer (L : Set G) := by
    intro l hl
    have heq := hb ⟨l, hl⟩ zi
    rw [show (b zi).toAdd = identity F from
      congrArg Multiplicative.toAdd (b.apply_symm_apply _)] at heq
    rw [show OrthogonalCover.action F (e.groupEquiv
      (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩)) (identity F) = identity F from
      traceZeroAction_identity F _] at heq
    have hc : l * z0 * l⁻¹ = z0 := (congrArg Subtype.val heq).symm
    exact mul_inv_eq_iff_eq_mul.mp hc
  have hz0eq : z0 = z := (hfixed z0 hz0 hz0L).resolve_left hz01
  let c : Additive V ≃ₗ[F] E := by
    let ca : Additive V ≃+ E := {
      toFun v := (b v.toMul).toAdd
      invFun w := Additive.ofMul (b.symm (Multiplicative.ofAdd w))
      left_inv v := congrArg Additive.ofMul (b.symm_apply_apply v.toMul)
      right_inv w := congrArg Multiplicative.toAdd (b.apply_symm_apply _)
      map_add' v w := congrArg Multiplicative.toAdd (map_mul b v.toMul w.toMul) }
    exact { ca with map_smul' := ZMod.map_smul ca }
  let ρ := elementaryRepresentation (p := 2)
    (V.normalizerMonoidHom.comp (inclusion hMV))
  let σ : Representation F (normalizer (L : Set G)) E :=
    c.conjRingEquiv.toMonoidHom.comp ρ
  have hσ (m : normalizer (L : Set G)) (v : E) :
      (b.symm (Multiplicative.ofAdd (σ m v)) : G) =
        (m : G) * (b.symm (Multiplicative.ofAdd v) : G) * (m : G)⁻¹ := by
    change (b.symm (b (V.normalizerMonoidHom
      ⟨m, hMV m.property⟩ (b.symm (Multiplicative.ofAdd v)))) : G) = _
    rw [b.symm_apply_apply]
    rfl
  have hσi (m : normalizer (L : Set G)) : σ m (identity F) = identity F := by
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    rw [hσ]
    change (m : G) * z0 * (m : G)⁻¹ = z0
    rw [hz0eq]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp (hzM.le m.property))
  have hσn (m : normalizer (L : Set G)) (g : DerivedActor) :
      ∃ j : DerivedActor, ∀ x,
        σ m (Atlas.G2.Natural.OrthogonalCover.action F g x) =
          Atlas.G2.Natural.OrthogonalCover.action F j (σ m x) := by
    obtain ⟨l, rfl⟩ := hsurj g
    let l' : L := ⟨(m : G) * l * (m : G)⁻¹,
      (mem_normalizer_iff.mp m.property l).mp l.property⟩
    refine ⟨e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l'), ?_⟩
    intro x
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    rw [hσ]
    have hh (k : L) (w : E) :
        (b.symm (Multiplicative.ofAdd
          (Atlas.G2.Natural.OrthogonalCover.action F
            (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) k)) w)) : G) =
          (k : G) * (b.symm (Multiplicative.ofAdd w) : G) * (k : G)⁻¹ := by
      have hh := congrArg Subtype.val (hb k
        (b.symm (Multiplicative.ofAdd w)))
      rw [b.apply_symm_apply] at hh
      exact hh
    rw [hh, hh, hσ]
    dsimp only [l']
    group
  have hactor (m : normalizer (L : Set G)) :
      ∃ g : Atlas.G2.Model F, ∀ x,
        σ m x = Atlas.G2.Natural.traceZeroAction F g x := by
    exact Atlas.G2.Natural.OrthogonalCover.normalizing_equiv_eq_traceZeroAction
      (LinearEquiv.ofBijective (σ m) (σ.apply_bijective m)) (by simpa using hσi m)
      (by simpa [LinearEquiv.ofBijective] using hσn m)
  have huniq {g k : Atlas.G2.Model F}
      (hg : ∀ x, Atlas.G2.Natural.traceZeroAction F g x =
        Atlas.G2.Natural.traceZeroAction F k x) : g = k := by
    apply traceZeroAction_injective_binary
    exact LinearMap.ext hg
  let φ : normalizer (L : Set G) →* Atlas.G2.Model F := {
    toFun := fun m => Classical.choose (hactor m)
    map_one' := by
      apply huniq
      intro x
      have hm := Classical.choose_spec (hactor (1 : normalizer (L : Set G))) x
      simpa using hm.symm
    map_mul' := by
      intro m n
      apply huniq
      intro x
      calc
        Atlas.G2.Natural.traceZeroAction F
            (Classical.choose (hactor (m * n))) x = σ (m * n) x :=
          (Classical.choose_spec (hactor (m * n)) x).symm
        _ = σ m (σ n x) := by rw [map_mul]; rfl
        _ = Atlas.G2.Natural.traceZeroAction F
            (Classical.choose (hactor m)) (σ n x) :=
          Classical.choose_spec (hactor m) (σ n x)
        _ = Atlas.G2.Natural.traceZeroAction F
            (Classical.choose (hactor m))
              (Atlas.G2.Natural.traceZeroAction F (Classical.choose (hactor n)) x) :=
          congrArg _ (Classical.choose_spec (hactor n) x)
        _ = Atlas.G2.Natural.traceZeroAction F
            (Classical.choose (hactor m) * Classical.choose (hactor n)) x := by
          rw [map_mul]; rfl }
  have hφ (m : normalizer (L : Set G)) (x : E) :
      (b.symm (Multiplicative.ofAdd
        (Atlas.G2.Natural.traceZeroAction F (φ m) x)) : G) =
        (m : G) * (b.symm (Multiplicative.ofAdd x) : G) * (m : G)⁻¹ := by
    rw [← show σ m x = Atlas.G2.Natural.traceZeroAction F (φ m) x from
      Classical.choose_spec (hactor m) x]
    exact hσ m x
  refine ⟨b, φ, hφ, ?_⟩
  intro l
  apply huniq
  intro x
  apply Multiplicative.ofAdd.injective
  apply b.symm.injective
  apply Subtype.ext
  rw [hφ]
  have hh := congrArg Subtype.val (hb l (b.symm (Multiplicative.ofAdd x)))
  rw [b.apply_symm_apply] at hh
  exact hh.symm

/-- The full actor in literal ambient coordinates, without the optional
restriction formula for the originally marked derived subgroup. -/
theorem exists_normalizer_full_g2_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    ∃ (b : V ≃* Multiplicative E)
      (φ : normalizer (L : Set G) →* Atlas.G2.Model F),
      ∀ (m : normalizer (L : Set G)) (x : E),
        (b.symm (Multiplicative.ofAdd
          (Atlas.G2.Natural.traceZeroAction F (φ m) x)) : G) =
          (m : G) * (b.symm (Multiplicative.ofAdd x) : G) * (m : G)⁻¹ := by
  obtain ⟨b, φ, hφ, _⟩ := exists_normalizer_full_g2_actor_marked h D structural e hne
  exact ⟨b, φ, hφ⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
