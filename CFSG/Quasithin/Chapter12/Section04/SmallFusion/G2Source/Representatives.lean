module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Setup
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2Transport
public import Theory.Representation.G2OrthogonalCover.BinaryFusion

/-!
# Sylow-central representatives for the original binary G₂ row

This is the Weyl calculation from 12.2.16 extracted at the local
`Structural1222At` boundary.  It constructs the actual representatives needed
by 12.4.7 and does not use the 12.2.13 `NoEscape` assumption.  The fixed line
is supplied by the 12.4.2 setup; the Weyl scalar identity identifies the
coordinate fixed involution with that line.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02
open Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource
open Atlas.G2.Natural

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

local notation "F" => ZMod 2
local notation "E" => TraceZero F
private abbrev DerivedActor := _root_.commutator (Atlas.G2.Model F)

/-- Construct the `N_G(L)`-central representatives in the original binary G₂
row.  The hypotheses are exactly the fixed-line data from 12.4.2--3 and the
local structural prefix; no global `NoEscape` premise is present. -/
theorem exists_sylow_central_representatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    (hM : normalizer (L : Set G) = centralizer ({z} : Set G)) :
    ∀ x ∈ V, x ≠ 1 → x ≠ z →
      ∃ m ∈ normalizer (L : Set G),
        (T : Subgroup G) ≤ centralizer ({m * x * m⁻¹} : Set G) := by
  let := D.elementary
  let b : V ≃* Multiplicative E :=
    D.spaceEquiv.symm.trans e.linearEquiv.toAddEquiv.toMultiplicative
  have hb (l : L) (v : V) :
      b.symm (Multiplicative.ofAdd (OrthogonalCover.action F
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
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rcases ((structural L h).2.2 V D).2.2.2 with hn | heq
    · exact hn
    · exact (hz1 (mem_bot.mp (heq ▸
        (show z ∈ V ⊓ centralizer (L : Set G) from ⟨hz, hzL⟩)))).elim
  let M := normalizer (L : Set G)
  have hMz : ∀ m : M, MulAut.conj (m : G) z0 = z0 := by
    intro m
    have hmz : MulAut.conj (m : G) z = z := by
      change (m : G) * z * (m : G)⁻¹ = z
      exact mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp (hM ▸ m.property))
    simpa [hz0eq] using hmz
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
  let σ : Representation F M E := c.conjRingEquiv.toMonoidHom.comp ρ
  have hσ (m : M) (v : E) :
      (b.symm (Multiplicative.ofAdd (σ m v)) : G) =
        (m : G) * (b.symm (Multiplicative.ofAdd v) : G) * (m : G)⁻¹ := by
    change (b.symm (b (V.normalizerMonoidHom ⟨m, hMV m.property⟩
      (b.symm (Multiplicative.ofAdd v)))) : G) = _
    rw [b.symm_apply_apply]
    rfl
  have hσi (m : M) : σ m (identity F) = identity F := by
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    rw [hσ]
    simpa [z0, zi] using hMz m
  have hσn (m : M) (g : DerivedActor) : ∃ j : DerivedActor, ∀ x,
      σ m (OrthogonalCover.action F g x) = OrthogonalCover.action F j (σ m x) := by
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
        (b.symm (Multiplicative.ofAdd (OrthogonalCover.action F
          (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) k)) w)) : G) =
          (k : G) * (b.symm (Multiplicative.ofAdd w) : G) * (k : G)⁻¹ := by
      have hh := congrArg Subtype.val (hb k (b.symm (Multiplicative.ofAdd w)))
      rw [b.apply_symm_apply] at hh
      exact hh
    rw [hh, hh, hσ]
    dsimp only [l']
    group
  have hσq (m : M) (x : E) : OrthogonalCover.form F (σ m x) =
      OrthogonalCover.form F x :=
    OrthogonalCover.binary_form_normalized (σ m) (hσi m) (hσn m) x
  have hTM : (T : Subgroup G) ≤ M := (structural L h).1
  let τ := σ.comp (inclusion hTM)
  obtain ⟨v, hv, hvq, hvT⟩ := OrthogonalCover.binary_exists_fixed_singular
    T.isPGroup' τ (fun t x => hσq (inclusion hTM t) x)
  have hvn : mk F v ≠ 0 := by
    intro heq
    have hs : v ∈ scalarLine F := (Submodule.Quotient.mk_eq_zero _).mp heq
    rcases (OrthogonalCover.binary_scalar_iff v).mp hs with heq | rfl
    · exact hv heq
    · exact one_ne_zero ((OrthogonalCover.form_identity F).symm.trans hvq)
  intro x hx hx1 hxz
  let xi : V := ⟨x, hx⟩
  have hxn : mk F (b xi).toAdd ≠ 0 := by
    intro heq
    have hs : (b xi).toAdd ∈ scalarLine F :=
      (Submodule.Quotient.mk_eq_zero _).mp heq
    rcases (OrthogonalCover.binary_scalar_iff _).mp hs with heq | heq
    · exact hx1 (congrArg Subtype.val (b.map_eq_one_iff.mp heq))
    · have hh : xi = zi := b.injective
        (heq.trans (congrArg Multiplicative.toAdd (b.apply_symm_apply _)).symm)
      exact hxz ((congrArg Subtype.val hh).trans hz0eq)
  obtain ⟨g, hg⟩ := OrthogonalCover.binary_orbit_pair hvn hxn
  obtain ⟨l, rfl⟩ := hsurj g
  refine ⟨l, L.le_normalizer l.property, ?_⟩
  intro t ht
  apply mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  have hcentral (w : E) (hw : ∀ t : T, τ t w = w) :
      t * (b.symm (Multiplicative.ofAdd w) : G) * t⁻¹ =
        (b.symm (Multiplicative.ofAdd w) : G) := by
    have hh := hσ (inclusion hTM ⟨t, ht⟩) w
    change (b.symm (Multiplicative.ofAdd (τ ⟨t, ht⟩ w)) : G) = _ at hh
    rw [hw] at hh
    exact hh.symm
  have hxcoord :
      (b.symm (Multiplicative.ofAdd (OrthogonalCover.action F
        (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) (b xi).toAdd)) : G) =
      (l : G) * x * (l : G)⁻¹ := congrArg Subtype.val (hb l xi)
  rw [← hxcoord]
  rcases hg with heq | heq
  · rw [heq]
    exact hcentral v hvT
  · rw [heq]
    apply hcentral
    intro s
    rw [map_add, hvT]
    exact congrArg (v + ·) (hσi (inclusion hTM s))

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
