module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2Fusion
public import Theory.Representation.G2OrthogonalCover.BinaryFusion

/-!
# The Weyl fusion calculation on the original chosen subgroup

An actual action equivalence identifies V with the binary trace-zero Weyl
module. Its scalar identity gives the unique nontrivial fixed element z.
Structural normality makes M=N_G(L) act on V and fix z. Conjugation by M
normalizes the derived G₂ action, so uniqueness of the invariant quadratic
form makes M preserve the Weyl norm.

The original Sylow T therefore fixes a nonzero singular vector. Natural
transitivity conjugates each vector outside the scalar line to that vector
or its translate by z, both centralized by T. The common-centralizer Sylow
adjustment and N_G(T) ≤ M give M-fusion and hence global TI.

Source: Aschbacher–Smith, 12.2.16, printed p.800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource Atlas.G2.Natural
local notation "F" => ZMod 2
local notation "E" => TraceZero F
private abbrev DerivedActor := _root_.commutator (Atlas.G2.Model F)
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The reconstructed Weyl action supplies the actual Sylow-central
representatives; no model geometry or fusion callback remains. -/
theorem globalTI_of_g2_weyl_action
    {K : GroupClass} (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (a : ActionEquiv D.quotientAction (OrthogonalCover.action F)) : IsTISubgroup V := by
  let := D.elementary
  let b : V ≃* Multiplicative E :=
    D.spaceEquiv.symm.trans a.linearEquiv.toAddEquiv.toMultiplicative
  have hb (l : L) (v : V) :
      b.symm (Multiplicative.ofAdd (OrthogonalCover.action F
        (a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) (b v).toAdd)) =
      V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ v := by
    apply b.injective
    rw [b.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    let w := (D.spaceEquiv.symm v).toAdd
    have he := a.intertwines (QuotientGroup.mk' (pCore 2 L) l) w
    have hw : D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l w)) =
        V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ v := by
      apply Subtype.ext
      rw [D.spaceEquiv_apply]
      have hv : (w.val.toMul.val : G) = (v : G) :=
        (D.spaceEquiv_apply w).symm.trans
          (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
      change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = _
      rw [hv]
      rfl
    change _ = a.linearEquiv (D.spaceEquiv.symm
      (V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ v)).toAdd
    rw [←hw,D.spaceEquiv.symm_apply_apply]
    exact he.symm
  have hsurj : Function.Surjective
      (fun l : L => a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) :=
    a.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let zi := b.symm (Multiplicative.ofAdd (identity F))
  let z : G := zi.val
  have hz : z ∈ V := zi.property
  have hz1 : z ≠ 1 := by
    intro he
    have hh : zi = 1 := Subtype.ext he
    have hh' := congrArg (fun v : V => (b v).toAdd) hh
    have hi : identity F = 0 := by
      change (b (b.symm (Multiplicative.ofAdd (identity F)))).toAdd = (b 1).toAdd at hh'
      rw [b.apply_symm_apply,map_one] at hh'
      exact hh'
    exact Atlas.SplitOctonion.unit_ne_zero (congrArg Subtype.val hi)
  have hzL : z ∈ centralizer (L : Set G) := by
    intro l hl
    have he := hb ⟨l,hl⟩ zi
    rw [show (b zi).toAdd = identity F from congrArg Multiplicative.toAdd (b.apply_symm_apply _)] at he
    rw [show OrthogonalCover.action F (a.groupEquiv
      (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)) (identity F) = identity F from
      traceZeroAction_identity F _] at he
    have hc : l*z*l⁻¹ = z := (congrArg Subtype.val he).symm
    exact mul_inv_eq_iff_eq_mul.mp hc
  have hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z := by
    intro w hw hwL
    let wi : V := ⟨w,hw⟩
    have hfix : (b wi).toAdd ∈ Representation.OneCohomology.fixed
        (OrthogonalCover.action F) := by
      intro g
      obtain ⟨l,rfl⟩ := hsurj g
      have hh := hb l wi
      have hc : V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ wi = wi := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (hwL l l.property)
      rw [hc] at hh
      have hh' := congrArg (fun v : V => (b v).toAdd) hh
      rw [b.apply_symm_apply] at hh'
      exact hh'
    rw [OrthogonalCover.fixed_eq_scalarLine,OrthogonalCover.binary_scalar_iff] at hfix
    rcases hfix with he | he
    · left
      have hh : b wi = 1 := he
      exact congrArg Subtype.val (b.map_eq_one_iff.mp hh)
    · right
      have hh : b wi = b zi := he.trans (congrArg Multiplicative.toAdd (b.apply_symm_apply _)).symm
      exact congrArg Subtype.val (b.injective hh)
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rcases ((structural G T L h).2.2 V D).2.2.2 with hn | he
    · exact hn
    · exact (hz1 (mem_bot.mp (he ▸ (show z ∈ V ⊓ centralizer (L : Set G) from ⟨hz,hzL⟩)))).elim
  have hMz := normalizer_centralizes_fixed_line h D structural hz hz1 hzL hfixed
  let M := normalizer (L : Set G)
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
        (m : G)*(b.symm (Multiplicative.ofAdd v) : G)*(m : G)⁻¹ := by
    change (b.symm (b (V.normalizerMonoidHom ⟨m,hMV m.property⟩
      (b.symm (Multiplicative.ofAdd v)))) : G) = _
    rw [b.symm_apply_apply]
    rfl
  have hσi (m : M) : σ m (identity F) = identity F := by
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    rw [hσ]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hMz m.property))
  have hσn (m : M) (g : DerivedActor) : ∃ j : DerivedActor, ∀ x,
      σ m (OrthogonalCover.action F g x) = OrthogonalCover.action F j (σ m x) := by
    obtain ⟨l,rfl⟩ := hsurj g
    let l' : L := ⟨(m : G)*l*(m : G)⁻¹,(mem_normalizer_iff.mp m.property l).mp l.property⟩
    refine ⟨a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l'),?_⟩
    intro x
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    rw [hσ]
    have hh (k : L) (w : E) :
        (b.symm (Multiplicative.ofAdd (OrthogonalCover.action F
          (a.groupEquiv (QuotientGroup.mk' (pCore 2 L) k)) w)) : G) =
          (k : G)*(b.symm (Multiplicative.ofAdd w) : G)*(k : G)⁻¹ := by
      have hh := congrArg Subtype.val (hb k (b.symm (Multiplicative.ofAdd w)))
      rw [b.apply_symm_apply] at hh
      exact hh
    rw [hh,hh,hσ]
    dsimp only [l']
    group
  have hσq (m : M) (x : E) : OrthogonalCover.form F (σ m x) = OrthogonalCover.form F x :=
    OrthogonalCover.binary_form_normalized (σ m) (hσi m) (hσn m) x
  have hTM : (T : Subgroup G) ≤ M := (structural G T L h).1
  let τ := σ.comp (inclusion hTM)
  obtain ⟨v,hv,hvq,hvT⟩ := OrthogonalCover.binary_exists_fixed_singular T.isPGroup' τ
    (fun t x => hσq (inclusion hTM t) x)
  have hvn : mk F v ≠ 0 := by
    intro he
    have hs : v ∈ scalarLine F := (Submodule.Quotient.mk_eq_zero _).mp he
    rcases (OrthogonalCover.binary_scalar_iff v).mp hs with he | rfl
    · exact hv he
    · exact one_ne_zero ((OrthogonalCover.form_identity F).symm.trans hvq)
  apply globalTI_of_sylow_central_representatives h D structural hnone hNT hz hz1 hzL hfixed
  intro x hx hx1 hxz
  let xi : V := ⟨x,hx⟩
  have hxn : mk F (b xi).toAdd ≠ 0 := by
    intro he
    have hs : (b xi).toAdd ∈ scalarLine F := (Submodule.Quotient.mk_eq_zero _).mp he
    rcases (OrthogonalCover.binary_scalar_iff _).mp hs with he | he
    · exact hx1 (congrArg Subtype.val (b.map_eq_one_iff.mp he))
    · have hh : xi = zi := b.injective (he.trans (congrArg Multiplicative.toAdd (b.apply_symm_apply _)).symm)
      exact hxz (congrArg Subtype.val hh)
  obtain ⟨g,hg⟩ := OrthogonalCover.binary_orbit_pair hvn hxn
  obtain ⟨l,rfl⟩ := hsurj g
  refine ⟨l,L.le_normalizer l.property,?_⟩
  intro t ht
  apply mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  have hcentral (w : E) (hw : ∀ t : T, τ t w = w) :
      t*(b.symm (Multiplicative.ofAdd w) : G)*t⁻¹ = (b.symm (Multiplicative.ofAdd w) : G) := by
    have hh := hσ (inclusion hTM ⟨t,ht⟩) w
    change (b.symm (Multiplicative.ofAdd (τ ⟨t,ht⟩ w)) : G) = _ at hh
    rw [hw] at hh
    exact hh.symm
  have hxcoord : (b.symm (Multiplicative.ofAdd (OrthogonalCover.action F
      (a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) (b xi).toAdd)) : G) =
      (l : G)*x*(l : G)⁻¹ := congrArg Subtype.val (hb l xi)
  rw [←hxcoord]
  rcases hg with he | he
  · rw [he]
    exact hcentral v hvT
  · rw [he]
    apply hcentral
    intro s
    rw [map_add,hvT]
    exact congrArg (v + ·) (hσi (inclusion hTM s))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
