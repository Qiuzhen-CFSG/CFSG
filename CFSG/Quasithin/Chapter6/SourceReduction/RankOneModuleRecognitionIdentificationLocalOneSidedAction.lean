module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalOneSided
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# The literal field-plane quotient action

For H = C_G(U), put the central subgroup U inside H and take the normal
closure of the image of the original layer in H/U. This is the image of
its actual H-conjugate span. The action kernel is precisely the relative
commutator preimage, not an abstract replacement quotient.

In the noncommuting one-sided configuration of 6.2.7, the conjugate layer
has elementary image of order four on this same quotient. This is the
A* used by the subsequent source action argument, which remains open.

Source: Aschbacher--Smith, 6.2.7, printed p.682, the opening four-group
reduction. No LocalAnalysis or later recognition theorem is used.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
variable {G : Type*} [Group G]

abbrev Centralizer (U : Subgroup G) := centralizer (U : Set G)
def point (U : Subgroup G) : Subgroup (Centralizer U) := U.subgroupOf (Centralizer U)

/-- The point subgroup is central in its full centralizer. -/
theorem point_central (U : Subgroup G) : point U ≤ center (Centralizer U) := by
  intro u hu
  apply mem_center_iff.mpr
  intro h
  apply Subtype.ext
  exact (h.property u hu).symm

instance point_normal (U : Subgroup G) : (point U).Normal := ⟨by
  intro u hu h
  have hc := mem_center_iff.mp (point_central U hu) h
  simpa only [hc, mul_inv_cancel_right] using hu⟩

abbrev Ambient (U : Subgroup G) := Centralizer U ⧸ point U
def projection (U : Subgroup G) : Centralizer U →* Ambient U := QuotientGroup.mk' (point U)
def space (B U : Subgroup G) : Subgroup (Ambient U) :=
  normalClosure ((B.subgroupOf (Centralizer U)).map (projection U) : Set (Ambient U))
instance space_normal (B U : Subgroup G) : (space B U).Normal := normalClosure_normal
def action (B U : Subgroup G) : Centralizer U →* MulAut (space B U) :=
  (MulAut.conjNormal : Ambient U →* MulAut (space B U)).comp (projection U)

/-- The image of the literal conjugate span is its normal quotient closure. -/
theorem closure_image (B U : Subgroup G) (hBH : B ≤ Centralizer U) :
    ((conjugateSpanBy B (Centralizer U)).subgroupOf (Centralizer U)).map (projection U) =
      space B U := by
  rw [← normalClosure_subgroupOf_eq_conjugateSpanBy B (Centralizer U) hBH]
  exact map_normalClosure _ (projection U) (QuotientGroup.mk'_surjective _)

/-- The exact kernel of conjugation on the original quotient closure. -/
theorem action_ker (B U : Subgroup G) (hBH : B ≤ Centralizer U) :
    (action B U).ker =
      (commutatorPreimage (Centralizer U) (conjugateSpanBy B (Centralizer U)) U).subgroupOf
        (Centralizer U) := by
  let J := conjugateSpanBy B (Centralizer U)
  have hHU : Centralizer U ≤ normalizer (U : Set G) := Subgroup.centralizer_le_normalizer _
  ext x
  rw [MonoidHom.mem_ker, action, MonoidHom.comp_apply,
    ← MonoidHom.mem_ker, MulAut.conjNormal_ker_eq_centralizer, ← closure_image B U hBH]
  constructor
  · intro hx
    apply (mem_commutatorPreimage_iff (Centralizer U) J U hHU x).mpr
    refine ⟨x.property, ?_⟩
    intro u hu
    have huH := conjugateSpanBy_le_self hBH hu
    have hc := hx _ (mem_map_of_mem (projection U)
      (show (⟨u, huH⟩ : Centralizer U) ∈ J.subgroupOf (Centralizer U) from hu))
    have he : projection U ⁅x, (⟨u, huH⟩ : Centralizer U)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc.symm
    exact (QuotientGroup.eq_one_iff (N := point U) _).mp he
  · intro hx
    have hh := (mem_commutatorPreimage_iff (Centralizer U) J U hHU x).mp hx
    rintro _ ⟨u, hu, rfl⟩
    have he : projection U ⁅x, u⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hh.2 u hu)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at he
    exact he.symm

variable [Finite G] {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- The noncommuting conjugate induces an actual elementary four-group. -/
theorem layer_image_four
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let I := (A.subgroupOf (Centralizer U)).map (action B U)
    Nat.card I = 4 ∧ IsElementaryAbelian 2 I := by
  let := h.layer_elementary
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := Centralizer U
  let J := conjugateSpanBy B H
  let K := commutatorPreimage H J U
  let f := action B U
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAH : A ≤ H := le_centralizer_iff.mpr inf_le_right
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  have hBH : B ≤ H := B.le_centralizer.trans (centralizer_le inf_le_left)
  constructor
  · rw [← relIndex_ker, action_ker B U hBH]
    have hi := relIndex_map_map_of_injective (K.subgroupOf H) (A.subgroupOf H)
      H.subtype_injective
    rw [map_subgroupOf_eq_of_le (commutatorPreimage_le H J U),
      map_subgroupOf_eq_of_le hAH] at hi
    exact hi.symm.trans (local_one_sided_quotient_kernel h hnatural hE hfactor g hBA hnon).2
  · exact IsElementaryAbelian.map _

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
