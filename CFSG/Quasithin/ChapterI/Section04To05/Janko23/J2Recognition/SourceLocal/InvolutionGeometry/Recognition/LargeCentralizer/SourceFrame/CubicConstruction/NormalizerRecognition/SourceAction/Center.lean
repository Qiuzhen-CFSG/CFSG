module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.Action
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.RootQuotient
public import Theory.SpecificGroups.MinusExtraspecial.InvolutionCentralizerFixer
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# The source root product is self-centralizing

The centralizer of the first literal core intersection is the marked
four-group E. To prove this, an element centralizing the intersection
normalizes the extraspecial core and fixes the centralizer of its noncentral
involution pointwise. The core automorphism calculation makes this action
inner; self-centralization of the generalized Fitting subgroup puts the
element back in the core, where its double centralizer is E.

Consequently C_G(R) = E = Z(R), before choosing root coordinates or assuming
any normalizer action. The earlier Frattini calculation then gives
Φ(R) = Z(R). The literal normalizer action has kernel E in any coordinates,
and C_G(E) normalizes R by preserving both core factors.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15(2), 46.2–46.3,
printed pp.29–30 and 251. No normalizer identification or splitting is used.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Matrix.PSL3Four
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

private noncomputable def coreEquiv : ambientCore D.z ≃* MinusExtraspecial.Model :=
  ((localCore D.z).equivMapOfInjective (involutionCentralizer D.z).subtype
    (involutionCentralizer D.z).subtype_injective).symm.trans D.localType.core_equiv.some

private theorem centralizer_core_le : centralizer (ambientCore D.z : Set G) ≤ ambientCore D.z := by
  intro c hc
  have hcH : c ∈ involutionCentralizer D.z :=
    mem_centralizer_singleton_iff.mpr (hc D.z HTypeAt.involution_mem_core).symm
  have hcQ : (⟨c, hcH⟩ : involutionCentralizer D.z) ∈
      centralizer (localCore D.z : Set (involutionCentralizer D.z)) := by
    intro q hq
    exact Subtype.ext (hc q (mem_map_of_mem (involutionCentralizer D.z).subtype hq))
  exact mem_map_of_mem (involutionCentralizer D.z).subtype
    (centralizer_generalizedFitting_le _ hcQ)

private theorem u_not_center :
    (⟨P.u, P.mem_core⟩ : ambientCore D.z) ∉ center (ambientCore D.z) := by
  intro hu
  have huLine : P.u ∈ zpowers D.z := D.localType.core_center_image ▸ mem_map_of_mem _ hu
  have hE : P.E ≤ zpowers D.z := sup_le le_rfl (zpowers_le.mpr huLine)
  have hcard := Nat.card_le_card_of_injective (inclusion hE) (inclusion_injective hE)
  rw [P.E_card, Nat.card_zpowers, D.localType.involution] at hcard
  omega

private theorem centralizer_leftCore_le_core : centralizer (P.leftCore : Set G) ≤ ambientCore D.z := by
  intro c hc
  have hz : D.z ∈ P.leftCore :=
    ⟨HTypeAt.involution_mem_core, mem_centralizer_singleton_iff.mpr P.commute.eq⟩
  have hcH : c ∈ involutionCentralizer D.z :=
    mem_centralizer_singleton_iff.mpr (hc D.z hz).symm
  apply MinusExtraspecial.normalizer_inf_centralizer_involutionCentralizer_le
    (ambientCore D.z) coreEquiv ⟨P.u, P.mem_core⟩
    (Subtype.ext (P.u_order ▸ pow_orderOf_eq_one P.u)) (u_not_center P)
    centralizer_core_le
  exact ⟨D.localType.normalizer_core.symm ▸ hcH, hc⟩

/-- The full ambient centralizer of the first factor is the marked four-group. -/
theorem centralizer_leftCore_eq_E : centralizer (P.leftCore : Set G) = P.E := by
  apply le_antisymm
  · intro c hc
    have hcQ := centralizer_leftCore_le_core P hc
    let q : ambientCore D.z := ⟨c, hcQ⟩
    let u : ambientCore D.z := ⟨P.u, P.mem_core⟩
    have hq : q ∈ centralizer (centralizer ({u} : Set (ambientCore D.z)) : Set (ambientCore D.z)) := by
      intro x hx
      exact Subtype.ext (hc x ⟨x.property,
        mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))⟩)
    have hqspan := MinusExtraspecial.centralizer_centralizer_involution_le
      coreEquiv u (Subtype.ext (P.u_order ▸ pow_orderOf_eq_one P.u)) (u_not_center P) hq
    have hm := mem_map_of_mem (ambientCore D.z).subtype hqspan
    rw [Subgroup.map_sup, D.localType.core_center_image, MonoidHom.map_zpowers] at hm
    exact hm
  · intro e he x hx
    obtain ⟨r, hr, rfl⟩ := P.E_le_center_image he
    exact congrArg (fun r : P.R => (r : G))
      (mem_center_iff.mp hr ⟨x, (le_sup_left : P.leftCore ≤ P.R) hx⟩)

/-- The source root product has precisely E as its ambient centralizer. -/
theorem centralizer_eq_E : centralizer (P.R : Set G) = P.E := by
  apply le_antisymm
  · exact (centralizer_le (show P.leftCore ≤ P.R from le_sup_left)).trans
      (centralizer_leftCore_eq_E P).le
  · intro e he x hx
    obtain ⟨r, hr, rfl⟩ := P.E_le_center_image he
    exact congrArg (fun r : P.R => (r : G)) (mem_center_iff.mp hr ⟨x, hx⟩)

/-- Discharges the self-centralizing field of `RootAction` unconditionally. -/
theorem selfCentralizing : centralizer (P.R : Set G) ≤ P.R :=
  (centralizer_eq_E P).le.trans P.E_le_R

/-- The marked four-group is the full intrinsic center of R. -/
theorem E_center : (center P.R).map P.R.subtype = P.E := by
  apply le_antisymm _ P.E_le_center_image
  rw [← centralizer_eq_E P]
  rintro x ⟨r, hr, rfl⟩ y hy
  exact congrArg (fun r : P.R => (r : G)) (mem_center_iff.mp hr ⟨y, hy⟩)

/-- The existing square calculation and the full center calculation agree. -/
theorem frattini_eq_center (L : LocalCensus D) : frattini P.R = center P.R := by
  apply Subgroup.map_injective P.R.subtype_injective
  rw [P.frattini_image_eq_E L, E_center P]

/-- The exact kernel in arbitrary root coordinates, without action recognition. -/
theorem conjugation_kernel (e : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) :
    (conjugation P e).ker = P.E.subgroupOf (normalizer (P.R : Set G)) := by
  rw [conjugation, MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e).injective,
    normalizerMonoidHom_ker, centralizer_eq_E P]

/-- The pointwise stabilizer of E preserves both literal core intersections. -/
theorem centralizer_E_le_normalizer_R : centralizer (P.E : Set G) ≤ normalizer (P.R : Set G) := by
  have hz : centralizer (P.E : Set G) ≤ involutionCentralizer D.z := by
    intro c hc
    exact mem_centralizer_singleton_iff.mpr (hc D.z P.z_mem_E).symm
  have hu : centralizer (P.E : Set G) ≤ involutionCentralizer P.u := by
    intro c hc
    exact mem_centralizer_singleton_iff.mpr (hc P.u P.u_mem_E).symm
  apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup P.leftCore P.rightCore)
  apply le_inf
  · apply le_trans _ inf_normalizer_le_normalizer_inf
    apply le_inf
    · rw [D.localType.normalizer_core]
      exact hz
    · exact hu.trans le_normalizer
  · apply le_trans _ inf_normalizer_le_normalizer_inf
    apply le_inf
    · rw [P.normalizer_conjugateCore]
      exact hu
    · exact hz.trans le_normalizer

/-- The literal root inclusion acts by the corresponding inner automorphism. -/
theorem conjugation_rootEmbedding (e : P.R ≃* RootNormalizerModel.Root)
    (r : RootNormalizerModel.Root) :
    conjugation P e (rootEmbedding P e r) = MulAut.conj r := by
  apply MulEquiv.ext
  intro x
  change e (e.symm r * e.symm x * (e.symm r)⁻¹) = r * x * r⁻¹
  simp only [map_mul, map_inv, e.apply_symm_apply]

/-- The inner part of the required action image is already present. -/
theorem inner_le_conjugation_range (e : P.R ≃* RootNormalizerModel.Root) :
    (MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range ≤
      (conjugation P e).range := by
  rintro a ⟨r, rfl⟩
  exact ⟨rootEmbedding P e r, conjugation_rootEmbedding P e r⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction
