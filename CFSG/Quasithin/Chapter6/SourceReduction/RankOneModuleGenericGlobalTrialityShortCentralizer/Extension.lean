module
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Containment
public import Theory.GroupAction.TypedCosetAutomorphisms
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtension.FullNormalizer
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.CartanTransport
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Sylow

/-!
# Full-extension short-root containment with the original marking

The native short-root centralizer fixes a unique vertex of the actual
triality hexagon. The whole-middle factorization of a source extension gives
a semilinear graph action for each of its elements. An extension element
centralizing the short root preserves its native centralizer, hence fixes
that unique central vertex and belongs to the central endpoint.

The prepared application retains the same constructed extension and the
supplied reversed comparison. Its left endpoint maps the original local
short-root centralizer onto the entire extension centralizer, with an exact
root equation. This does not yet identify the ambient centralizer with its
intersection with N_G(L); that is the remaining F.4.42 argument.

Source: Aschbacher–Smith F.4.27(4)(ii) and F.4.42, printed pp.288 and295,
with the application 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates.LeviCommutators
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityShortExtension
open ChapterF.SourceCompletion.TrialityNonbinary

/-- Fixing the marked root forces an extension automorphism into its central endpoint. -/
theorem fixes_short_mem_right {m : ℕ} {hm : 0 < m} (hm2 : 1 < m)
    (E : SourceExtension m hm)
    (t : ExtensionField (binaryParameters m hm)) (ht : t ≠ 0)
    (a : MulAut (BinaryCarrier m hm)) (ha : a ∈ E.carrier)
    (hfix : a (short (binaryParameters m hm) rfl 2 t) =
      short (binaryParameters m hm) rfl 2 t) : a ∈ E.right := by
  let P := binaryParameters m hm
  let r := short P rfl 2 t
  have hfix' : a r = r := hfix
  let C := centralizer ({r} : Set (BinaryCarrier m hm))
  obtain ⟨g,d,hd,he⟩ := E.factor a ha
  have hinv (i : Node) : (parabolic P i).map d.toMonoidHom = parabolic P i := by
    have hi (x : BinaryCarrier m hm) : d x ∈ parabolic P i ↔ x ∈ parabolic P i := by
      cases i
      · exact E.middle_preserves_left (conj_injective m hm) ⟨d,hd⟩ x
      · exact E.middle_preserves_right (conj_injective m hm) ⟨d,hd⟩ x
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (hi y).mpr hy
    · intro hx
      exact ⟨d.symm x,(hi _).mp (by simpa using hx),d.apply_symm_apply x⟩
  let α := CosetGeometry.innerAutomorphismGraphIso (parabolic P) g d hinv
  let b := CosetGeometry.base (parabolic P) .central
  have hb : ∀ k ∈ C, k • b = b := by
    intro k hk
    have hkP := _root_.Triality.Standard.ShortRootCentralizer.centralizer_le_central
      m hm hm2 t ht hk
    rwa [←CosetGeometry.stabilizer_base (parabolic P) .central] at hkP
  have hfixed : ∀ k ∈ C, k • α b = α b := by
    intro k hk
    have hk' : a.symm k ∈ C := by
      apply mem_centralizer_singleton_iff.mpr
      apply a.injective
      simpa only [map_mul,a.apply_symm_apply,hfix'] using
        (mem_centralizer_singleton_iff.mp hk)
    have h := CosetGeometry.innerAutomorphismGraphIso_smul
      (parabolic P) g d hinv (a.symm k) b
    rw [←he,a.apply_symm_apply,hb _ hk'] at h
    exact h.symm
  have heq := _root_.Triality.Standard.ShortRootCentralizer.unique_centralizer_fixed_vertex
    m hm hm2 t ht (α b) hfixed
  have hgb : g • b = b := by
    have hα : α b = g • b := by
      change g • CosetGeometry.automorphismEquiv (parabolic P) d hinv b = g • b
      rw [show CosetGeometry.automorphismEquiv (parabolic P) d hinv b = b from
        CosetGeometry.automorphismEquiv_base (parabolic P) d hinv .central]
    exact hα.symm.trans heq
  have hg : g ∈ parabolic P .central := by
    rw [←CosetGeometry.stabilizer_base (parabolic P) .central]
    exact hgb
  rw [he]
  exact E.right.mul_mem ((E.conj_mem_right_iff (conj_injective m hm) g).mpr hg) hd.2

/-- The entire extension centralizer lies in the central endpoint, including outer automorphisms. -/
theorem short_centralizer_le_right {m : ℕ} {hm : 0 < m} (hm2 : 1 < m)
    (E : SourceExtension m hm)
    (t : ExtensionField (binaryParameters m hm)) (ht : t ≠ 0) :
    centralizer ({E.baseHom (short (binaryParameters m hm) rfl 2 t)} : Set E.carrier) ≤
      E.right.subgroupOf E.carrier := by
  intro a ha
  apply fixes_short_mem_right hm2 E t ht a.val a.property
  apply conj_injective m hm
  have hc := congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
  change MulAut.conj (a.val (short (binaryParameters m hm) rfl 2 t)) = _
  calc
    _ = a.val * MulAut.conj (short (binaryParameters m hm) rfl 2 t) * a.val⁻¹ := by
      ext x
      simp [MulAut.conj_apply]
    _ = MulAut.conj (short (binaryParameters m hm) rfl 2 t) := by
      change a.val * MulAut.conj (short (binaryParameters m hm) rfl 2 t) =
        MulAut.conj (short (binaryParameters m hm) rfl 2 t) * a.val at hc
      rw [hc,mul_inv_cancel_right]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityShortExtension

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open TrialityCompletionFusion
variable {G : Type*} [Group G] [Finite G]

/-- Exact root marking under the same constructed whole-normalizer comparison. -/
theorem Preparation.triality_short_extension_marker
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    let M := d.trialityNormalizerMarking h hH hp m hm e
    let t : G := (e.right.symm (shortElement P rfl)).val
    ∃ ht : t ∈ normalizer (L : Set G),
      (M.comparison.left ⟨t,ht⟩).val = MulAut.conj (short P rfl 2 1) := by
  let M := d.trialityNormalizerMarking h hH hp m hm e
  obtain ⟨v,hv,_,he,hN⟩ := d.triality_short_marker_left h hH hp m hm e
  refine ⟨hN,?_⟩
  have ht : (⟨(e.right.symm (shortElement (binaryParameters m hm) rfl)).val,hN⟩ :
      normalizer (L : Set G)) = inclusion M.left_le (e.left.symm v) := Subtype.ext he
  change (M.comparison.left _).val = _
  rw [ht,M.left_marked,e.left.apply_symm_apply,hv]

private theorem centralizer_image {X Y : Type*} [Group X] [Group Y]
    (N : Subgroup X) (f : N →* Y) (hf : Function.Injective f)
    (t : X) (ht : t ∈ N) (z : Y) (hz : f ⟨t,ht⟩ = z)
    (hc : centralizer ({z} : Set Y) ≤ f.range) :
    ((centralizer ({t} : Set X)).subgroupOf N).map f = centralizer ({z} : Set Y) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←hz,←map_mul,←map_mul]
    exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp hx))
  · intro x hx
    obtain ⟨y,rfl⟩ := hc hx
    refine ⟨y,?_,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he : y * (⟨t,ht⟩ : N) = (⟨t,ht⟩ : N) * y := hf (by
      simpa only [map_mul,hz] using mem_centralizer_singleton_iff.mp hx)
    exact congrArg Subtype.val he

/-- The original local short-root centralizer maps onto the entire centralizer
in the same full extension, with the original endpoint map. -/
theorem Preparation.triality_short_extension_centralizer_image
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    let M := d.trialityNormalizerMarking h hH hp m hm e
    let t : G := (e.right.symm (shortElement P rfl)).val
    let f := (inclusion M.extension.right_le).comp M.comparison.left.toMonoidHom
    ((centralizer ({t} : Set G)).subgroupOf (normalizer (L : Set G))).map f =
      centralizer ({M.extension.baseHom (short P rfl 2 1)} : Set M.extension.carrier) := by
  let P := binaryParameters m hm
  let M := d.trialityNormalizerMarking h hH hp m hm e
  let t : G := (e.right.symm (shortElement P rfl)).val
  let f := (inclusion M.extension.right_le).comp M.comparison.left.toMonoidHom
  obtain ⟨ht,hmark⟩ := d.triality_short_extension_marker h hH hp m hm e
  have hf : Function.Injective f :=
    (inclusion_injective M.extension.right_le).comp M.comparison.left.injective
  have hm2 := (d.triality_local_structure h hH.1.1.2 hp m hm e).2.1
  apply centralizer_image (normalizer (L : Set G)) f hf t ht
    (M.extension.baseHom (short P rfl 2 1)) (Subtype.ext hmark)
  intro x hx
  have hxR := TrialityShortExtension.short_centralizer_le_right hm2 M.extension 1 one_ne_zero hx
  refine ⟨M.comparison.left.symm ⟨x.val,hxR⟩,?_⟩
  apply Subtype.ext
  change (M.comparison.left (M.comparison.left.symm ⟨x.val,hxR⟩)).val = x.val
  exact congrArg (fun y : M.extension.right => y.val)
    (M.comparison.left.apply_symm_apply ⟨x.val,hxR⟩)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
