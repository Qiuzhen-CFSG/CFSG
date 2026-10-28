module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.MaxElementaryOffender

/-!
# Action transport for the noncentral orthogonal Thompson alternative

The literal conjugation coordinates identify ambient centralizers with fixed
vectors of the actual action image. Applying the maximum-elementary offender
bound inside `M` gives `16 ≤ |C_V(A)| |image(A)|` without imposing ambient
normality on `V`. The fixed-center lemma also gives
`Ω₁(Z(J(T))) ∩ V = C_V(J(T))` directly from elementary maximality.

The remaining helpers transport normalizers, recover plane-stabilizer
containment from action images, and identify pointwise fixation of a fixed
space. `OrthogonalOffenderControl` specifies the separate finite-action
calculation needed by the conditional assembly; this module does not assert
that specification for the natural action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.5,
printed p.1122, and the maximum-elementary bound in B.2.4, printed pp.75–76.
The argument uses the elementary maximum-order Thompson subgroup throughout.
-/

@[expose] public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03
open scoped IsMulCommutative
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction

/-- Vectors fixed by an actual subgroup of the natural orthogonal actor. -/
def orthogonalFixedVectors (R : Subgroup OrthogonalActor) : Subgroup OrthogonalVector where
  carrier v := ∀ a ∈ R, a • v = v
  one_mem' := by intro a ha; exact smul_one a
  mul_mem' := by intro v w hv hw a ha; rw [smul_mul', hv a ha, hw a ha]
  inv_mem' := by intro v hv a ha; rw [smul_inv', hv a ha]

/-- The actors fixing the entire common fixed space pointwise. -/
def orthogonalFixedSpaceFixer (R : Subgroup OrthogonalActor) : Subgroup OrthogonalActor :=
  fixingSubgroup OrthogonalActor (orthogonalFixedVectors R : Set OrthogonalVector)

/-- The two finite-action assertions needed below. The bound is the ordinary
offender order bound, not a family-saturation assertion. Every nontrivial
elementary offender lies in `Q` and normally generates `Q` inside `P`. -/
def OrthogonalOffenderControl (P Q : Subgroup OrthogonalActor) : Prop :=
  ∀ R : Subgroup OrthogonalActor, R ≤ P → IsElementaryAbelian 2 R →
    16 ≤ Nat.card (orthogonalFixedVectors R) * Nat.card R →
      R ≤ Q ∧ (R ≠ ⊥ → ∀ N : Subgroup OrthogonalActor,
        R ≤ N → N ≤ P → P ≤ normalizer (N : Set OrthogonalActor) → Q ≤ N)

variable {G : Type*} [Group G]

theorem NaturalOrthogonalAction.image_mono {M V X Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (h : X ≤ Y) : d.image X ≤ d.image Y :=
  map_mono (subgroupOf_mono M h)

theorem NaturalOrthogonalAction.elementary_image {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M) [IsElementaryAbelian 2 X] :
    IsElementaryAbelian 2 (d.image X) := by
  let _ : IsElementaryAbelian 2 (X.subgroupOf M) := IsElementaryAbelian.subgroupOf hXM
  exact IsElementaryAbelian.map d.actor

theorem NaturalOrthogonalAction.image_normalizes {M V X Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (h : X ≤ normalizer (Y : Set G)) :
    d.image X ≤ normalizer (d.image Y : Set OrthogonalActor) := by
  exact (map_mono ((subgroupOf_mono M h).trans (Y.le_normalizer_comap M.subtype))).trans
    ((Y.subgroupOf M).le_normalizer_map d.actor)

theorem NaturalOrthogonalAction.mem_fixed_iff {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M) (v : V) :
    d.coordinates v ∈ orthogonalFixedVectors (d.image X) ↔
      (v : G) ∈ centralizer (X : Set G) := by
  constructor
  · intro h x hx
    have hv := h (d.actor ⟨x, hXM hx⟩) (mem_map_of_mem d.actor hx)
    rw [← d.compatible] at hv
    have he := congrArg Subtype.val (d.coordinates.injective hv)
    change x * (v : G) * x⁻¹ = v at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro h a ha
    obtain ⟨m, hm, rfl⟩ := ha
    rw [← d.compatible]
    congr 1
    apply Subtype.ext
    change (m : G) * (v : G) * (m : G)⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr (h m hm)

/-- The ambient centralizer is identified with the fixed vectors of its image. -/
noncomputable def NaturalOrthogonalAction.fixedEquiv {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M) :
    fixedPlane V X ≃* orthogonalFixedVectors (d.image X) where
  toFun v := ⟨d.coordinates ⟨v, v.property.1⟩,
    (d.mem_fixed_iff hXM _).mpr v.property.2⟩
  invFun w := ⟨d.coordinates.symm w, (d.coordinates.symm w).property,
    (d.mem_fixed_iff hXM _).mp (by simpa only [MulEquiv.apply_symm_apply] using w.property)⟩
  left_inv v := by
    apply Subtype.ext
    change ((d.coordinates.symm (d.coordinates ⟨v,v.property.1⟩)) : G) = v
    rw [MulEquiv.symm_apply_apply]
  right_inv w := by apply Subtype.ext; exact d.coordinates.apply_symm_apply _
  map_mul' v w := by
    apply Subtype.ext
    change d.coordinates ((⟨v,v.property.1⟩ : V) * ⟨w,w.property.1⟩) = _
    exact d.coordinates.map_mul _ _

theorem NaturalOrthogonalAction.fixedPlane_eq_of_image_eq {M V X Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M) (hYM : Y ≤ M)
    (h : d.image X = d.image Y) : fixedPlane V X = fixedPlane V Y := by
  ext v
  constructor
  · intro hv
    exact ⟨hv.1, (d.mem_fixed_iff hYM ⟨v,hv.1⟩).mp
      (h ▸ (d.mem_fixed_iff hXM ⟨v,hv.1⟩).mpr hv.2)⟩
  · intro hv
    exact ⟨hv.1, (d.mem_fixed_iff hXM ⟨v,hv.1⟩).mp
      (h.symm ▸ (d.mem_fixed_iff hYM ⟨v,hv.1⟩).mpr hv.2)⟩

private theorem elementary_max_subgroupOf [Finite G] (T M A : Subgroup G)
    (hTM : T ≤ M) (hA : A ∈ elementaryAbelianMaxSubgroups T) :
    A.subgroupOf M ∈ elementaryAbelianMaxSubgroups (T.subgroupOf M) := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  refine ⟨subgroupOf_mono M hA.1, IsElementaryAbelian.subgroupOf (hA.1.trans hTM), ?_⟩
  intro B hB hBe
  let _ : IsElementaryAbelian 2 B := hBe
  have hb := hA.2.2 (B.map M.subtype)
    (by rintro x ⟨b,hb,rfl⟩; exact hB hb) (IsElementaryAbelian.map M.subtype)
  rw [card_map_of_injective M.subtype_injective] at hb
  exact hb.trans_eq (Nat.card_congr (subgroupOfEquivOfLe (hA.1.trans hTM)).toEquiv).symm

/-- The maximum-elementary bound transported through this exact natural action. -/
theorem NaturalOrthogonalAction.maxElementary_bound [Finite G]
    (T : Sylow 2 G) {M V A : Subgroup G} (d : NaturalOrthogonalAction M V)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G)) :
    16 ≤ Nat.card (orthogonalFixedVectors (d.image A)) * Nat.card (d.image A) := by
  let _ := d.elementary
  let _ : IsElementaryAbelian 2 (V.subgroupOf M) := IsElementaryAbelian.subgroupOf hVM
  let _ : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer d.normalizes
  have hker : d.actor.ker = centralizer (V.subgroupOf M : Set M) := by
    rw [d.ker_actor]
    ext m
    constructor
    · intro h v hv
      exact Subtype.ext (h v hv)
    · intro h v hv
      exact congrArg Subtype.val (h ⟨v,hVM hv⟩ hv)
  have h := maxElementary_card_le_fixed_mul_image
    (T.subgroupOf M) (V.subgroupOf M) (A.subgroupOf M)
    (subgroupOf_mono M (d.le_sylow T hTM hVM))
    (elementary_max_subgroupOf (T : Subgroup G) M A hTM hA) d.actor hker
  have hfixed : V.subgroupOf M ⊓ centralizer (A.subgroupOf M : Set M) =
      (fixedPlane V A).subgroupOf M := by
    ext v
    constructor
    · rintro ⟨hv,hc⟩
      exact ⟨hv, fun a ha => congrArg Subtype.val (hc ⟨a,hTM (hA.1 ha)⟩ ha)⟩
    · rintro ⟨hv,hc⟩
      exact ⟨hv, fun a ha => Subtype.ext (hc a ha)⟩
  rw [hfixed, Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv,
    Nat.card_congr (@subgroupOfEquivOfLe G _ (fixedPlane V A) M (inf_le_left.trans hVM)).toEquiv,
    d.card_vector, Nat.card_congr (d.fixedEquiv (hA.1.trans hTM)).toEquiv] at h
  exact h

/-- For an elementary module, its intersection with the Thompson fixed center
is exactly its centralizer of the elementary Thompson subgroup. -/
theorem NaturalOrthogonalAction.alpha_inf_eq_fixed [Finite G]
    (T : Sylow 2 G) {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) :
    ChapterB.thompsonAlpha (T : Subgroup G) ⊓ V =
      fixedPlane V (elementaryAbelianMaxJ (T : Subgroup G)) := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let F := fixedPlane V J
  let _ : IsElementaryAbelian 2 F := d.elementary_fixedPlane J
  have hF : F ≤ ChapterB.thompsonAlpha (T : Subgroup G) :=
    elementary_centralizer_maxJ_le_omegaCenter _ F
      (inf_le_left.trans (d.le_sylow T hTM hVM)) inf_le_right
  apply le_antisymm
  · intro v hv
    exact ⟨hv.2, mem_centralizer_iff.mpr
      ((mem_omegaOneCenterAmbient_iff J v).mp hv.1).2.2⟩
  · exact le_inf hF inf_le_left

/-- The image of the specified Sylow subgroup is itself Sylow in the actor. -/
noncomputable def NaturalOrthogonalAction.imageSylow [Finite G]
    (T : Sylow 2 G) {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (hTM : (T : Subgroup G) ≤ M) : Sylow 2 OrthogonalActor :=
  (T.subtype hTM).mapSurjective d.onto

theorem NaturalOrthogonalAction.imageSylow_coe [Finite G]
    (T : Sylow 2 G) {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (hTM : (T : Subgroup G) ≤ M) :
    (d.imageSylow T hTM : Subgroup OrthogonalActor) = d.image (T : Subgroup G) := rfl

/-- Containment in a plane stabilizer can be tested in the faithful action image:
the action kernel already stabilizes every plane. -/
theorem NaturalOrthogonalAction.le_planeStabilizer_of_image_le
    (T : Sylow 2 G) {M V X : Subgroup G} (d : NaturalOrthogonalAction M V)
    (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex)
    (hXT : X ≤ (T : Subgroup G))
    (himage : d.image X ≤ d.image (planeStabilizer T (d.plane i))) :
    X ≤ planeStabilizer T (d.plane i) := by
  intro x hx
  let m : M := ⟨x, hTM (hXT hx)⟩
  obtain ⟨s, hs, he⟩ := himage (mem_map_of_mem d.actor
    (show m ∈ X.subgroupOf M from hx))
  have hker : s⁻¹ * m ∈ d.actor.ker := by
    change d.actor (s⁻¹ * m) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  rw [d.ker_actor] at hker
  have hcentral : (s : G)⁻¹ * x ∈ centralizer (V : Set G) := hker
  have hnormal : (s : G)⁻¹ * x ∈ normalizer (d.plane i : Set G) :=
    Subgroup.centralizer_le_normalizer _ (centralizer_le (d.plane_le i) hcentral)
  refine ⟨hXT hx, ?_⟩
  change x ∈ normalizer (d.plane i : Set G)
  have hsnormal : (s : G) ∈ normalizer (d.plane i : Set G) := hs.2
  have hh := (normalizer (d.plane i : Set G)).mul_mem hsnormal hnormal
  simpa only [mul_inv_cancel_left] using hh

/-- Centralizing the ambient fixed space means fixing its coordinate space. -/
theorem NaturalOrthogonalAction.image_le_fixedSpaceFixer
    {M V X Y : Subgroup G} (d : NaturalOrthogonalAction M V)
    (hYM : Y ≤ M) (h : X ≤ centralizer (fixedPlane V Y : Set G)) :
    d.image X ≤ orthogonalFixedSpaceFixer (d.image Y) := by
  rintro a ⟨m,hm,rfl⟩
  rw [orthogonalFixedSpaceFixer, mem_fixingSubgroup_iff]
  intro w hw
  let v : V := d.coordinates.symm w
  have hv : (v : G) ∈ fixedPlane V Y :=
    ⟨v.property, (d.mem_fixed_iff hYM v).mp (by
      change d.coordinates (d.coordinates.symm w) ∈ orthogonalFixedVectors (d.image Y)
      rw [MulEquiv.apply_symm_apply]
      exact hw)⟩
  have hc := h hm v hv
  have he : V.normalizerMonoidHom ⟨m,d.normalizes m.property⟩ v = v := by
    apply Subtype.ext
    change (m : G) * (v : G) * (m : G)⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr hc.symm
  have hf := d.compatible m v
  rw [he] at hf
  simpa only [v, MulEquiv.apply_symm_apply] using hf.symm

end CFSG.Quasithin.Chapter15.Section03

end
