module
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.BinaryExtension.CentralizerQuotient
public import Theory.Mathieu.M12.SmallParabolicPair.Centralizers

/-!
# Realizing the full M₁₂ centralizer quotient

The three-matching action on the model involution centralizer descends along
its actual marked cover map to `C_K(u)/⟨root²⟩`. Its kernel is identified with
`centralizerCore u / squareLine`, with both literal quotient maps retained.

Surjectivity of the binary coordinates lifts every model-core element up to
its central involution; the marked root square lifts that involution. Since
the ambient cover kernel lies in the actual core, this proves that the core
is the full preimage of the model core. The first isomorphism theorem then
identifies the kernel of the descended matching action. Transporting the
actual cubic conjugation identifies its fixed subgroup with the ambient
center image, and the existing central-class lift supplies the extra
involution. No vanishing square form, splitting or retraction is assumed.

Source: Aschbacher–Smith, I.2.2(5), printed p.412 / PDF p.423.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
namespace MarkedSquareCoordinates
variable {K : Type*} [Group K] {u : K}
variable {e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12}
variable {m : Sporadic.Mathieu.M12SmallPair.CoverOrbitData}
variable (d : MarkedSquareCoordinates e u m)
namespace Realization
open Sporadic.Mathieu.M12SmallPair

def coverMap : K →* Sporadic.Mathieu.M12 :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center K))

@[simp] theorem coverMap_eq_one (x : K) : coverMap (e := e) x = 1 ↔ x ∈ center K := by
  change e (QuotientGroup.mk' (center K) x) = 1 ↔ _
  rw [e.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

def coreMap : centralizerCore u →* core :=
  ((coverMap (e := e)).comp (centralizerCore u).subtype).codRestrict _ d.core_image

theorem coreMap_coordinates (r : centralizerCore u) :
    m.coordinates (coreMap d r) = d.coordinates r := d.coordinate_compatibility r

theorem root_square_image : coverMap (e := e) ((d.root : K) ^ 2) = z := by
  change e (QuotientGroup.mk' (center K) ((d.root : K) ^ 2)) = z
  rw [d.toSquareCoordinates.root_square_mark, d.quotient_mark]

/-- Lift the binary coordinates, then correct by the lifted central involution. -/
theorem coreMap_surjective : Function.Surjective (coreMap d) := by
  intro q
  obtain ⟨r, hr⟩ := d.coordinates_surjective (m.coordinates q)
  have hk : q * (coreMap d r)⁻¹ ∈ center core := by
    rw [← m.coordinates_ker, MonoidHom.mem_ker, map_mul, map_inv,
      coreMap_coordinates, hr, mul_inv_cancel]
  rcases (core_center_mem _).mp hk with h | h
  · refine ⟨r, ?_⟩
    apply Subtype.ext
    exact (mul_inv_eq_one.mp h).symm
  · refine ⟨d.root ^ 2 * r, ?_⟩
    apply Subtype.ext
    change coverMap (e := e) (((d.root : K) ^ 2) * (r : K)) = (q : Sporadic.Mathieu.M12)
    rw [map_mul, root_square_image]
    exact (eq_mul_inv_iff_mul_eq.mp h.symm)

include d in
/-- The actual core is the full preimage, including the ambient cover kernel. -/
theorem core_preimage : centralizerCore u = core.comap (coverMap (e := e)) := by
  apply le_antisymm
  · intro x hx
    exact d.core_image ⟨x, hx⟩
  · intro x hx
    obtain ⟨r, hr⟩ := coreMap_surjective d ⟨coverMap (e := e) x,hx⟩
    have he : coverMap (e := e) (r : K) = coverMap (e := e) x := congrArg Subtype.val hr
    have hz : x * (r : K)⁻¹ ∈ center K := by
      rw [← coverMap_eq_one, map_mul, map_inv, he, mul_inv_cancel]
    have hm := (centralizerCore u).mul_mem (d.ambient_center_le hz) r.property
    simpa only [inv_mul_cancel_right] using hm

/-- The marked map from the literal centralizer onto the actual model centralizer. -/
def centralizerMap : centralizer ({u} : Set K) →* firstParabolic :=
  ((coverMap (e := e)).comp (centralizer ({u} : Set K)).subtype).codRestrict _ (by
    intro x
    rw [← d.centralizer_image]
    exact mem_map.mpr ⟨x, x.property, rfl⟩)

theorem centralizerMap_surjective : Function.Surjective (centralizerMap d) := by
  intro x
  have hx : (x : Sporadic.Mathieu.M12) ∈
      (centralizer ({u} : Set K)).map (coverMap (e := e)) := by
    simpa only [coverMap, d.centralizer_image] using x.property
  obtain ⟨y, hy, he⟩ := hx
  exact ⟨⟨y, hy⟩, Subtype.ext he⟩

def matchingMap : centralizer ({u} : Set K) →* Equiv.Perm (Fin 3) :=
  FirstCore.matchingQuotient.comp (centralizerMap d)

theorem matchingMap_surjective : Function.Surjective (matchingMap d) :=
  FirstCore.matchingQuotient_surjective.comp (centralizerMap_surjective d)

theorem matchingMap_eq_one (x : centralizer ({u} : Set K)) :
    matchingMap d x = 1 ↔ (x : K) ∈ centralizerCore u := by
  change FirstCore.matchingQuotient (centralizerMap d x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, ← FirstCore.core_eq_matching_ker, core_preimage d]
  rfl

theorem line_le_matching_ker : d.centralizerLine ≤ (matchingMap d).ker := by
  apply zpowers_le.mpr
  exact (matchingMap_eq_one d _).mpr (d.root ^ 2).property

/-- The required S₃ quotient is the descended three-matching action. -/
def projection : d.BinaryCentralizer →* Equiv.Perm (Fin 3) :=
  QuotientGroup.lift d.centralizerLine (matchingMap d) (line_le_matching_ker d)

@[simp] theorem projection_mk (x : centralizer ({u} : Set K)) :
    projection d (QuotientGroup.mk' d.centralizerLine x) = matchingMap d x := rfl

theorem projection_surjective : Function.Surjective (projection d) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (matchingMap_surjective d) _

def coreToKernel : centralizerCore u →* (projection d).ker :=
  ((QuotientGroup.mk' d.centralizerLine).comp d.coreToCentralizer).codRestrict _ (by
    intro r
    exact (matchingMap_eq_one d _).mpr r.property)

@[simp] theorem coreToKernel_apply (r : centralizerCore u) :
    (coreToKernel d r : d.BinaryCentralizer) =
      QuotientGroup.mk' d.centralizerLine (d.coreToCentralizer r) := rfl

theorem coreToKernel_surjective : Function.Surjective (coreToKernel d) := by
  intro x
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective d.centralizerLine x.val
  have hm : matchingMap d c = 1 := by
    rw [← projection_mk, hc]
    exact x.property
  refine ⟨⟨c, (matchingMap_eq_one d c).mp hm⟩, ?_⟩
  exact Subtype.ext hc

theorem coreToKernel_ker : (coreToKernel d).ker = d.toSquareCoordinates.squareLine := by
  ext r
  change coreToKernel d r = 1 ↔ _
  rw [← Subtype.val_inj]
  change QuotientGroup.mk' d.centralizerLine (d.coreToCentralizer r) = 1 ↔ _
  refine (QuotientGroup.eq_one_iff (N := d.centralizerLine) (d.coreToCentralizer r)).trans ?_
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact congrArg (fun c : centralizer ({u} : Set K) => (c : K)) hn
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa only [map_zpow] using congrArg d.coreToCentralizer hn⟩

noncomputable def quotientToKernel : d.toSquareCoordinates.BinaryQuotient ≃* (projection d).ker :=
  (QuotientGroup.quotientMulEquivOfEq (coreToKernel_ker d).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (coreToKernel d) (coreToKernel_surjective d))

@[simp] theorem quotientToKernel_mk (r : centralizerCore u) :
    quotientToKernel d (QuotientGroup.mk' d.toSquareCoordinates.squareLine r) =
      coreToKernel d r := rfl

noncomputable def kernelEquiv : (projection d).ker ≃* d.toSquareCoordinates.BinaryQuotient :=
  (quotientToKernel d).symm

theorem kernelEquiv_apply (r : centralizerCore u) :
    kernelEquiv d (coreToKernel d r) = QuotientGroup.mk' d.toSquareCoordinates.squareLine r := by
  change (quotientToKernel d).symm (coreToKernel d r) = _
  rw [← quotientToKernel_mk]
  exact (quotientToKernel d).symm_apply_apply _

theorem center_le_kernel : d.centerEmbedding.range ≤ (projection d).ker := by
  rintro _ ⟨z, rfl⟩
  exact (matchingMap_eq_one d _).mpr (d.ambient_center_le z.property)

@[simp] theorem quotientToKernel_center (z : center K) :
    (quotientToKernel d (d.toSquareCoordinates.centerInjection z) : d.BinaryCentralizer) =
      d.centerEmbedding z := by
  rw [SquareCoordinates.centerInjection_apply, quotientToKernel_mk, coreToKernel_apply]
  rfl

/-- This is conjugation by the literal cubic lift on the literal kernel. -/
theorem quotientToKernel_cubic (r : d.toSquareCoordinates.BinaryQuotient) :
    (quotientToKernel d (d.quotientCubic r) : d.BinaryCentralizer) =
      QuotientGroup.mk' d.centralizerLine d.cubicInCentralizer *
        (quotientToKernel d r : d.BinaryCentralizer) *
        (QuotientGroup.mk' d.centralizerLine d.cubicInCentralizer)⁻¹ := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective d.toSquareCoordinates.squareLine r
  rw [d.quotientCubic_mk, quotientToKernel_mk, quotientToKernel_mk,
    coreToKernel_apply, coreToKernel_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact d.core_action_apply r

theorem cubic_fixed_iff (x : d.BinaryCentralizer) (hx : x ∈ (projection d).ker) :
    Commute (QuotientGroup.mk' d.centralizerLine d.cubicInCentralizer) x ↔
      x ∈ d.centerEmbedding.range := by
  constructor
  · intro hc
    let xk : (projection d).ker := ⟨x, hx⟩
    obtain ⟨r, hr⟩ := (quotientToKernel d).surjective xk
    have hrx : (quotientToKernel d r : d.BinaryCentralizer) = x := congrArg Subtype.val hr
    have hf : d.quotientCubic r = r := by
      apply (quotientToKernel d).injective
      apply Subtype.ext
      rw [quotientToKernel_cubic, hrx, hc.eq, mul_inv_cancel_right]
    have hz := (d.quotientCubic_fixed_iff r).mp hf
    rw [← d.toSquareCoordinates.centerInjection_range] at hz
    obtain ⟨z, hz⟩ := hz
    refine ⟨z, ?_⟩
    rw [← quotientToKernel_center, hz, hrx]
  · intro hx
    exact (mem_center_iff.mp (d.centerEmbedding_range_le_center hx) _)

theorem cubic_image_order :
    orderOf (projection d (QuotientGroup.mk' d.centralizerLine d.cubicInCentralizer)) = 3 := by
  apply orderOf_eq_prime
  · rw [← map_pow, ← map_pow, d.cubicInCentralizer_cube, map_one, map_one]
  · intro he
    have hm := (matchingMap_eq_one d d.cubicInCentralizer).mp he
    have h4 : (d.cubic_lift : K) ^ 4 = 1 :=
      congrArg Subtype.val (d.fourth_power ⟨d.cubic_lift, hm⟩)
    have h3 : (d.cubic_lift : K) ^ 3 = 1 :=
      congrArg Subtype.val d.cubicInCentralizer_cube
    have h1 : d.cubic_lift = 1 := by
      apply Subtype.ext
      change (d.cubic_lift : K) = 1
      simpa only [show 4 = 3 + 1 from rfl, pow_succ, h3, one_mul] using h4
    have ho := d.cubic_lift_order
    rw [h1, orderOf_one] at ho
    contradiction

theorem extra_image_order (w : centralizer ({u} : Set K))
    (hw2 : w ^ 2 = 1) (hw : (w : K) ∉ centralizerTwoResidual u) :
    orderOf (projection d (QuotientGroup.mk' d.centralizerLine w)) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, ← map_pow, hw2, map_one, map_one]
  · intro he
    have hc := (matchingMap_eq_one d w).mp he
    exact hw (map_subtype_le (pCore 2 (centralizerTwoResidual u)) hc)

end Realization

/-- Realize every field of the published centralizer-quotient contract on the
actual group, without an elementary-kernel or splitting hypothesis. -/
theorem nonempty_centralizerQuotientData (hZ : Nat.card (center K) = 2)
    (hu : orderOf u = 2) : Nonempty d.CentralizerQuotientData := by
  obtain ⟨w, hw2, hwm, hw⟩ := d.exists_extra_lift hZ hu
  exact ⟨{
    projection := Realization.projection d
    projection_surjective := Realization.projection_surjective d
    coreToKernel := Realization.coreToKernel d
    coreToKernel_apply := Realization.coreToKernel_apply d
    kernelEquiv := Realization.kernelEquiv d
    kernelEquiv_apply := Realization.kernelEquiv_apply d
    center_le_kernel := Realization.center_le_kernel d
    cubic_image_order := Realization.cubic_image_order d
    cubic_fixed_iff := Realization.cubic_fixed_iff d
    extra := w
    extra_square := hw2
    extra_mark := hwm
    extra_image_order := Realization.extra_image_order d w hw2 hw }⟩

end MarkedSquareCoordinates
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
