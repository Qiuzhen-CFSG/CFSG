module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.BinaryExtension.CubicNorm
/-!
# The literal full-centralizer quotient for the M₁₂ splitting step

The square line is central in C_K(u), so its quotient is a group. The ambient
center injects into that quotient, with central image of order two. These
facts identify the actual kernel to be split and prove that a retraction
after quotienting pulls back along the literal centralizer projection.

`CentralizerQuotientData` is the remaining structural contract: a map onto
S₃ whose kernel is the already identified core quotient, with the actual
cubic element and an involutory lift of the marked extra element. Its
existence is not assumed or asserted by this module. Its elementary-kernel
clause follows from the proved binary quotient identification.

Source: Aschbacher–Smith, I.2.2(5), printed p.412 / PDF p.423.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
variable {K : Type*} [Group K] {u : K}
namespace MarkedSquareCoordinates
variable {e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12}
variable {m : Sporadic.Mathieu.M12SmallPair.CoverOrbitData}
variable (d : MarkedSquareCoordinates e u m)

/-- Inclusion of the source core in the full centralizer. -/
def coreToCentralizer (_d : MarkedSquareCoordinates e u m) : centralizerCore u →* centralizer ({u} : Set K) :=
  inclusion ((map_subtype_le _).trans (centralizerTwoResidual_le u))

def centralizerLine : Subgroup (centralizer ({u} : Set K)) :=
  zpowers (d.coreToCentralizer (d.root ^ 2))

theorem centralizerLine_le_center :
    d.centralizerLine ≤ center (centralizer ({u} : Set K)) := by
  apply zpowers_le.mpr
  apply mem_center_iff.mpr
  intro c
  apply Subtype.ext
  exact (d.root_square_commutes c).symm.eq

instance centralizerLine_normal : d.centralizerLine.Normal := by
  constructor
  intro x hx g
  have hc := mem_center_iff.mp (d.centralizerLine_le_center hx) g
  simpa only [hc, mul_inv_cancel_right] using hx

/-- The full centralizer modulo the same square line used in the core quotient. -/
abbrev BinaryCentralizer := centralizer ({u} : Set K) ⧸ d.centralizerLine

def centerEmbedding : center K →* d.BinaryCentralizer :=
  (QuotientGroup.mk' d.centralizerLine).comp (centerToCentralizer u)

theorem centerEmbedding_injective : Function.Injective d.centerEmbedding := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro z hz
  change d.centerEmbedding z = 1 at hz
  have hm : centerToCentralizer u z ∈ d.centralizerLine :=
    (QuotientGroup.eq_one_iff _).mp hz
  obtain ⟨n,hn⟩ := hm
  change (d.coreToCentralizer (d.root ^ 2)) ^ n = centerToCentralizer u z at hn
  have hr : (⟨z,d.ambient_center_le z.property⟩ : centralizerCore u) ∈
      d.toSquareCoordinates.squareLine := by
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact congrArg (fun x : centralizer ({u} : Set K) => (x : K)) hn
  have he : d.toSquareCoordinates.centerInjection z = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hr
  change z = 1
  exact (d.toSquareCoordinates.centerInjection_injective d.noncentral)
    (he.trans d.toSquareCoordinates.centerInjection.map_one.symm)

theorem centerEmbedding_range_le_center : d.centerEmbedding.range ≤ center d.BinaryCentralizer := by
  rintro _ ⟨z,rfl⟩
  apply mem_center_iff.mpr
  intro c
  obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective d.centralizerLine c
  change QuotientGroup.mk' d.centralizerLine c *
      QuotientGroup.mk' d.centralizerLine (centerToCentralizer u z) =
    QuotientGroup.mk' d.centralizerLine (centerToCentralizer u z) *
      QuotientGroup.mk' d.centralizerLine c
  simp only [← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_center_iff.mp z.property c

theorem centerEmbedding_range_card (hZ : Nat.card (center K) = 2) :
    Nat.card d.centerEmbedding.range = 2 :=
  (Nat.card_congr (MonoidHom.ofInjective d.centerEmbedding_injective).toEquiv).symm.trans hZ

def cubicInCentralizer : centralizer ({u} : Set K) :=
  ⟨d.cubic_lift, centralizerTwoResidual_le u d.cubic_lift.property⟩

theorem cubicInCentralizer_cube : d.cubicInCentralizer ^ 3 = 1 := by
  apply Subtype.ext
  have hp := pow_orderOf_eq_one d.cubic_lift
  rw [d.cubic_lift_order] at hp
  exact congrArg (fun x : centralizerTwoResidual u => (x : K)) hp

/-- Structural realization still needed for the final splitting step. All maps
are attached to the literal centralizer and its actual core; no splitting or
retraction is an input. -/
structure CentralizerQuotientData where
  projection : d.BinaryCentralizer →* Equiv.Perm (Fin 3)
  projection_surjective : Function.Surjective projection
  coreToKernel : centralizerCore u →* projection.ker
  coreToKernel_apply : ∀ r, (coreToKernel r : d.BinaryCentralizer) =
    QuotientGroup.mk' d.centralizerLine (d.coreToCentralizer r)
  kernelEquiv : projection.ker ≃* d.toSquareCoordinates.BinaryQuotient
  kernelEquiv_apply : ∀ r, kernelEquiv (coreToKernel r) =
    QuotientGroup.mk' d.toSquareCoordinates.squareLine r
  center_le_kernel : d.centerEmbedding.range ≤ projection.ker
  cubic_image_order : orderOf (projection
    (QuotientGroup.mk' d.centralizerLine d.cubicInCentralizer)) = 3
  cubic_fixed_iff : ∀ x : d.BinaryCentralizer, x ∈ projection.ker →
    (Commute (QuotientGroup.mk' d.centralizerLine d.cubicInCentralizer) x ↔
      x ∈ d.centerEmbedding.range)
  extra : centralizer ({u} : Set K)
  extra_square : extra ^ 2 = 1
  extra_mark : e (QuotientGroup.mk' (center K) (extra : K)) = m.extra
  extra_image_order : orderOf (projection (QuotientGroup.mk' d.centralizerLine extra)) = 2

namespace CentralizerQuotientData
variable {d} (s : d.CentralizerQuotientData)

/-- The already proved elementary core identification supplies the splitting
lemma's elementary-kernel hypothesis, retaining its actual kernel. -/
theorem kernel_elementary (hq : d.quadratic = 0) : IsElementaryAbelian 2 s.projection.ker := by
  let := d.toSquareCoordinates.quotient_elementary hq
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · apply s.kernelEquiv.injective
    simp only [map_mul]
    exact mul_comm' _ _
  · intro x
    apply s.kernelEquiv.injective
    rw [map_pow, map_one]
    exact (d.toSquareCoordinates.quotient_square_eq_one_iff _).mpr (by rw [hq]; rfl)

end CentralizerQuotientData

/-- A retraction on the full quotient pulls back to precisely the source's
centralizer retraction. The kernel and the center inclusion are literal. -/
theorem centralizerRetraction_of_quotient
    (r : d.BinaryCentralizer →* d.centerEmbedding.range)
    (hr : ∀ z : d.centerEmbedding.range, r z = z) : Nonempty (CentralizerRetraction u) := by
  let eZ := MonoidHom.ofInjective d.centerEmbedding_injective
  refine ⟨⟨eZ.symm.toMonoidHom.comp (r.comp (QuotientGroup.mk' d.centralizerLine)), ?_⟩⟩
  intro z
  apply eZ.injective
  change eZ (eZ.symm (r (d.centerEmbedding z))) = eZ z
  rw [eZ.apply_symm_apply]
  exact hr (eZ z)

end MarkedSquareCoordinates
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
