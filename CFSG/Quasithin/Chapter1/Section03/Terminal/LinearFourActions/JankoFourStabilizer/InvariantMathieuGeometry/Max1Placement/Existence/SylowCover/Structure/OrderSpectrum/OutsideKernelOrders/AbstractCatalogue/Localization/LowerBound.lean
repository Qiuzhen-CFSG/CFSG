module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.RepSeeds
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.CoreSeeds
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.KernelSection

/-!
# The core forced by an outside element of the envelope

Adjoin the normal tail `<g18,g19,g20>` to a normal subgroup. Seven binary
coordinates then suffice: every representative outside the literal kernel
forces g16 into the join. The normal product decomposition lifts this to an
actual subgroup member in g16 times the tail. Eight checked conjugation
calculations recover all four core generators from that member.

This lower interval bound needs neither an order hypothesis nor elementary
abelianness. All word identities are in the universal presentation, and the
kernel comparison uses its eleven original ascending words.
Source: the relations and provenance in SylowNormalEights/source/README.md;
context Aschbacher–Smith A.3.12, pp.47–48.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
open Janko4.LocalStructure.SylowNormalEights Presentation Profiles

/-- The core is forced by one envelope element outside the literal kernel.
Neither elementary abelianness nor the cardinal hypothesis is needed here. -/
theorem core_le_of_outside_envelope_element (A : Subgroup Carrier) (hn : A.Normal)
    (x : Carrier) (hx : x ∈ A) (he : x ∈ envelope) (hout : x ∉ abstractKernel) :
    core ≤ A := by
  let _ : A.Normal := hn
  obtain ⟨n, hnx⟩ := envelope_cover x he
  obtain ⟨r, t, hrt⟩ := envelope_split n
  have hform : wordValue (repWord r) * wordValue (tailWord t) = x := by
    rw [← wordValue_append, ← hrt, hnx]
  have hrout : r.val / 4 % 2 = 1 ∨ r.val / 16 % 2 = 1 := by
    by_contra h
    apply hout
    rw [← hform]
    exact abstractKernel.mul_mem (rep_mem_kernel r h) (tail_le_kernel (tailWord_mem t))
  have hrmem : wordValue (repWord r) ∈ A ⊔ tail := by
    apply ((A ⊔ tail).mul_mem_cancel_right
      (show wordValue (tailWord t) ∈ A ⊔ tail from (le_sup_right : tail ≤ A ⊔ tail) (tailWord_mem t))).mp
    rw [hform]
    exact (le_sup_left : A ≤ A ⊔ tail) hx
  have h16 : generator 16 ∈ A ⊔ tail :=
    rep_seed (A ⊔ tail) inferInstance le_sup_right r hrout hrmem
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp h16
  obtain ⟨s, hs⟩ := tail_cover b⁻¹ (tail.inv_mem hb)
  apply core_seed A hn s
  have hae : a = generator 16 * b⁻¹ := (eq_mul_inv_iff_mul_eq).mpr hab
  simpa only [wordValue_append, wordValue_cons, wordValue_nil, mul_one, hs, ← hae] using ha

/-- The lower interval bound for every normal subgroup in the envelope. -/
theorem core_le_of_normal_in_envelope (A : Subgroup Carrier) (hn : A.Normal)
    (he : A ≤ envelope) (hout : ¬ A ≤ abstractKernel) : core ≤ A := by
  obtain ⟨x, hx, hxout⟩ := SetLike.not_le_iff_exists.mp hout
  exact core_le_of_outside_envelope_element A hn x hx (he hx) hxout

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
