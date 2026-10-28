module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Generation

/-!
# Normal generation by the selected element outside the fixed preimage

Pull the seed's ambient normal closure back to the finite vertex stabilizer
and intersect with V. It contains Z and the selected element outside B.
Irreducibility of the supplied single natural section, followed by residual
commutator idempotence, puts [V,Ltilde] in this pullback. Mapping down gives
the required containment in the actual quotient G_alpha/D_alpha.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(iii)--(iv) and the
first application of (1.7) in (4.3.2)(2), printed pp.882--883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {a : Vertex R} {f : FrameAt a}

namespace SelectedSeed

/-- The normal closure of the enlarged seed contains the actual moving image. -/
theorem moving_le_generated (s : SelectedSeed geometry a f)
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (ha : color R a = false) :
    quotientImage a (Vcirc R a) ≤ generated s.X := by
  let A := stabilizer R a
  let H := (V R a).subgroupOf A
  let J := H ⊓ (generated s.X).comap (quotientMap a)
  let := finite_stabilizer R a
  let := f.natural_section.normal_group
  let : J.Normal := inferInstance
  have hZJ : (Z R a).subgroupOf A ≤ J := by
    intro x hx
    exact ⟨Z_le_VBall R a 2 hx, le_normalClosure (s.Z_le_X (mem_map_of_mem _ hx))⟩
  have hnot : letI := f.natural_section.normal_kernel
      ¬ J ≤ centralizerModulo H (pResidual 2 A) ((Z R a).subgroupOf A) := by
    intro h
    have hxJ : s.element ∈ J := ⟨moving_Z_le_V s.moving s.element_mem,
      le_normalClosure (s.cyclic_le_X hb ha (mem_zpowers _))⟩
    apply s.outside
    exact ⟨s.element, h hxJ, rfl⟩
  have hm := Initial.Natural.moving_le_of_normal_not_fixed f.natural_section
    (isPPerfect_pResidual 2) ((source.V_isPGroup geometry hb a ha).comap_subtype)
    J hZJ inf_le_left hnot
  have hVS : V R a ≤ A := (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hLS : Ltilde R a ≤ A := Ltilde_le_stabilizer a
  have he : (Vcirc R a).subgroupOf A = ⁅H, pResidual 2 A⁆ := by
    rw [Vcirc, commutator_subgroupOf A _ _ hVS hLS, Ltilde_subgroupOf]
  rintro x ⟨v, hv, rfl⟩
  exact (hm (he ▸ hv)).2

end SelectedSeed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
