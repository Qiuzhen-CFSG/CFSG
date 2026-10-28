module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Transport

/-!
# Assembly of the initial opposite selected configuration

The two independent missing deductions are the local edge identities and the
critical-path centralizer selection. Given their outputs, the assembly
transports the moving element, the edge identities and the kernel product
with the actual conjugator. It retains the opposite frame through equality
of the full local span, keeping its original projection and markings.

This is a conditional assembly, not a constructor from CommonFacts alone.
The edge and path producers must still be proved before the selected
configuration contract, or source (4.4.1)(1), can be reported complete.
Source: Meierfrankenfeld--Stellmacher (1993), printed pp.890--891.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
open Selection
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

/-- Combine the actual edge calculation with a selected critical placement,
preserving the original ordered pair and the exact moved element. The two
substantive selection premises remain explicit. -/
theorem selectedPath_of_edgeData_and_placement {a c : Vertex R}
    (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (s : EdgeData a c) (p : PathPlacement geometry a c s.neighbor) :
    Nonempty (SelectedPath R geometry a c) := by
  have hcenter : act R p.conjugator c = p.path.walk.getVert 2 :=
    p.local_conjugator.trans p.center_eq.symm
  obtain ⟨f', hop'⟩ : ∃ f' : FrameAt p.start (p.path.walk.getVert 2),
      ¬ f'.SameOrientation := by
    rw [p.center_eq, ← p.start_image]
    obtain ⟨f', _, _, _, hop'⟩ := frame_of_local_conjugator f hop p.local_conjugator
    exact ⟨f', hop'⟩
  have hedge : (edgeCommutator R a s.neighbor).map
      (MulAut.conj p.conjugator⁻¹).toMonoidHom =
      edgeCommutator R p.start (p.path.walk.getVert 1) := by
    calc
      _ = edgeCommutator R (act R p.conjugator a)
          (act R p.conjugator s.neighbor) := by
        simp only [edgeCommutator, Z_act, Q_act, map_commutator]
      _ = _ := congrArg₂ (edgeCommutator R) p.start_image p.first_image
  refine ⟨{
    start := p.start
    endpoint := p.endpoint
    path := p.path
    conjugator := p.conjugator
    start_image := p.start_image
    center_image := hcenter
    frame := f'
    opposite := hop'
    element := (MulAut.conj p.conjugator⁻¹) s.element
    element_mem := ?_
    moving := ?_
    displacement := ?_
    edge_eq := ?_
    kernel_product := ?_
    centralizer_selection := ?_ }⟩
  · rw [← p.start_image]
    exact (s.act p.conjugator).element_mem
  · have h := (s.act p.conjugator).moving
    change ¬ ⁅zpowers ((MulAut.conj p.conjugator⁻¹) s.element),
      Q R (act R p.conjugator c)⁆ ≤ fixedCore R (act R p.conjugator c) at h
    rwa [hcenter] at h
  · have h := (s.act p.conjugator).displacement
    change ⁅zpowers ((MulAut.conj p.conjugator⁻¹) s.element), Q R (act R p.conjugator c)⁆ =
      edgeCommutator R (act R p.conjugator a) (act R p.conjugator s.neighbor) at h
    rwa [hcenter, p.start_image, p.first_image] at h
  · have h := (s.act p.conjugator).edge_eq
    change edgeCommutator R (act R p.conjugator a) (act R p.conjugator s.neighbor) =
      edgeCommutator R (act R p.conjugator c) (act R p.conjugator s.neighbor) at h
    rwa [hcenter, p.start_image, p.first_image] at h
  · have h := (s.act p.conjugator).kernel_product
    change Q R (act R p.conjugator a) ⊔ Q R (act R p.conjugator c) =
      Q R (act R p.conjugator s.neighbor) ⊓ centralizer
        (edgeCommutator R (act R p.conjugator a) (act R p.conjugator s.neighbor) :
          Set (FreeAmalgam R)) at h
    rwa [hcenter, p.start_image, p.first_image] at h
  · have h := p.centralizer_selection
    rw [hedge] at h
    exact h.trans (congrArg (Q R) p.center_eq.symm).le

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
