module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# Retaining the opposite frame and moving element under selection

The right-coset action transports the moving element by inverse conjugation.
Both edge equalities and the kernel centralizer identity transport with it.
A change of the origin within G_c leaves the whole local span unchanged;
therefore the original projection and both natural markings can be retained
literally. In particular the opposite orientation is preserved.

These lemmas supply transport to the selected-configuration assembly. They do
not construct the initial edge identities or the critical-path selection.
Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] {R : Subgroup M}

private theorem centralizer_map {G : Type*} [Group G] (E : Subgroup G) (f : G ≃* G) :
    (centralizer (E : Set G)).map f.toMonoidHom =
      centralizer (E.map f.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
  intro y hy
  apply f.injective
  simpa only [map_mul, f.apply_symm_apply] using hx (f y) (mem_map_of_mem _ hy)

private theorem edge_act (g : FreeAmalgam R) (a t : Vertex R) :
    edgeCommutator R (act R g a) (act R g t) =
      (edgeCommutator R a t).map (MulAut.conj g⁻¹).toMonoidHom := by
  simp only [edgeCommutator, Z_act, Q_act, map_commutator]

/-- Simultaneous transport of the edge, its moving element and both kernel
factors. The right action uses inverse conjugation on every group. -/
noncomputable def EdgeData.act {a c : Vertex R} (s : EdgeData a c) (g : FreeAmalgam R) :
    EdgeData (Stellmacher.PushingUp.AmalgamGraph.act R g a)
      (Stellmacher.PushingUp.AmalgamGraph.act R g c) where
  neighbor := Stellmacher.PushingUp.AmalgamGraph.act R g s.neighbor
  adjacent_start := (adjacent_act_iff R g _ _).mpr s.adjacent_start
  adjacent_center := (adjacent_act_iff R g _ _).mpr s.adjacent_center
  element := (MulAut.conj g⁻¹).toMonoidHom s.element
  element_mem := by
    rw [Z_act]
    exact mem_map_of_mem _ s.element_mem
  moving := by
    rw [Q_act, Escape.PairingControl.FirstPairing.fixedCore_act,
      ← (MulAut.conj g⁻¹).toMonoidHom.map_zpowers, ← map_commutator,
      map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
    exact s.moving
  displacement := by
    rw [Q_act, edge_act, ← (MulAut.conj g⁻¹).toMonoidHom.map_zpowers, ← map_commutator, s.displacement]
  edge_eq := by rw [edge_act, edge_act, s.edge_eq]
  kernel_product := by
    rw [Q_act, Q_act, Q_act, edge_act, ← Subgroup.map_sup,
      ← centralizer_map, ← map_inf _ _ _ (MulAut.conj g⁻¹).injective, s.kernel_product]

/-- Rebase the frame along equality of the actual span, preserving the
projection and both markings. No new representation is chosen. -/
theorem frame_of_span_eq {a c d : Vertex R} (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (he : localZSpan R d c = localZSpan R a c) :
    ∃ f' : FrameAt d c,
      f'.sectionData.projection = f.sectionData.projection ∧
      f'.naturalU.marking = f.naturalU.marking ∧
      f'.sectionData.module_section.natural.marking =
        f.sectionData.module_section.natural.marking ∧ ¬ f'.SameOrientation := by
  have h : Nonempty (Σ s : Escape.NaturalSectionAt c (localZSpan R d c) (Z R c),
      {n : RankOnePairing.NaturalFactor s.projection ⊤
        ((U R c).subgroupOf (stabilizer R c)) ⊥ //
        s.projection = f.sectionData.projection ∧
        n.marking = f.naturalU.marking ∧
        s.module_section.natural.marking = f.sectionData.module_section.natural.marking ∧
        n.marking.symm.trans s.module_section.natural.marking ∉ MulAut.innerSubgroup SL}) := by
    rw [he]
    exact ⟨⟨f.sectionData, f.naturalU, rfl, rfl, rfl, hop⟩⟩
  obtain ⟨s, n, hπ, hU, hW, hn⟩ := h
  exact ⟨⟨s, n⟩, hπ, hU, hW, hn⟩

/-- A conjugator at c changes the seed but preserves its span and original
opposite frame, including both literal markings. -/
theorem frame_of_local_conjugator {a c : Vertex R} (f : FrameAt a c)
    (hop : ¬ f.SameOrientation) {g : FreeAmalgam R} (hg : g ∈ stabilizer R c) :
    ∃ f' : FrameAt (act R g a) c,
      f'.sectionData.projection = f.sectionData.projection ∧
      f'.naturalU.marking = f.naturalU.marking ∧
      f'.sectionData.module_section.natural.marking =
        f.sectionData.module_section.natural.marking ∧ ¬ f'.SameOrientation :=
  frame_of_span_eq f hop (CriticalCase.span_eq_of_local_conjugator hg)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
