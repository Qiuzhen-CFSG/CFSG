module
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Coverage.TripleLocal
import all Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Coverage.TripleLocal
public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions.Heptad
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.KernelNormalizer

/-!
# Full normalizers of the two native E16 cores

The quintet translations fix exactly the marked triple, whose stabilizer
preserves the quintet. The heptad translation kernel recovers its seven
fixed points. Transporting the latter through the existing source marking
identifies the full normalizers with the literal intrinsic local subgroups.
These equalities retain the native M23 embeddings used in C.3.1.
Source: Aschbacher–Smith H.14.2(1–3), printed p.397; C.3.1, pp.149–151.
-/

public section
open Subgroup
namespace Sporadic.Mathieu.M23Geometry
open CommonFour ChapterHLocalActions

theorem quintet_core_normalizer :
    normalizer ((pCore 2 quintetStabilizer).map quintetStabilizer.subtype : Set M23) =
      quintetStabilizer := by
  apply le_antisymm
  · rw [quintet_core_eq, SylowTwoLocals.Coverage.marked_core_normalizer]
    exact SylowTwoLocals.Coverage.markedTriple_le_quintet
  · have h := le_normalizer_map (H := pCore 2 quintetStabilizer) quintetStabilizer.subtype
    rw [normalizer_eq_top] at h
    exact fun x hx => h ⟨⟨x,hx⟩,mem_top _,rfl⟩

theorem source_heptad_core_normalizer :
    normalizer ((pCore 2 markedHeptadStabilizer).map markedHeptadStabilizer.subtype : Set M23) =
      markedHeptadStabilizer := by
  have hm : (pCore 2 markedHeptadStabilizer).map markedHeptadStabilizer.subtype =
      heptadKernelAmbient.map (MulAut.conj sourceMarking).toMonoidHom := by
    rw [← pCore_map_iso 2 sourceStabilizerEquiv, heptad_core_eq_kernel, map_map]
    change _ = (heptadKernel.map heptadStabilizer.subtype).map _
    rw [map_map]
    rfl
  rw [hm, ← map_equiv_normalizer_eq, heptadKernelAmbient_normalizer,
    sourceMarking_stabilizer]
end Sporadic.Mathieu.M23Geometry
