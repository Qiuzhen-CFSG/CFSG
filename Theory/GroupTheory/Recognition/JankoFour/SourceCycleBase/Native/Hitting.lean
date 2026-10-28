module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.OctadOverlap
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Ovals

/-!
# Disc and oval hitting for the native trio geometry

Every trio has an octad disjoint from an octad of a prescribed sextet.
The four small seed checks are transported using the proved exhaustive
sextet-stabilizer forest. A disc or oval covers every octad of its sextet,
so it contains a trio outside the far orbital of any given trio.
The witnesses retain literal disjoint octads for the ambient Todd transport.

Source: Aschbacher–Segev (1991), (3.11.1), p.596.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Theory.SpecificGroups.SymmetricSix
open scoped Pointwise

/-- Disjointness is retained under the same actual point permutation. -/
theorem disjoint_smul_octads (g : M24) {A B : Finset (Fin 24)} (hAB : Disjoint A B) :
    Disjoint (g • A) (g • B) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨a,ha,he⟩ := Finset.mem_smul_finset.mp hv
  obtain ⟨b,hb,hf⟩ := Finset.mem_smul_finset.mp hw
  have hab := (MulAction.injective g) (he.trans hf.symm)
  exact Finset.disjoint_left.mp hAB ha (hab ▸ hb)

theorem planeOctad_transport (g : M24) {π σ : Plane} {A : Finset (Fin 24)}
    (hπ : σ.parts = g • π.parts) (hA : PlaneOctad π A) : PlaneOctad σ (g • A) := by
  obtain ⟨B,hB,C,hC,hBC,rfl⟩ := hA
  exact ⟨g • B,hπ.symm ▸ Finset.smul_mem_smul_finset hB,
    g • C,hπ.symm ▸ Finset.smul_mem_smul_finset hC,
    (MulAction.injective g).ne hBC,Finset.smul_finset_union ..⟩

private theorem root_disjoint_octad (r : Fin 4) :
    ∃ A ∈ (FarOrbit.rootLine r).parts, ∃ B, PlaneOctad standardSextet B ∧ Disjoint A B := by
  have h : ∀ r : Fin 4, ∃ j : Fin 3, ∃ a b : Fin 6,
      a ≠ b ∧ Disjoint (FarOrbit.support (FarOrbit.seedMasks (r.castLE (by decide)) j))
        (standardTetrad a ∪ standardTetrad b) := by decide +kernel
  obtain ⟨j,a,b,hab,hd⟩ := h r
  refine ⟨FarOrbit.support (FarOrbit.seedMasks (r.castLE (by decide)) j), ?_,
    standardTetrad a ∪ standardTetrad b, ?_, hd⟩
  · change FarOrbit.support _ ∈ FarOrbit.parts _
    apply Finset.mem_image.mpr
    refine ⟨_,?_,rfl⟩
    fin_cases j <;> simp [FarOrbit.maskParts]
  · refine ⟨standardTetrad a, ?_,standardTetrad b, ?_, ?_,rfl⟩
    · exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
    · exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩
    · exact (by decide : Function.Injective standardTetrad).ne hab

/-- Every trio has an octad disjoint from an octad of any prescribed sextet.
The four small seed checks extend through the already checked orbit forest. -/
theorem exists_disjoint_plane_octad (π : Plane) (l : Line) :
    ∃ A ∈ l.parts, ∃ B, PlaneOctad π B ∧ Disjoint A B := by
  have standard (m : Line) : ∃ A ∈ m.parts, ∃ B,
      PlaneOctad standardSextet B ∧ Disjoint A B := by
    obtain ⟨i,rfl⟩ := FarOrbit.entry_surjective m
    let g := (FarOrbit.exists_transport i).choose
    obtain ⟨A,hA,B,hB,hd⟩ := root_disjoint_octad (FarOrbit.row i).root
    exact ⟨(g : M24) • A,Finset.smul_mem_smul_finset hA,
      (g : M24) • B,planeOctad_transport _ g.property.symm hB,
      disjoint_smul_octads _ hd⟩
  obtain ⟨g,hg⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator π
  obtain ⟨A,hA,B,hB,hd⟩ := standard (g⁻¹ • l)
  refine ⟨g • A,?_,g • B,planeOctad_transport g hg.symm hB,disjoint_smul_octads g hd⟩
  simpa only [smulLine_parts,smul_inv_smul] using Finset.smul_mem_smul_finset (a := g) hA

/-- Disjoint octads already exclude the far relation, with the literal radical sum. -/
theorem not_delta_four_of_disjoint {l m : Line} {A B : Finset (Fin 24)}
    (hA : A ∈ l.parts) (hB : B ∈ m.parts) (hd : Disjoint A B) : ¬ Delta 4 l m := by
  obtain ⟨v,hv,he⟩ := octad_in_radicalSum_of_disjoint hA (m.octad B hB) hd
  intro ht
  have hm : B ∈ octadsInRadicalSum l m := ⟨hB,v,hv,he⟩
  change octadsInRadicalSum l m = ∅ at ht
  rw [ht] at hm
  exact hm

/-- In the dual quadrangle a disc, like an oval, covers every octad. -/
theorem disc_hits_pencil (s : Syntheme) (a : Duad) :
    ∃ t, t ∈ Polar.disc s ∧ incident a t := by decide +revert

/-- The finite source (3.11.1) hitting calculation. Its stronger conclusion
retains the disjoint octads, permitting transport without any unproved
identification of the radical orbitals. -/
theorem residue_hits_nonfar (π : Plane) (e : Fin 6 ≃ {A // A ∈ π.parts})
    (S : Finset Syntheme) (hS : Polar.Oval S ∨ ∃ s, S = Polar.disc s) (l : Line) :
    ∃ m : {m : Line // Incident m π}, residueEquiv π e m ∈ S ∧
      ∃ A ∈ l.parts, ∃ B ∈ m.val.parts, Disjoint A B := by
  obtain ⟨A,hA,B,hB,hd⟩ := exists_disjoint_plane_octad π l
  obtain ⟨a,ha⟩ := planeOctad_duad π e hB
  have hit : ∃ s, s ∈ S ∧ incident a s := by
    rcases hS with ho | ⟨s,rfl⟩
    · obtain ⟨s,hs,_⟩ := Polar.oval_hits_pencil S ho a
      exact ⟨s,hs⟩
    · exact disc_hits_pencil s a
  obtain ⟨s,hs,has⟩ := hit
  let m := (residueEquiv π e).symm s
  have hm : residueEquiv π e m = s := (residueEquiv π e).apply_symm_apply s
  refine ⟨m,hm.symm ▸ hs,A,hA,B,?_,hd⟩
  rw [←ha]
  exact (residueEquiv_incidence π e m a).mp (hm.symm ▸ has)

theorem residue_hits_not_delta_four (π : Plane) (e : Fin 6 ≃ {A // A ∈ π.parts})
    (S : Finset Syntheme) (hS : Polar.Oval S ∨ ∃ s, S = Polar.disc s) (l : Line) :
    ∃ m : {m : Line // Incident m π}, residueEquiv π e m ∈ S ∧ ¬ Delta 4 l m.val := by
  obtain ⟨m,hm,A,hA,B,hB,hd⟩ := residue_hits_nonfar π e S hS l
  exact ⟨m,hm,not_delta_four_of_disjoint hA hB hd⟩
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
