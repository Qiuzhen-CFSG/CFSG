module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConcreteSystem.LocalGraph
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.LocalRecognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceComparison.Similarity

/-!
# Applying the local comparison to the concrete J₂ target

The target system and compatible source-to-target local maps are constructed
from their literal subgroups. This module retains the general conditional
geometry interfaces and proves recognition from a cycle base of the target.
That last theorem extends the local maps to an actual surjective homomorphism;
the independently proved source and target orders establish bijectivity.
`SourceRecognition` supplies the cycle base and exports the unconditional
simple-source J₂-type specialization.

Source: Aschbacher, *Sporadic Groups* (1994), §§37 and 47.10, pp.266–267.
The conclusion concerns the exact degree-100 ATLAS carrier.
-/

public section
namespace CFSG.Quasithin.Janko23.J2Recognition.ConcreteSystem
open Theory.GroupTheory.GraphUniquenessSystem
open Sporadic.LeechRelated.J2

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The source assembly can use the checked target without further model premises.
The remaining hypotheses concern only source geometry and its local comparison. -/
theorem recognition_of_concrete_local_geometry (D : Seed G) (L : LocalData D)
    (s : Similarity L.simpleSystem system) (he : s.IsEquivalence)
    (hsc : D.graph.TriangleSimplyConnected)
    (htri : L.simpleSystem.TrianglesInLocalOrbits) : Nonempty (G ≃* Carrier) :=
  recognition_of_local_geometry D L system s he hsc htri

open Subgroup SourceLocal
open Sporadic.LeechRelated.J2.RecognitionGeometry

/-- The image of a source reversal is the fixed ATLAS reversal. Triviality
of the actual local pointwise edge overlap proves uniqueness. -/
theorem source_reversal_image (D : Seed G)
    (s : Similarity (sourceSystem D) system) (u : (sourceSystem D).H)
    (hux : (u : G) • (sourceSystem D).x = (sourceSystem D).y)
    (huy : (u : G) • (sourceSystem D).y = (sourceSystem D).x) :
    (s.localIso u : Carrier) = t := by
  obtain ⟨hx, hy⟩ := s.map_swap u hux huy
  have htx : t⁻¹ • system.x = system.y := by
    rw [inv_smul_eq_iff, system_reversal.2.2.2.1]
  have hty : t⁻¹ • system.y = system.x := by
    rw [inv_smul_eq_iff, system_reversal.2.2.1]
  have hf : (s.localIso u : Carrier) * t⁻¹ ∈ system.H ⊓ system.edgeGroup := by
    refine ⟨system.H.mul_mem (s.localIso u).property
      (system.H.inv_mem system_reversal.1), ?_, ?_⟩
    · change ((s.localIso u : Carrier) * t⁻¹) • system.x = system.x
      rw [mul_smul, htx, hy]
    · change ((s.localIso u : Carrier) * t⁻¹) • system.y = system.y
      rw [mul_smul, hty, hx]
  have hbot : system.H ⊓ system.edgeGroup = ⊥ := by
    rw [system_local, system_edgeGroup, LocalA5.K_inf_E_eq_bot]
  exact mul_inv_eq_one.mp (hbot.le hf)

/-- The full edge-conjugation compatibility follows from the actual source
and target reversals. It is no longer a separate comparison hypothesis. -/
theorem source_similarity_isEquivalence (D : Seed G)
    (s : Similarity (sourceSystem D) system) : s.IsEquivalence := by
  obtain ⟨u, _, _, hux, huy, hc⟩ := (sourceFrame D).centralizing_reversal
  have hu := source_reversal_image D s u hux huy
  refine ⟨u, hux, huy, ?_⟩
  intro b
  have hb : (⟨(u : G) * (b : G) * (u : G)⁻¹,
      ((sourceSystem D).conj_mem_edgeGroup hux huy b.property).1⟩ :
        (sourceSystem D).vertexGroup) = ⟨b, b.property.1⟩ :=
    Subtype.ext (hc b)
  rw [hb, hu]
  exact (system_reversal.2.2.2.2
    ⟨s.vertexIso ⟨b, b.property.1⟩, (s.edge _).mp b.property⟩).symm

/-- The current source-recognition boundary: both systems and edge reversal
are constructed, leaving the compatible local maps and ambient triangle
geometry to be proved. This is not the unconditional J₂ recognition theorem. -/
theorem recognition_of_source_geometry (D : Seed G)
    (s : Similarity (sourceSystem D) system)
    (hsc : D.graph.TriangleSimplyConnected)
    (htri : (sourceSystem D).TrianglesInLocalOrbits) : Nonempty (G ≃* Carrier) :=
  recognition_of_concrete_local_geometry D (sourceFrame D).localData s
    (source_similarity_isEquivalence D s) hsc htri

/-- In the same literal recognition consumer, the internal triangle orbit
is discharged; only the external branch of 47.6(5) remains. -/
theorem recognition_of_source_external_geometry (D : Seed G)
    (s : Similarity (sourceSystem D) system)
    (hsc : D.graph.TriangleSimplyConnected)
    (hexternal : ∀ U V : D.Vertex,
      D.graph.Adj D.base U → D.graph.Adj (sourceFrame D).y U →
      D.graph.Adj D.base V → D.graph.Adj (sourceFrame D).y V →
      ¬ U.val ≤ D.X ⊔ (sourceFrame D).y.val →
      ¬ V.val ≤ D.X ⊔ (sourceFrame D).y.val →
      ∃ e : edgeStabilizer G D.base (sourceFrame D).y, (e : G) • U = V) :
    Nonempty (G ≃* Carrier) :=
  recognition_of_source_geometry D s hsc
    ((sourceFrame D).trianglesInLocalOrbits_of_external_transitivity hexternal)

/-- Both triangle orbits and the edge-reversal condition are proved for the
source seed. Only compatible local maps and source triangle contraction
remain before the actual J₂ equivalence can be assembled. -/
theorem recognition_of_source_comparison (D : Seed G)
    (s : Similarity (sourceSystem D) system)
    (hsc : D.graph.TriangleSimplyConnected) : Nonempty (G ≃* Carrier) :=
  recognition_of_source_geometry D s hsc (sourceFrame D).trianglesInLocalOrbits

/-- Literal recognition consumer for the source short-cycle route. The source
suborbit counts, diameter two, both triangle orbits and reversal compatibility
are discharged. Compatible local maps, nonedge common-neighbor connectivity,
and pentagon contraction remain explicit source obligations. -/
theorem recognition_of_source_pentagons (D : Seed G)
    (s : Similarity (sourceSystem D) system)
    (hconn : ∀ A B : D.Vertex, A ≠ B → ¬ D.graph.Adj A B →
      (D.graph.commonNeighborGraph A B).Preconnected)
    (hpentagon : ∀ (A : D.Vertex) (p : D.graph.Walk A A),
      p.length = 5 → p.TriangleHomotopy .nil) : Nonempty (G ≃* Carrier) :=
  recognition_of_source_comparison D s
    (SourceLocal.triangleSimplyConnected_of_common_connected_pentagons D hconn hpentagon)

/-- The literal source-recognition consumer with the A₅ common-neighbor
branch discharged. The single SL₂(3) connectivity premise, pentagon
contraction and compatible local maps remain to be constructed. -/
theorem recognition_of_source_one_sl2_pentagons (D : Seed G)
    (s : Similarity (sourceSystem D) system) (Y : D.Vertex)
    (hY : sl2Join D D.base Y)
    (hconn : (D.graph.commonNeighborGraph D.base Y).Preconnected)
    (hpentagon : ∀ (A : D.Vertex) (p : D.graph.Walk A A),
      p.length = 5 → p.TriangleHomotopy .nil) : Nonempty (G ≃* Carrier) :=
  recognition_of_source_comparison D s
    (SourceLocal.triangleSimplyConnected_of_one_sl2_pentagons D Y hY hconn hpentagon)

/-- The source square-contraction premise is discharged, including the
SL₂(3) branch. Only compatible local maps and contraction of five-step
source loops remain before unconditional recognition can be assembled. -/
theorem recognition_of_source_local_maps_pentagons (D : Seed G)
    (s : Similarity (sourceSystem D) system)
    (hpentagon : ∀ (A : D.Vertex) (p : D.graph.Walk A A),
      p.length = 5 → p.TriangleHomotopy .nil) : Nonempty (G ≃* Carrier) :=
  recognition_of_source_comparison D s
    (SourceLocal.triangleSimplyConnected_of_pentagons D hpentagon)

/-- The arbitrary-source localization and chord cases are discharged in the
literal recognition consumer. Only the compatible local maps and the
normalized local pentagons of 47.9 remain; this is still conditional. -/
theorem recognition_of_source_normalized_pentagons (D : Seed G)
    (s : Similarity (sourceSystem D) system)
    (hlocal : ∀ (A B C E : D.Vertex), B ≠ D.base → C ≠ D.base →
      ¬ D.graph.Adj D.base B → ¬ D.graph.Adj D.base C →
      B.val ≤ involutionCentralizer D.z → C.val ≤ involutionCentralizer D.z →
      ∀ (h0a : D.graph.Adj D.base A) (hab : D.graph.Adj A B)
        (hbc : D.graph.Adj B C) (hce : D.graph.Adj C E) (he0 : D.graph.Adj E D.base),
      SimpleGraph.Walk.TriangleHomotopy
        (.cons h0a (.cons hab (.cons hbc (.cons hce he0.toWalk)))) .nil) :
    Nonempty (G ≃* Carrier) :=
  recognition_of_source_comparison D s
    (SourceLocal.triangleSimplyConnected_of_normalized_pentagons D hlocal)

/-- All local comparison and source square/triangle-orbit conditions are
proved. Only contraction of the normalized source pentagons of 47.9 remains. -/
theorem recognition_of_normalized_pentagons (D : Seed G)
    (hlocal : ∀ (A B C E : D.Vertex), B ≠ D.base → C ≠ D.base →
      ¬ D.graph.Adj D.base B → ¬ D.graph.Adj D.base C →
      B.val ≤ involutionCentralizer D.z → C.val ≤ involutionCentralizer D.z →
      ∀ (h0a : D.graph.Adj D.base A) (hab : D.graph.Adj A B)
        (hbc : D.graph.Adj B C) (hce : D.graph.Adj C E) (he0 : D.graph.Adj E D.base),
      SimpleGraph.Walk.TriangleHomotopy
        (.cons h0a (.cons hab (.cons hbc (.cons hce he0.toWalk)))) .nil) :
    Nonempty (G ≃* Carrier) := by
  obtain ⟨s⟩ := SourceComparison.source_similarity D
  exact recognition_of_source_normalized_pentagons D s hlocal

/-- A cycle base for the actual target extends the constructed local comparison
in the reverse direction. The resulting homomorphism is surjective by the source
generation theorem; the independently proved source and target orders make it
bijective. No simplicity certification of the target is required. -/
theorem recognition_of_concrete_base (D : Seed G) (hb : system.IsBase) :
    Nonempty (G ≃* Carrier) := by
  obtain ⟨s⟩ := SourceComparison.source_similarity D
  obtain ⟨f⟩ := s.nonempty_extension_of_isEquivalence_of_isBase
    (source_similarity_isEquivalence D s) hb
  have hc : Nat.card Carrier = Nat.card G := by
    rw [ExceptionalParabolics.FirstParabolic.card_carrier, InvolutionGeometry.card_eq D]
  exact ⟨(MulEquiv.ofBijective f.hom
    ((Nat.bijective_iff_surjective_and_card f.hom).mpr ⟨f.surjective, hc⟩)).symm⟩

end CFSG.Quasithin.Janko23.J2Recognition.ConcreteSystem
