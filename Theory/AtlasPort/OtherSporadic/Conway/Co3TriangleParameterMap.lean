/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleParameterMap.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleParameters
public import Theory.AtlasPort.OtherSporadic.Conway.DisjointOctadCount
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleParameterMap.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem supportNegativeCount_eq_weight (T : Finset Omega) (s : T → Bit) :
    supportNegativeCount T s = (hammingNorm s : ℤ) := by
  rw [hammingNorm_eq_sum]
  push_cast
  rfl

theorem constantSupport_four_mem (T : Finset Omega) (hT : T.card = 2) :
    constantSupportVector 4 T ∈ leech := by
  have he : supportWord ∅ = 0 := by funext i; simp [supportWord]
  have hz : supportWord ∅ ∈ golay := he ▸ golay.zero_mem
  have h := (twoFour_mem_iff ∅ T (fun _ => 0) (fun _ => 0) hz).mpr (by simp [hT])
  convert h using 1
  funext i
  by_cases hi : i ∈ T <;> simp [twoFourVector,signedSupport,constantSupportVector,hi]

def co3SignedOctadVector (T : Finset Omega) (hT : T ∈ octads)
    (s : T → Bit) (hs : (∑ i, s i) = 0) : leech :=
  ⟨fun i => 2*signedSupport T s i,
    (twoFourFamily_properties 8 0 _ (disjointOctadVector_mem ∅
      ⟨⟨T,hT,Finset.disjoint_empty_right _⟩,⟨s,hs⟩⟩)).1⟩

def co3TriangleParameterVector (a : Omega) : (t : Fin 8) → Co3TriangleParameters a t → leech
  | 0, _ => oddMinimumVector a 0
  | 1, T => ⟨constantSupportVector 4 T.val,constantSupport_four_mem T.val (Finset.mem_powersetCard.mp T.prop).2⟩
  | 2, c => oddMinimumVector a c.val
  | 3, p => oddMinimumVector p.2.val p.1.val
  | 4, p => oddMinimumVector p.2.val p.1.val
  | 5, p => co3SignedOctadVector p.1.val (Finset.mem_filter.mp p.1.prop).1 p.2.val
      (by rw [bit_sum_eq_weight,p.2.prop.2]; decide)
  | 6, p => co3SignedOctadVector p.1.val (Finset.mem_filter.mp p.1.prop).1 p.2.val
      (by rw [bit_sum_eq_weight,p.2.prop]; decide)
  | 7, p => oddMinimumVector p.2.val p.1.val

theorem co3_triangle_parameter_shape (a : Omega) (t : Fin 8) (p : Co3TriangleParameters a t) :
    Co3TriangleShape a t (co3TriangleParameterVector a t p) := by
  fin_cases t
  · rfl
  · refine ⟨p.val,(Finset.mem_powersetCard.mp p.prop).2,?_,rfl⟩
    intro ha
    have := (Finset.mem_powersetCard.mp p.prop).1 ha
    simp at this
  · exact ⟨p.val,p.prop.1,p.prop.2,rfl⟩
  · exact ⟨p.2.val,p.1.val,p.2.prop.1,p.1.prop.1,p.1.prop.2,p.2.prop.2,rfl⟩
  · exact ⟨p.2.val,p.1.val,p.2.prop.1,p.1.prop.1,p.1.prop.2,p.2.prop.2,rfl⟩
  · refine ⟨p.1.val,(Finset.mem_filter.mp p.1.prop).1,p.2.val,
      ⟨(Finset.mem_filter.mp p.1.prop).2,p.2.prop.1⟩,?_,rfl⟩
    rw [supportNegativeCount_eq_weight,p.2.prop.2]; norm_num
  · refine ⟨p.1.val,(Finset.mem_filter.mp p.1.prop).1,p.2.val,
      (Finset.mem_filter.mp p.1.prop).2,?_,rfl⟩
    rw [supportNegativeCount_eq_weight,p.2.prop]; norm_num
  · exact ⟨p.2.val,p.1.val,p.2.prop.1,p.1.prop.1,p.1.prop.2,p.2.prop.2,rfl⟩

def co3TriangleParameterMap (a : Omega) (p : (t : Fin 8) × Co3TriangleParameters a t) : Co3Triangles a :=
  ⟨co3TriangleParameterVector a p.1 p.2,
    co3_triangle_shape_sound a p.1 _ (co3_triangle_parameter_shape a p.1 p.2)⟩

theorem co3_triangle_parameter_represents (a : Omega) (t : Fin 8) (y : leech)
    (hy : Co3TriangleShape a t y) : ∃ p : Co3TriangleParameters a t,
      co3TriangleParameterVector a t p = y := by
  fin_cases t
  · exact ⟨PUnit.unit,hy.symm⟩
  · obtain ⟨T,hT,ha,he⟩ := hy
    refine ⟨⟨T,Finset.mem_powersetCard.mpr ⟨?_,hT⟩⟩,Subtype.ext he.symm⟩
    intro i hi
    simp only [Finset.mem_erase,Finset.mem_univ,and_true]
    intro h; subst i; exact ha hi
  · obtain ⟨c,hw,ha,he⟩ := hy
    exact ⟨⟨c,hw,ha⟩,he.symm⟩
  · obtain ⟨b,c,hb,hw,ha,hc,he⟩ := hy
    exact ⟨⟨⟨c,hw,ha⟩,⟨b,hb,hc⟩⟩,he.symm⟩
  · obtain ⟨b,c,hb,hw,ha,hc,he⟩ := hy
    exact ⟨⟨⟨c,hw,ha⟩,⟨b,hb,hc⟩⟩,he.symm⟩
  · obtain ⟨T,hT,s,⟨ha,hz⟩,hn,he⟩ := hy
    have hw : hammingNorm s = 4 := by rw [supportNegativeCount_eq_weight] at hn; omega
    exact ⟨⟨⟨T,Finset.mem_filter.mpr ⟨hT,ha⟩⟩,⟨s,hz,hw⟩⟩,Subtype.ext he.symm⟩
  · obtain ⟨T,hT,s,ha,hn,he⟩ := hy
    have hw : hammingNorm s = 2 := by rw [supportNegativeCount_eq_weight] at hn; omega
    exact ⟨⟨⟨T,Finset.mem_filter.mpr ⟨hT,ha⟩⟩,⟨s,hw⟩⟩,Subtype.ext he.symm⟩
  · obtain ⟨b,c,hb,hw,ha,hc,he⟩ := hy
    exact ⟨⟨⟨c,hw,ha⟩,⟨b,hb,hc⟩⟩,he.symm⟩

theorem co3TriangleParameterMap_surjective (a : Omega) : Function.Surjective (co3TriangleParameterMap a) := by
  intro y
  obtain ⟨t,ht⟩ := co3_triangle_shape_exhaustive a y
  obtain ⟨p,hp⟩ := co3_triangle_parameter_represents a t y.val ht
  exact ⟨⟨t,p⟩,Subtype.ext hp⟩

end Atlas.Conway
