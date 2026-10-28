module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Transport
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The native octad–trio–sextet incidence geometry

Vertices are the 759 octads of the fixed Witt design. Lines are its actual
partitions into three disjoint octads, and planes are its actual sextets;
a point on a plane is a union of two tetrads. The native M24 action preserves
these incidences and has precisely the existing geometric stabilizers.

The graph joins disjoint octads. Native transport of ordered disjoint octads
identifies this with source collinearity. An edge has a unique trio, whose
third octad is the complement of its ends. Consequently every triangle is on
a line and, by transport of the standard flag, in an actual sextet.

Source: Aschbacher, *Sporadic Groups* (1994), §20, pp.96–99, and Exercise
13.2, p.210. This module establishes incidence and the triangle part of the
base argument; it does not assert the remaining uniqueness-system axioms.
-/

@[expose] public section

noncomputable section

open scoped Pointwise
open Sporadic.Mathieu
namespace Sporadic.Mathieu.M24LocalGeometry
open PairOvergroups

theorem octad_smul_mem (g : M24) {O : Finset (Fin 24)} (hO : O ∈ m24Blocks) :
    g • O ∈ m24Blocks := by
  have h := (mem_M24_iff g.val).mp g.property
  change g.val • O ∈ (m24Blocks : Set (Finset (Fin 24)))
  rw [← h]
  exact Set.smul_mem_smul_set hO

instance : MulAction M24 Octad where
  smul g O := ⟨g • O.val, octad_smul_mem g O.property⟩
  one_smul O := Subtype.ext (one_smul M24 O.val)
  mul_smul g h O := Subtype.ext (mul_smul g h O.val)

@[simp] theorem Octad.smul_val (g : M24) (O : Octad) :
    (g • O).val = g • O.val := rfl

@[ext] theorem Trio.ext {T U : Trio} (h : T.parts = U.parts) : T = U := by
  cases T; cases U; cases h; rfl

@[ext] theorem Sextet.ext {S T : Sextet} (h : S.parts = T.parts) : S = T := by
  cases S; cases T; cases h; rfl

private theorem disjoint_smul (g : M24) {A B : Finset (Fin 24)}
    (h : Disjoint A B) : Disjoint (g • A) (g • B) := by
  exact Finset.disjoint_left.mpr (by
    intro x hx hy
    exact Finset.disjoint_left.mp h
      (by simpa using Finset.smul_mem_smul_finset (a := g⁻¹) hx)
      (by simpa using Finset.smul_mem_smul_finset (a := g⁻¹) hy))

private theorem smul_parts_cover (g : M24) (P : Finset (Finset (Fin 24)))
    (h : P.biUnion id = Finset.univ) : (g • P).biUnion id = Finset.univ := by
  have he : (g • P).biUnion id = g • (P.biUnion id) := by
    simp only [Finset.smul_finset_def, Finset.image_biUnion, Finset.biUnion_image, id_eq]
  rw [he, h, Finset.smul_finset_univ]

/-- Transport the literal octad partition by a native Mathieu element. -/
def translateTrio (g : M24) (T : Trio) : Trio where
  parts := g • T.parts
  card := by rw [Finset.card_smul_finset, T.card]
  octad A hA := by
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact octad_smul_mem g (T.octad B hB)
  disjoint A hA B hB hne := by
    rcases Finset.mem_image.mp hA with ⟨C, hC, rfl⟩
    rcases Finset.mem_image.mp hB with ⟨D, hD, rfl⟩
    exact disjoint_smul g (T.disjoint C hC D hD (fun he => hne (congrArg (g • ·) he)))
  cover := by exact smul_parts_cover g T.parts T.cover

instance : MulAction M24 Trio where
  smul := translateTrio
  one_smul T := Trio.ext (one_smul M24 T.parts)
  mul_smul g h T := Trio.ext (mul_smul g h T.parts)

@[simp] theorem Trio.smul_parts (g : M24) (T : Trio) :
    (g • T).parts = g • T.parts := rfl

/-- Transport the literal tetrad partition by a native Mathieu element. -/
def translateSextet (g : M24) (S : Sextet) : Sextet where
  parts := g • S.parts
  card := by rw [Finset.card_smul_finset, S.card]
  tetrad A hA := by
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    rw [Finset.card_smul_finset, S.tetrad B hB]
  disjoint A hA B hB hne := by
    rcases Finset.mem_image.mp hA with ⟨C, hC, rfl⟩
    rcases Finset.mem_image.mp hB with ⟨D, hD, rfl⟩
    exact disjoint_smul g (S.disjoint C hC D hD (fun he => hne (congrArg (g • ·) he)))
  cover := by exact smul_parts_cover g S.parts S.cover
  octad A hA B hB hne := by
    rcases Finset.mem_image.mp hA with ⟨C, hC, rfl⟩
    rcases Finset.mem_image.mp hB with ⟨D, hD, rfl⟩
    rw [← Finset.smul_finset_union]
    exact octad_smul_mem g (S.octad C hC D hD (fun he => hne (congrArg (g • ·) he)))

instance : MulAction M24 Sextet where
  smul := translateSextet
  one_smul S := Sextet.ext (one_smul M24 S.parts)
  mul_smul g h S := Sextet.ext (mul_smul g h S.parts)

@[simp] theorem Sextet.smul_parts (g : M24) (S : Sextet) :
    (g • S).parts = g • S.parts := rfl

@[simp] theorem stabilizer_octad (O : Octad) :
    MulAction.stabilizer M24 O = octadStabilizer O := by
  ext g
  change g • O = O ↔ g • O.val = O.val
  exact Subtype.ext_iff

@[simp] theorem stabilizer_trio (T : Trio) :
    MulAction.stabilizer M24 T = trioStabilizer T := by
  ext g
  change g • T = T ↔ g • T.parts = T.parts
  exact ⟨congrArg Trio.parts, fun he => Trio.ext (T := g • T) (U := T) he⟩

@[simp] theorem stabilizer_sextet (S : Sextet) :
    MulAction.stabilizer M24 S = sextetStabilizer S := by
  ext g
  change g • S = S ↔ g • S.parts = S.parts
  exact ⟨congrArg Sextet.parts, fun he => Sextet.ext (S := g • S) (T := S) he⟩

namespace OctadGraph

/-- An octad is incident with a trio when it is one of its three parts. -/
def OnLine (O : Octad) (T : Trio) : Prop := O.val ∈ T.parts

/-- An octad is incident with a sextet when it is the union of two tetrads. -/
def OnPlane (O : Octad) (S : Sextet) : Prop :=
  ∃ A ∈ S.parts, ∃ B ∈ S.parts, A ≠ B ∧ O.val = A ∪ B

/-- All three octads of the trio are incident with the sextet. -/
def LineOnPlane (T : Trio) (S : Sextet) : Prop :=
  ∀ O : Octad, OnLine O T → OnPlane O S

@[simp] theorem onLine_smul_iff (g : M24) (O : Octad) (T : Trio) :
    OnLine (g • O) (g • T) ↔ OnLine O T :=
  Finset.smul_mem_smul_finset_iff g

theorem onPlane_smul (g : M24) {O : Octad} {S : Sextet} (h : OnPlane O S) :
    OnPlane (g • O) (g • S) := by
  obtain ⟨A, hA, B, hB, hne, he⟩ := h
  refine ⟨g • A, Finset.smul_mem_smul_finset hA,
    g • B, Finset.smul_mem_smul_finset hB, ?_, ?_⟩
  · exact fun he => hne ((MulAction.injective g) he)
  · change g • O.val = g • A ∪ g • B
    rw [he, Finset.smul_finset_union]

@[simp] theorem onPlane_smul_iff (g : M24) (O : Octad) (S : Sextet) :
    OnPlane (g • O) (g • S) ↔ OnPlane O S := by
  constructor
  · intro h
    simpa using onPlane_smul g⁻¹ h
  · exact onPlane_smul g

theorem lineOnPlane_smul (g : M24) {T : Trio} {S : Sextet}
    (h : LineOnPlane T S) : LineOnPlane (g • T) (g • S) := by
  intro O hO
  have hh : OnLine (g⁻¹ • O) T := by
    simpa using (onLine_smul_iff g⁻¹ O (g • T)).mpr hO
  simpa using onPlane_smul g (h _ hh)

@[simp] theorem lineOnPlane_smul_iff (g : M24) (T : Trio) (S : Sextet) :
    LineOnPlane (g • T) (g • S) ↔ LineOnPlane T S := by
  constructor
  · intro h
    simpa using lineOnPlane_smul g⁻¹ h
  · exact lineOnPlane_smul g

/-- The native octad collinearity graph. -/
def graph : SimpleGraph Octad where
  Adj O P := Disjoint O.val P.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro O h
    have he : O.val = ∅ := disjoint_self.mp h
    have hc := m24Blocks_card O.val O.property
    rw [he, Finset.card_empty] at hc
    omega⟩

theorem preserves (g : M24) {O P : Octad} (h : graph.Adj O P) :
    graph.Adj (g • O) (g • P) := disjoint_smul g h

def first : Octad := ⟨standardTrioOctad 0, standardTrioOctad_mem 0⟩
def second : Octad := ⟨standardTrioOctad 1, standardTrioOctad_mem 1⟩

theorem first_adj_second : graph.Adj first second :=
  standardTrioOctad_disjoint 0 1 (by decide)

theorem vertex_transitive (O P : Octad) : ∃ g : M24, g • O = P := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq O P
  exact ⟨g, Subtype.ext hg⟩

theorem edge_transitive {O P : Octad} (h : graph.Adj O P) :
    ∃ g : M24, g • first = O ∧ g • second = P := by
  obtain ⟨g, hO, hP⟩ := MathieuCode.TrioCalculation.exists_smul_disjoint_octads
    O.property P.property h
  exact ⟨g, Subtype.ext hO, Subtype.ext hP⟩

theorem first_on_standardTrio : OnLine first standardTrio := by
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

theorem second_on_standardTrio : OnLine second standardTrio := by
  exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩

theorem adj_iff_common_trio (O P : Octad) :
    graph.Adj O P ↔ O ≠ P ∧ ∃ T : Trio, OnLine O T ∧ OnLine P T := by
  constructor
  · intro h
    obtain ⟨g, rfl, rfl⟩ := edge_transitive h
    exact ⟨graph.ne_of_adj h, g • standardTrio,
      (onLine_smul_iff _ _ _).mpr first_on_standardTrio,
      (onLine_smul_iff _ _ _).mpr second_on_standardTrio⟩
  · rintro ⟨hne, T, hO, hP⟩
    exact T.disjoint _ hO _ hP (fun he => hne (Subtype.ext he))

/-- An octad disjoint from the two ends of an edge is their complementary octad. -/
theorem third_eq_complement {O P Q : Octad} (hOP : graph.Adj O P)
    (hOQ : graph.Adj O Q) (hPQ : graph.Adj P Q) :
    Q.val = Finset.univ \ (O.val ∪ P.val) := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
    exact ⟨fun ho => Finset.disjoint_left.mp hOQ ho hx,
      fun hp => Finset.disjoint_left.mp hPQ hp hx⟩
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_union_of_disjoint hOP, Finset.card_univ, Fintype.card_fin,
      m24Blocks_card _ O.property, m24Blocks_card _ P.property,
      m24Blocks_card _ Q.property]

/-- A line is determined by two of its distinct points, with the third retained literally. -/
theorem trio_parts_of_two {O P : Octad} (hOP : graph.Adj O P) {T : Trio}
    (hO : OnLine O T) (hP : OnLine P T) :
    T.parts = {O.val, P.val, Finset.univ \ (O.val ∪ P.val)} := by
  apply Finset.eq_of_subset_of_card_le
  · intro A hA
    by_cases hAO : A = O.val
    · simp [hAO]
    by_cases hAP : A = P.val
    · simp [hAP]
    have hthird := third_eq_complement (Q := ⟨A, T.octad A hA⟩) hOP
      (T.disjoint _ hO _ hA (Ne.symm hAO)) (T.disjoint _ hP _ hA (Ne.symm hAP))
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inr hthird)
  · have h1 := Finset.card_insert_le O.val
      {P.val, Finset.univ \ (O.val ∪ P.val)}
    have h2 := Finset.card_insert_le P.val {Finset.univ \ (O.val ∪ P.val)}
    simp only [Finset.card_singleton] at h2
    rw [T.card]
    omega

/-- Every adjacent pair belongs to exactly one actual trio. -/
theorem existsUnique_line {O P : Octad} (hOP : graph.Adj O P) :
    ∃! T : Trio, OnLine O T ∧ OnLine P T := by
  obtain ⟨T, hO, hP⟩ := ((adj_iff_common_trio O P).mp hOP).2
  refine ⟨T, ⟨hO, hP⟩, ?_⟩
  intro U hU
  exact Trio.ext ((trio_parts_of_two hOP hU.1 hU.2).trans
    (trio_parts_of_two hOP hO hP).symm)

/-- Every triangle lies on the unique line through any of its edges. -/
theorem triangle_on_line {O P Q : Octad} (hOP : graph.Adj O P)
    (hPQ : graph.Adj P Q) (hQO : graph.Adj Q O) :
    ∃ T : Trio, OnLine O T ∧ OnLine P T ∧ OnLine Q T := by
  obtain ⟨T, hO, hP⟩ := ((adj_iff_common_trio O P).mp hOP).2
  refine ⟨T, hO, hP, ?_⟩
  change Q.val ∈ T.parts
  rw [trio_parts_of_two hOP hO hP, third_eq_complement hOP hQO.symm hPQ]
  simp

/-- The explicit standard trio is incident with the standard sextet. -/
theorem standardTrio_on_standardSextet : LineOnPlane standardTrio standardSextet := by
  intro O hO
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hO
  have hm (j : Fin 6) : standardTetrad j ∈ standardSextet.parts :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  fin_cases i
  · exact ⟨_, hm 0, _, hm 1, by decide, hi.symm⟩
  · exact ⟨_, hm 2, _, hm 3, by decide, hi.symm⟩
  · exact ⟨_, hm 4, _, hm 5, by decide, hi.symm⟩

/-- The native trio transport also transports its incident sextet. -/
theorem line_in_plane (T : Trio) : ∃ S : Sextet, LineOnPlane T S := by
  obtain ⟨g, hg⟩ := MathieuCode.TrioCalculation.exists_smul_standardTrio T
  have he : g • standardTrio = T := Trio.ext hg
  exact ⟨g • standardSextet, he ▸ lineOnPlane_smul g standardTrio_on_standardSextet⟩

/-- Triangles of the native octad graph lie in actual sextets. -/
theorem triangle_in_plane {O P Q : Octad} (hOP : graph.Adj O P)
    (hPQ : graph.Adj P Q) (hQO : graph.Adj Q O) :
    ∃ S : Sextet, OnPlane O S ∧ OnPlane P S ∧ OnPlane Q S := by
  obtain ⟨T, hO, hP, hQ⟩ := triangle_on_line hOP hPQ hQO
  obtain ⟨S, hS⟩ := line_in_plane T
  exact ⟨S, hS O hO, hS P hP, hS Q hQ⟩

end OctadGraph
end Sporadic.Mathieu.M24LocalGeometry
