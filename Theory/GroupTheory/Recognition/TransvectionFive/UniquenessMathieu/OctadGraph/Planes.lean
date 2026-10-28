module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Incidence

/-!
# Sextets through short paths and quadrangles

Four-transitivity transports a standard tetrad. Unique five-set completion
then says that every octad containing a sextet tetrad is its union with one
other part. This determines the sextet from any tetrad and proves sextet
transitivity.

For noncollinear octads with a common neighbor, the remaining octad of the
first edge's trio and the Witt intersection bound force an intersection of
size four. In the sextet through that intersection, a common neighbor lies
in the three unused tetrads. The intersection bound forces it to be a union
of two of them. Hence all quadrangles are coplanar, with no finite enumeration
of squares. The last theorem includes repeated vertices for use with closed
walks.

Source: Aschbacher, *Sporadic Groups* (1994), §20, pp.96–99; 38.6 and
Exercise 13.2(3), pp.207–210. Four-generation remains a separate obligation.
-/

@[expose] public section
noncomputable section
open scoped Pointwise
open Sporadic.Mathieu
namespace Sporadic.Mathieu.M24LocalGeometry.OctadGraph
open PairOvergroups

/-- Four-transitivity transports the first standard tetrad to any four-set. -/
theorem exists_smul_standardTetrad (A : Finset (Fin 24)) (hA : A.card = 4) :
    ∃ g : M24, g • standardTetrad 0 = A := by
  let : MulAction.IsMultiplyPretransitive M24 (Fin 24) 5 := m24_isFivePretransitive
  have h4 : MulAction.IsMultiplyPretransitive M24 (Fin 24) 4 :=
    MulAction.isMultiplyPretransitive_of_le (n := 5) (by decide) (by simp)
  let e0 : Fin 4 ≃ standardTetrad 0 :=
    (Finset.equivFinOfCardEq (standardTetrad_card 0)).symm
  let eA : Fin 4 ≃ A := (Finset.equivFinOfCardEq hA).symm
  let a : Fin 4 ↪ Fin 24 := e0.toEmbedding.trans (Function.Embedding.subtype _)
  let b : Fin 4 ↪ Fin 24 := eA.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp h4) a b
  refine ⟨g, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    let i := e0.symm ⟨y,hy⟩
    have he := congrArg (fun f : Fin 4 ↪ Fin 24 => f i) hg
    have hsource : a i = y := congrArg Subtype.val (e0.apply_symm_apply ⟨y,hy⟩)
    change g • a i = b i at he
    rw [hsource] at he
    rw [he]
    exact (eA i).property
  · rw [Finset.card_smul_finset, hA, standardTetrad_card]

/-- Every tetrad occurs in an actual native sextet. -/
theorem exists_sextet_of_tetrad (A : Finset (Fin 24)) (hA : A.card = 4) :
    ∃ S : Sextet, A ∈ S.parts := by
  obtain ⟨g, hg⟩ := exists_smul_standardTetrad A hA
  refine ⟨g • standardSextet, ?_⟩
  rw [Sextet.smul_parts, ← hg]
  exact Finset.smul_mem_smul_finset
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)

/-- An octad through a sextet tetrad is its union with one other tetrad.
The five-set obtained by adding one point determines the octad. -/
theorem octad_eq_union_of_tetrad_subset (S : Sextet) {A : Finset (Fin 24)}
    (hA : A ∈ S.parts) (O : Octad) (hAO : A ⊆ O.val) :
    ∃ B ∈ S.parts, A ≠ B ∧ O.val = A ∪ B := by
  have hc : (O.val \ A).card = 4 := by
    rw [Finset.card_sdiff_of_subset hAO, m24Blocks_card _ O.property, S.tetrad A hA]
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (O.val \ A).card by omega)
  obtain ⟨hxO, hxA⟩ := Finset.mem_sdiff.mp hx
  have hxcov : x ∈ S.parts.biUnion id := by rw [S.cover]; simp
  obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.mp hxcov
  have hne : A ≠ B := by rintro rfl; exact hxA hxB
  refine ⟨B, hB, hne, ?_⟩
  apply m24WittDesign.block_eq_of_subset (S := insert x A)
  · rw [Finset.card_insert_of_notMem hxA, S.tetrad A hA]
  · simpa only [m24WittDesign_blocks] using O.property
  · simpa only [m24WittDesign_blocks] using S.octad A hA B hB hne
  · exact Finset.insert_subset hxO hAO
  · exact Finset.insert_subset (Finset.mem_union_right _ hxB) Finset.subset_union_left

/-- Octads intersecting in a tetrad lie in a common actual sextet. -/
theorem intersection_four_in_plane {O P : Octad} (h : (O.val ∩ P.val).card = 4) :
    ∃ S : Sextet, O.val ∩ P.val ∈ S.parts ∧ OnPlane O S ∧ OnPlane P S := by
  obtain ⟨S, hS⟩ := exists_sextet_of_tetrad _ h
  obtain ⟨A, hA, hneA, heA⟩ :=
    octad_eq_union_of_tetrad_subset S hS O Finset.inter_subset_left
  obtain ⟨B, hB, hneB, heB⟩ :=
    octad_eq_union_of_tetrad_subset S hS P Finset.inter_subset_right
  exact ⟨S, hS, ⟨_,hS,_,hA,hneA,heA⟩, ⟨_,hS,_,hB,hneB,heB⟩⟩

private theorem octad_inter_le_four {A B : Finset (Fin 24)}
    (hA : A ∈ m24Blocks) (hB : B ∈ m24Blocks) (hne : A ≠ B) :
    (A ∩ B).card ≤ 4 := by
  have h := m24WittDesign.inter_card_lt
    (by simpa only [m24WittDesign_blocks] using hA)
    (by simpa only [m24WittDesign_blocks] using hB) hne
  omega

/-- Three disjoint parts whose pair unions are octads contain no other octad. -/
private theorem octad_in_three_parts {A B C : Finset (Fin 24)}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hoAB : A ∪ B ∈ m24Blocks) (hoAC : A ∪ C ∈ m24Blocks)
    (hoBC : B ∪ C ∈ m24Blocks) (Q : Octad) (hQ : Q.val ⊆ A ∪ (B ∪ C)) :
    Q.val = A ∪ B ∨ Q.val = A ∪ C ∨ Q.val = B ∪ C := by
  by_contra hn
  simp only [not_or] at hn
  have h1 := octad_inter_le_four Q.property hoAB hn.1
  have h2 := octad_inter_le_four Q.property hoAC hn.2.1
  have h3 := octad_inter_le_four Q.property hoBC hn.2.2
  have hd1 : Disjoint (Q.val ∩ A) (Q.val ∩ B) := hAB.mono
    Finset.inter_subset_right Finset.inter_subset_right
  have hd2 : Disjoint (Q.val ∩ A) (Q.val ∩ C) := hAC.mono
    Finset.inter_subset_right Finset.inter_subset_right
  have hd3 : Disjoint (Q.val ∩ B) (Q.val ∩ C) := hBC.mono
    Finset.inter_subset_right Finset.inter_subset_right
  rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hd1] at h1
  rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hd2] at h2
  rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hd3] at h3
  have he : Q.val = (Q.val ∩ A) ∪ ((Q.val ∩ B) ∪ (Q.val ∩ C)) := by
    rw [← Finset.inter_union_distrib_left, ← Finset.inter_union_distrib_left]
    exact (Finset.inter_eq_left.mpr hQ).symm
  have hc := m24Blocks_card Q.val Q.property
  rw [he, Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hd1,hd2⟩),
    Finset.card_union_of_disjoint hd3] at hc
  omega

/-- Every common neighbor of two distinct octads sharing a sextet tetrad
also belongs to that sextet. -/
theorem common_neighbor_on_plane (S : Sextet) {A : Finset (Fin 24)} (hA : A ∈ S.parts)
    {O P Q : Octad} (hAO : A ⊆ O.val) (hAP : A ⊆ P.val) (hne : O ≠ P)
    (hOQ : graph.Adj O Q) (hPQ : graph.Adj P Q) : OnPlane Q S := by
  obtain ⟨B, hB, hAB, heO⟩ := octad_eq_union_of_tetrad_subset S hA O hAO
  obtain ⟨C, hC, hAC, heP⟩ := octad_eq_union_of_tetrad_subset S hA P hAP
  have hBC : B ≠ C := by
    intro he
    exact hne (Subtype.ext (heO.trans ((congrArg (A ∪ ·) he).trans heP.symm)))
  have hsub : {A,B,C} ⊆ S.parts := by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl <;> assumption
  have hcard : (S.parts \ {A,B,C}).card = 3 := by
    rw [Finset.card_sdiff_of_subset hsub, S.card]
    simp [hAB, hAC, hBC]
  obtain ⟨D,E,F,hDE,hDF,hEF,hparts⟩ := Finset.card_eq_three.mp hcard
  have hD : D ∈ S.parts := Finset.mem_sdiff.mp (by rw [hparts]; simp) |>.1
  have hE : E ∈ S.parts := Finset.mem_sdiff.mp (by rw [hparts]; simp) |>.1
  have hF : F ∈ S.parts := Finset.mem_sdiff.mp (by rw [hparts]; simp) |>.1
  have hQsub : Q.val ⊆ D ∪ (E ∪ F) := by
    intro x hx
    have hcov : x ∈ S.parts.biUnion id := by rw [S.cover]; simp
    obtain ⟨X,hX,hxX⟩ := Finset.mem_biUnion.mp hcov
    have hXA : X ≠ A := by
      rintro rfl
      exact Finset.disjoint_left.mp hOQ (hAO hxX) hx
    have hXB : X ≠ B := by
      rintro rfl
      exact Finset.disjoint_left.mp hOQ (heO ▸ Finset.mem_union_right A hxX) hx
    have hXC : X ≠ C := by
      rintro rfl
      exact Finset.disjoint_left.mp hPQ (heP ▸ Finset.mem_union_right A hxX) hx
    have hrem : X ∈ S.parts \ {A,B,C} := by
      exact Finset.mem_sdiff.mpr ⟨hX, by simp [hXA,hXB,hXC]⟩
    rw [hparts] at hrem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrem
    rcases hrem with rfl | rfl | rfl
    · exact Finset.mem_union_left _ hxX
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxX)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxX)
  rcases octad_in_three_parts
    (S.disjoint D hD E hE hDE) (S.disjoint D hD F hF hDF) (S.disjoint E hE F hF hEF)
    (S.octad D hD E hE hDE) (S.octad D hD F hF hDF) (S.octad E hE F hF hEF) Q hQsub
    with he | he | he
  · exact ⟨D,hD,E,hE,hDE,he⟩
  · exact ⟨D,hD,F,hF,hDF,he⟩
  · exact ⟨E,hE,F,hF,hEF,he⟩

/-- Distinct noncollinear octads with a common neighbor meet in a tetrad.
The common neighbor completes the first octad to a trio; the remaining
sixteen points are two octads, each meeting the other endpoint in at most four. -/
theorem common_neighbor_inter_card_four {O P Q : Octad}
    (hOP : graph.Adj O P) (hPQ : graph.Adj P Q) (hne : O ≠ Q)
    (hnadj : ¬ graph.Adj O Q) : (O.val ∩ Q.val).card = 4 := by
  obtain ⟨T, hO, hP⟩ := ((adj_iff_common_trio O P).mp hOP).2
  have hparts := trio_parts_of_two hOP hO hP
  let R : Octad := ⟨Finset.univ \ (O.val ∪ P.val), T.octad _ (by rw [hparts]; simp)⟩
  have hOR : graph.Adj O R := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_left _ hx)
  have hQR : Q.val ≠ R.val := by
    intro he
    have he' : Q = R := Subtype.ext he
    exact hnadj (he'.symm ▸ hOR)
  have hQO : Q.val ≠ O.val := fun he => hne (Subtype.ext he.symm)
  have h1 := octad_inter_le_four Q.property O.property hQO
  have h2 := octad_inter_le_four Q.property R.property hQR
  have hsub : Q.val ⊆ O.val ∪ R.val := by
    intro x hx
    by_cases hxO : x ∈ O.val
    · exact Finset.mem_union_left _ hxO
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        fun h => (Finset.mem_union.mp h).elim hxO (fun hp => Finset.disjoint_left.mp hPQ hp hx)⟩
  have he : Q.val = (Q.val ∩ O.val) ∪ (Q.val ∩ R.val) := by
    rw [← Finset.inter_union_distrib_left]
    exact (Finset.inter_eq_left.mpr hsub).symm
  have hd : Disjoint (Q.val ∩ O.val) (Q.val ∩ R.val) :=
    hOR.mono Finset.inter_subset_right Finset.inter_subset_right
  have hc := m24Blocks_card Q.val Q.property
  rw [he, Finset.card_union_of_disjoint hd] at hc
  rw [Finset.inter_comm]
  omega

/-- Every genuine quadrangle is incident with an actual sextet. The hypotheses
retain the four edges and distinguish the opposite vertices. -/
theorem square_in_plane {O P Q R : Octad}
    (hOP : graph.Adj O P) (hPQ : graph.Adj P Q)
    (hQR : graph.Adj Q R) (hRO : graph.Adj R O)
    (hOQ : O ≠ Q) (hPR : P ≠ R) :
    ∃ S : Sextet, OnPlane O S ∧ OnPlane P S ∧ OnPlane Q S ∧ OnPlane R S := by
  have hn : ¬ graph.Adj O Q := by
    intro h
    have hP := third_eq_complement h hOP hPQ.symm
    have hR := third_eq_complement h hRO.symm hQR
    exact hPR (Subtype.ext (hP.trans hR.symm))
  have hc := common_neighbor_inter_card_four hOP hPQ hOQ hn
  obtain ⟨S, hS, hSO, hSQ⟩ := intersection_four_in_plane hc
  exact ⟨S, hSO,
    common_neighbor_on_plane S hS Finset.inter_subset_left Finset.inter_subset_right
      hOQ hOP hPQ.symm, hSQ,
    common_neighbor_on_plane S hS Finset.inter_subset_left Finset.inter_subset_right
      hOQ hRO.symm hQR⟩

/-- A sextet is determined by any one of its tetrads, by unique five-set
completion and cancellation of that tetrad from the five incident octads. -/
theorem sextet_eq_of_common_tetrad {S T : Sextet} {A : Finset (Fin 24)}
    (hS : A ∈ S.parts) (hT : A ∈ T.parts) : S = T := by
  apply Sextet.ext
  apply Finset.eq_of_subset_of_card_le
  · intro B hB
    by_cases he : A = B
    · simpa only [← he] using hT
    let O : Octad := ⟨A ∪ B, S.octad A hS B hB he⟩
    obtain ⟨C, hC, hAC, hOC⟩ := octad_eq_union_of_tetrad_subset T hT O
      Finset.subset_union_left
    have hBC := congrArg (· \ A) hOC
    change (A ∪ B) \ A = (A ∪ C) \ A at hBC
    rw [Finset.union_sdiff_cancel_left (S.disjoint A hS B hB he),
      Finset.union_sdiff_cancel_left (T.disjoint A hT C hC hAC)] at hBC
    exact hBC.symm ▸ hC
  · rw [S.card, T.card]

/-- Every actual sextet is an M24 translate of the standard sextet. -/
theorem sextet_transitive (S : Sextet) : ∃ g : M24, g • standardSextet = S := by
  obtain ⟨A,hA⟩ := Finset.card_pos.mp (show 0 < S.parts.card by rw [S.card]; decide)
  obtain ⟨g,hg⟩ := exists_smul_standardTetrad A (S.tetrad A hA)
  refine ⟨g, sextet_eq_of_common_tetrad (A := A) ?_ hA⟩
  rw [← hg, Sextet.smul_parts]
  exact Finset.smul_mem_smul_finset
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)

/-- Any two-edge path is incident with a sextet, including a backtrack. -/
theorem two_step_in_plane {O P Q : Octad} (hOP : graph.Adj O P)
    (hPQ : graph.Adj P Q) :
    ∃ S : Sextet, OnPlane O S ∧ OnPlane P S ∧ OnPlane Q S := by
  by_cases he : O = Q
  · subst Q
    obtain ⟨T,hO,hP⟩ := ((adj_iff_common_trio O P).mp hOP).2
    obtain ⟨S,hS⟩ := line_in_plane T
    exact ⟨S,hS O hO,hS P hP,hS O hO⟩
  by_cases ha : graph.Adj O Q
  · exact triangle_in_plane hOP hPQ ha.symm
  obtain ⟨S,hS,hSO,hSQ⟩ :=
    intersection_four_in_plane (common_neighbor_inter_card_four hOP hPQ he ha)
  exact ⟨S,hSO,common_neighbor_on_plane S hS Finset.inter_subset_left
    Finset.inter_subset_right he hOP hPQ.symm,hSQ⟩

/-- The four vertices of every closed four-edge walk are coplanar, even when
the walk has repeated vertices. This is the form needed by walk closure. -/
theorem closed_square_in_plane {O P Q R : Octad}
    (hOP : graph.Adj O P) (hPQ : graph.Adj P Q)
    (hQR : graph.Adj Q R) (hRO : graph.Adj R O) :
    ∃ S : Sextet, OnPlane O S ∧ OnPlane P S ∧ OnPlane Q S ∧ OnPlane R S := by
  by_cases hOQ : O = Q
  · subst Q
    obtain ⟨S,hSP,hSO,hSR⟩ := two_step_in_plane hOP.symm hRO.symm
    exact ⟨S,hSO,hSP,hSO,hSR⟩
  by_cases hPR : P = R
  · subst R
    obtain ⟨S,hSO,hSP,hSQ⟩ := two_step_in_plane hOP hPQ
    exact ⟨S,hSO,hSP,hSQ,hSP⟩
  exact square_in_plane hOP hPQ hQR hRO hOQ hPR

end Sporadic.Mathieu.M24LocalGeometry.OctadGraph
