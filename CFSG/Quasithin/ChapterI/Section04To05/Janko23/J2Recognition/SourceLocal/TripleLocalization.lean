module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Triangles
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.NonadjacentInvolutions

/-!
# Simultaneous involution localization of an edge and a vertex

Every edge and every third source vertex centralize a common conjugate of
z. For a third vertex nonadjacent to either endpoint, the completed
six-coset argument supplies the involution. For triangles, both actual
setwise-edge orbits lie in a conjugate of the local A₅, whose marked
D₁₀ centralizes it. Coincident vertices use the A₅ edge fixer directly.
This avoids the incorrect A₄ identification of an inner fixer intersection.

Conjugating this involution back to z and applying Sylow conjugacy inside
C_G(z) sends the third vertex exactly to X while retaining both edge
endpoints in C_G(z). The pentagon consumer uses this normalization with
its first vertex and its opposite edge.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6(4), p.264, and the
first reduction of 47.9, p.265. Every preceding-source premise is discharged
from the original seed; local pentagon contraction is a separate obligation.
-/

public section
open Subgroup MulAction Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.TripleLocalization
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

private theorem fixer_involutions (D : Seed G) {Y : D.Vertex}
    (hY : D.graph.Adj D.base Y) {u : G}
    (hu : u ∈ edgeFixer G D.base Y) (ho : orderOf u = 2) : IsConj D.z u := by
  obtain ⟨S, hfive, hthree⟩ := InvolutionGeometry.Applications.source_prime_local D
  exact Representatives.edge_involutions_conjugate_of_earlier_source
    S hfive.root hfive.twoCentral hthree.sylow hthree.normalizer_card
    hthree.local_normalizer_card (InvolutionGeometry.card_eq D) hY hu ho

omit [IsSimpleGroup G] in
private theorem smul_le_centralizer (D : Seed G) (g t : G) (A : D.Vertex)
    (hA : A.val ≤ involutionCentralizer t) :
    (g • A).val ≤ involutionCentralizer (MulAut.conj g t) := by
  rw [D.smul_val]
  rintro _ ⟨a, ha, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  exact (map_mul (MulAut.conj g) a t).symm.trans
    ((congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (hA ha))).trans
      (map_mul (MulAut.conj g) t a))

private theorem nonedge_at_base (D : Seed G) (Y U : D.Vertex)
    (hY : D.graph.Adj D.base Y) (hne : U ≠ D.base)
    (hn : ¬ D.graph.Adj D.base U) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer t := by
  obtain ⟨S, hfive, hthree⟩ := InvolutionGeometry.Applications.source_prime_local D
  obtain ⟨R⟩ := Representatives.threePairRepresentatives_nonempty
    S hfive.root hfive.twoCentral hthree.sylow hthree.normalizer_card hthree.local_normalizer_card
  obtain ⟨H⟩ := PrimeNormalizers.centralizerCalculation_of_selectedGeometry
    (InvolutionGeometry.card_eq D) S
  let := H.quasisimple
  have hu : sl2Join D D.base U ∨ a5Join D D.base U := by
    rcases (InvolutionGeometry.Applications.fourSuborbits D).joins D.base U with he | ha | hs | hf
    · exact (hne he.symm).elim
    · exact (hn ha).elim
    · exact Or.inl hs
    · exact Or.inr hf
  exact NonadjacentInvolutions.commonInvolution_of_representatives D R
    (InvolutionGeometry.card_eq D) hthree.normalizer_card Y hY
    (fun _ ht ho => fixer_involutions D hY ht ho) H.center_eq H.centerQuotientEquiv
    (PrimeNormalizers.FiveLocal.fiveNormalizerTypes_of_selectedGeometry
      (InvolutionGeometry.card_eq D) S) U hu

private theorem nonedge (D : Seed G) (A B U : D.Vertex)
    (hAB : D.graph.Adj A B) (hne : U ≠ A) (hn : ¬ D.graph.Adj A U) :
    ∃ t : G, IsConj D.z t ∧ A.val ⊔ B.val ⊔ U.val ≤ involutionCentralizer t := by
  obtain ⟨g, rfl⟩ := D.transitive A
  have hb : D.graph.Adj D.base (g⁻¹ • B) := by
    simpa only [inv_smul_smul] using D.preserves g⁻¹ hAB
  have hne' : g⁻¹ • U ≠ D.base := by
    intro he
    apply hne
    simpa only [smul_inv_smul] using congrArg (fun V : D.Vertex => g • V) he
  have hn' : ¬ D.graph.Adj D.base (g⁻¹ • U) := by
    intro h
    exact hn (by simpa only [smul_inv_smul] using D.preserves g h)
  obtain ⟨t, ht, hle⟩ := nonedge_at_base D _ _ hb hne' hn'
  refine ⟨MulAut.conj g t, ht.trans (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
  apply sup_le (sup_le (smul_le_centralizer D g t D.base (le_sup_left.trans (le_sup_left.trans hle))) ?_) ?_
  · simpa only [smul_inv_smul] using smul_le_centralizer D g t (g⁻¹ • B)
      (le_sup_right.trans (le_sup_left.trans hle))
  · simpa only [smul_inv_smul] using smul_le_centralizer D g t (g⁻¹ • U) (le_sup_right.trans hle)

/-- Every triangle lies in the centralizer of an involution conjugate to z.
The two setwise-edge triangle orbits are retained through the local system. -/
theorem triangle (D : Seed G) (A B U : D.Vertex)
    (hAB : D.graph.Adj A B) (hBU : D.graph.Adj B U) (hUA : D.graph.Adj U A) :
    ∃ t : G, IsConj D.z t ∧ A.val ⊔ B.val ⊔ U.val ≤ involutionCentralizer t := by
  let F := sourceFrame D
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := F.B) 2
    (by rw [F.card_B]; norm_num)
  have ht2 : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hclass := fixer_involutions D F.adjacent (F.B_le t.property) ht2
  have hK : F.K ≤ involutionCentralizer (t : G) := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr (hk t t.property).symm
  obtain ⟨g, hab, hbu, hua⟩ := F.trianglesInLocalOrbits A B U hAB hBU hUA
  have ha := ((F.localData_localEdge_iff _ _).mp hab).2.1.trans hK
  have hb := ((F.localData_localEdge_iff _ _).mp hab).2.2.trans hK
  have hu := ((F.localData_localEdge_iff _ _).mp hbu).2.2.trans hK
  refine ⟨MulAut.conj g (t : G), hclass.trans (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
  apply sup_le (sup_le ?_ ?_) ?_
  · simpa only [smul_inv_smul] using smul_le_centralizer D g t (g⁻¹ • A) ha
  · simpa only [smul_inv_smul] using smul_le_centralizer D g t (g⁻¹ • B) hb
  · simpa only [smul_inv_smul] using smul_le_centralizer D g t (g⁻¹ • U) hu

private theorem edge (D : Seed G) (A B : D.Vertex) (hAB : D.graph.Adj A B) :
    ∃ t : G, IsConj D.z t ∧ A.val ⊔ B.val ≤ involutionCentralizer t := by
  obtain ⟨g, rfl⟩ := D.transitive A
  have hb : D.graph.Adj D.base (g⁻¹ • B) := by
    simpa only [inv_smul_smul] using D.preserves g⁻¹ hAB
  obtain ⟨t, ht, hle⟩ := EdgeConfigurations.commonInvolution_of_le_join D
    (g⁻¹ • B) D.base (InvolutionGeometry.Applications.edgeFixer_equiv D hb)
    (fun _ ht ho => fixer_involutions D hb ht ho) le_sup_left
  refine ⟨MulAut.conj g t, ht.trans (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
  apply sup_le (smul_le_centralizer D g t D.base (le_sup_right.trans hle))
  simpa only [smul_inv_smul] using smul_le_centralizer D g t (g⁻¹ • B)
    (le_sup_right.trans (le_sup_left.trans hle))

/-- Source 47.6(4): an edge and any third vertex have a common involution
in the distinguished source class, centralizing their actual subgroup join. -/
theorem edge_and_vertex (D : Seed G) (A B U : D.Vertex) (hAB : D.graph.Adj A B) :
    ∃ t : G, IsConj D.z t ∧ A.val ⊔ B.val ⊔ U.val ≤ involutionCentralizer t := by
  by_cases hUA : U = A
  · subst U
    obtain ⟨t, ht, hle⟩ := edge D A B hAB
    exact ⟨t, ht, sup_le hle (le_sup_left.trans hle)⟩
  by_cases hUB : U = B
  · subst U
    obtain ⟨t, ht, hle⟩ := edge D A B hAB
    exact ⟨t, ht, sup_le hle (le_sup_right.trans hle)⟩
  by_cases ha : D.graph.Adj A U
  · by_cases hb : D.graph.Adj B U
    · exact triangle D A B U hAB hb ha.symm
    · obtain ⟨t, ht, hle⟩ := nonedge D B A U hAB.symm hUB hb
      exact ⟨t, ht, sup_le (sup_le (le_sup_right.trans (le_sup_left.trans hle))
        (le_sup_left.trans (le_sup_left.trans hle))) (le_sup_right.trans hle)⟩
  · exact nonedge D A B U hAB hUA ha

/-- Conjugate an arbitrary edge and third vertex into the original C_G(z),
then use Sylow conjugacy inside that centralizer to send the third vertex
exactly to the seed X. This is the normalization used in source 47.9. -/
theorem normalize (D : Seed G) (A B U : D.Vertex) (hAB : D.graph.Adj A B) :
    ∃ g : G, g • U = D.base ∧
      (g • A).val ≤ involutionCentralizer D.z ∧
      (g • B).val ≤ involutionCentralizer D.z := by
  obtain ⟨t, ht, hle⟩ := edge_and_vertex D A B U hAB
  obtain ⟨a, ha⟩ := isConj_iff.mp ht
  have he : MulAut.conj a⁻¹ t = D.z := by
    change a⁻¹ * t * (a⁻¹)⁻¹ = D.z
    rw [← ha]
    group
  have hx (V : D.Vertex) (hV : V.val ≤ involutionCentralizer t) :
      (a⁻¹ • V).val ≤ involutionCentralizer D.z := by
    simpa only [he] using smul_le_centralizer D a⁻¹ t V hV
  have hu := hx U (le_sup_right.trans hle)
  obtain ⟨h, hh⟩ := D.conjugate_of_le_centralizer _ (D.vertex_card _) hu
  have hh' : (h : G) • D.base = a⁻¹ • U := Subtype.ext hh
  refine ⟨(h : G)⁻¹ * a⁻¹, ?_, ?_, ?_⟩
  · rw [mul_smul, ← hh', inv_smul_smul]
  · rw [mul_smul]
    exact conj_smul_le_of_le (hx A (le_sup_left.trans (le_sup_left.trans hle))) h⁻¹
  · rw [mul_smul]
    exact conj_smul_le_of_le (hx B (le_sup_right.trans (le_sup_left.trans hle))) h⁻¹

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.TripleLocalization
