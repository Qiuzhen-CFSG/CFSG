module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerOrbit
public import Theory.GroupAction.CubicTree.CentralIntervals
public import Theory.GroupAction.CubicTree.TrackTranslation
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# Transporting the central-edge exclusion along the original track

The normalizer of a nontrivial track fixer is transitive on the neighbors of
the first base vertex. Combined with the literal track translation, this
sends the base edge to every track edge, allowing either endpoint ordering.
Conjugation by these normalizing elements transports the intersection of the
fixer with the center of the base overlap to every edge center. Thus the
base-edge exclusion in Goldschmidt (5.3) rules out every central involution
fixing the entire track, exactly as needed to construct the Section 6 intervals.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(5.1)--(5.3) and the beginning of Section 6, printed pp.394--395.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The actual track normalizer sends the base edge to each edge of the track,
allowing the two endpoint orientations. -/
theorem NormalizerCandidate.track_edge_conjugate (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G)
    (h0 : t.vertex 0 = RankTwo.base F false) (h1 : t.vertex 1 = RankTwo.base F true)
    (hQ : NormalizerCandidate F t.fixer) (i : ℤ) :
    ∃ g ∈ normalizer (t.fixer : Set G),
      (g • RankTwo.base F false = t.vertex i ∧
        g • RankTwo.base F true = t.vertex (i+1)) ∨
      (g • RankTwo.base F false = t.vertex (i+1) ∧
        g • RankTwo.base F true = t.vertex i) := by
  have hn (k : ℤ) : t.translation ^ k ∈ normalizer (t.fixer : Set G) :=
    zpow_mem t.translation_mem_normalizer_fixer k
  rcases Int.even_or_odd i with ⟨k,hk⟩ | ⟨k,hk⟩
  · refine ⟨t.translation ^ k,hn k,Or.inl ⟨?_,?_⟩⟩
    · rw [← h0,t.zpow_translate]
      congr 1
      omega
    · rw [← h1,t.zpow_translate]
      congr 1
      omega
  · have h01 : (RankTwo.graph F).Adj (RankTwo.base F false) (RankTwo.base F true) := by
      rw [← h0,← h1]
      exact t.adjacent 0
    have h0m : (RankTwo.graph F).Adj (RankTwo.base F false) (t.vertex (-1)) := by
      rw [← h0]
      have hh := (t.adjacent (-1)).symm
      simpa using hh
    obtain ⟨a,ha,ha1⟩ := hQ.locally_transitive h h01 h0m
    have ha0 : a • RankTwo.base F false = RankTwo.base F false := by
      change a ∈ MulAction.stabilizer G (RankTwo.base F false)
      rw [RankTwo.base,stabilizer_base]
      exact ha.2
    refine ⟨t.translation ^ (k+1) * a,mul_mem (hn (k+1)) ha.1,
      Or.inr ⟨?_,?_⟩⟩
    · rw [mul_smul,ha0,← h0,t.zpow_translate]
      congr 1
      omega
    · rw [mul_smul,ha1,t.zpow_translate]
      congr 1
      omega

/-- A base-edge centralizer exclusion extends along the entire actual track.
The conjugating elements lie in the track normalizer, so the original fixer
and the literal edge stabilizers are both preserved. -/
theorem NormalizerCandidate.centralInvolution_not_mem_fixer_of_base
    (h : CubicTreeAction F) (t : Track (RankTwo.graph F) G)
    (h0 : t.vertex 0 = RankTwo.base F false) (h1 : t.vertex 1 = RankTwo.base F true)
    (hQ : NormalizerCandidate F t.fixer)
    (hbase : Disjoint t.fixer (centerIn (F false ⊓ F true)))
    (z : G) (hz : t.CentralInvolution z) : z ∉ t.fixer := by
  intro hzQ
  obtain ⟨i,hzi⟩ := hz.2
  obtain ⟨g,hg,he⟩ := hQ.track_edge_conjugate h t h0 h1 i
  let c : MulAut G := MulAut.conj g
  have hedge : (F false ⊓ F true).map c.toMonoidHom = t.edgeStabilizer i := by
    rw [map_inf _ _ _ c.injective]
    have hleft : (F false).map c.toMonoidHom =
        MulAction.stabilizer G (g • RankTwo.base F false) := by
      rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,RankTwo.base,stabilizer_base]
    have hright : (F true).map c.toMonoidHom =
        MulAction.stabilizer G (g • RankTwo.base F true) := by
      rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,RankTwo.base,stabilizer_base]
    rw [hleft,hright]
    rcases he with ⟨he0,he1⟩ | ⟨he0,he1⟩
    · rw [he0,he1]
      rfl
    · rw [he0,he1,inf_comm]
      rfl
  have hzcenter : z ∈ centerIn (t.edgeStabilizer i) :=
    ⟨hzi.1,fun x hx => (hzi.2 x hx).eq.symm⟩
  rw [← hedge,← centerIn_map_equiv] at hzcenter
  obtain ⟨w,hw,hwz⟩ := hzcenter
  have hwQ : w ∈ t.fixer := by
    have hn : c w ∈ t.fixer ↔ w ∈ t.fixer :=
      (mem_normalizer_iff.mp hg w).symm
    exact hn.mp (hwz.symm ▸ hzQ)
  have hw1 : w = 1 := mem_bot.mp ((disjoint_iff.mp hbase).le ⟨hwQ,hw⟩)
  have hz1 : z = 1 := by rw [← hwz,hw1,map_one]
  simpa [hz1] using hz.1

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
