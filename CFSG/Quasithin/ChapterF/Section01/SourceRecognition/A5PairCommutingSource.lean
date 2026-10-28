module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedLinearBetaProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableLinearFourMarkings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.TheoremBFullCatalogue
/-!
# The original A5 pair in the commuting critical branch

Each original A5 quotient transports through its actual starred inclusion
and local conjugation to the field-four quotient at every reduced graph
vertex. In the commuting distance-one branch the Chapter 11 field equation
would identify exponent two with twice itself. In the longer zero-displacement
branch Chapter 9 gives a field-two quotient, contradicting the same A5 marking.

Thus a commuting critical pair can only survive at distance three with
nonzero intersection displacement. The full original F.1.1 hypotheses and
whole reduced overlap are unchanged; no local catalogue, marked reduced
comparison, core equality, or containment is assumed. The surviving Chapter 12
nonzero-displacement branch remains a source obligation for A5 pair containment.

Source: DGS, Groups and Graphs (1985), Theorem B, Chapter 9, and
(11.6)--(11.7), printed pp.102,142--151,172--175.
-/

open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open scoped MatrixGroups

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal reduced actor at every vertex inherits the original field-four marking. -/
theorem a5_pair_reduced_graph_linear_four (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (z : Vertex (Reduction.reducedFamily L S)) :
    ClassicalGroup.IsPSL (graphLocalGroup (Reduction.reducedFamily L S) z ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) z)) 2 (2 ^ 2) := by
  have hc4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e4⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc4
  have az : (family L z.type ⧸ pCore 2 (family L z.type)) ≃* alternatingGroup (Fin 5) := by
    cases hz : z.type
    · exact (a 0).some
    · exact (a 1).some
  exact ⟨GaloisField 2 2, inferInstance, inferInstance, (by simpa using hc4),
    ⟨(Assembly.a5_graph_quotient h z.type az z rfl).some.trans e4.symm⟩⟩

/-- No directed distance-one critical pair can commute in an original A5/A5 pair. -/
theorem a5_pair_not_commuting_bOne
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hb : b (Reduction.reducedFamily L S) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ = ⊥)
    : False := by
  obtain ⟨he, _⟩ := reduced_linear_linear_parameters h
    (Reduction.reducedFullEarlierLocalTheorems h) hc hb hcomm 2 2 (by decide) (by decide)
    (a5_pair_reduced_graph_linear_four h a v) (a5_pair_reduced_graph_linear_four h a w)
  omega

/-- Chapter 9 excludes zero intersection displacement for every longer commuting A5 pair. -/
theorem a5_pair_not_commuting_trivial
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 = b (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S) u 1 ⊓ Q (Reduction.reducedFamily L S) w,
      V (Reduction.reducedFamily L S) w 1⁆ = ⊥) : False := by
  let F := Reduction.reducedFamily L S
  have models (z : Vertex F) : IsRankOneModel (graphLocalGroup F z ⧸ pCore 2 (graphLocalGroup F z)) :=
    .linear 2 (by decide) (a5_pair_reduced_graph_linear_four h a z)
  obtain ⟨_, K, _, _, _, E, _, _, _, hK, _, heK, _⟩ :=
    CommutingTrivial.reduced_critical_fields_two_from_chapterEight h models hc hvu hd hb hcomm htriv
  have az : (family L u.type ⧸ pCore 2 (family L u.type)) ≃* alternatingGroup (Fin 5) := by
    cases hz : u.type
    · exact (a 0).some
    · exact (a 1).some
  obtain ⟨ea⟩ := Assembly.a5_graph_quotient h u.type az u rfl
  have he := Nat.card_congr (ea.symm.trans heK.some).toEquiv
  rw [nat_card_alternatingGroup, BenderSuzuki.External.huppert614_card_specialLinearGroup, hK] at he
  norm_num [Nat.factorial] at he

/-- The commuting branch is reduced to the actual distance-three nonzero
intersection displacement. Both original quotient marks supply the entire
local catalogue, and the distance-one and zero-displacement branches are
excluded internally. -/
theorem a5_pair_commuting_critical_remaining
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v,
      Z (Reduction.reducedFamily L S) w⁆ = ⊥) :
    b (Reduction.reducedFamily L S) = 3 ∧
      ⁅V (Reduction.reducedFamily L S) u 1 ⊓ Q (Reduction.reducedFamily L S) w,
        V (Reduction.reducedFamily L S) w 1⁆ ≠ ⊥ := by
  have models (z : Vertex (Reduction.reducedFamily L S)) :
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S) z ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) z)) :=
    .linear 2 (by decide) (a5_pair_reduced_graph_linear_four h a z)
  have hb : b (Reduction.reducedFamily L S) = 3 := by
    rcases Assembly.reduced_critical_alternatives_from_full_catalogue h models hc hvu hd with
      ⟨hne, _⟩ | ⟨_, hb | hb⟩
    · exact (hne hcomm).elim
    · exact (a5_pair_not_commuting_bOne h a hc hb hcomm).elim
    · exact hb
  refine ⟨hb, ?_⟩
  intro htriv
  exact a5_pair_not_commuting_trivial h a hc hvu hd (by omega) hcomm htriv

end CFSG.Quasithin.ChapterF.Source
