module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryShortPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RemoteLayerVanishing

/-!
# The unitary remote layer without a four-walk premise

For an escaping turn at alpha, use the three-edge walk
beta, alpha, g·beta, g·c. The short-path theorem supplies its actual
transitivity, so source 6.7 gives both full edge supplements used in the
remote-layer argument. Selecting the linear alpha quotient from the original
catalogue then proves I_beta intersect Q_(g·beta) = 1.

Only this shorter walk is needed in (11.6); it contains all four vertices
used by `RemoteLayerVanishing`. Both unitary covers and the original field
degree are retained. No later path profile is used.
Source: DGS85, Groups and Graphs, (11.6), pp.172--173.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The remote layer vanishes on every escaping turn, with the source path
and its transitivity constructed from the unitary beta marking. -/
theorem source_unitary_remote_layer_eq_bot
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b)) :
    neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) = ⊥ := by
  have hab := source_critical_one_adjacent hc hb
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [show g • a = a from hga] at hh
  have hbc' : (graph (family P)).Adj (g • b) (g • c) :=
    (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc
  let p : BasedWalk (graph (family P)) 3 b :=
    ⟨⟨a,hab.symm⟩,⟨⟨g • b,hab'⟩,⟨⟨g • c,hbc'⟩,PUnit.unit⟩⟩⟩
  have hp : p.Nonbacktracking := by
    refine ⟨hgb,?_,trivial⟩
    intro he
    exact hac ((MulAction.injective g) ((show g • a = a from hga).trans he.symm))
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := by
    rcases mark with hi | hi
    · exact .projective_unitary m hm hi
    · exact .special_unitary m hm hi
  obtain ⟨_,n,hn,hi⟩ := source_unitary_beta_core_product_and_alpha h hB d hc hb hcomm
    hbc hac Ma hm mark
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact source_linear_rankOne_layer_eq_bot_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb (ea.trans ep.symm) g hga hgb hesc
    (source_unitary_three_walk_transitive h hB d hc hb hcomm hbc hac Ma hm mark b)
    p hp (by change a ∈ [b,a,g • b,g • c]; simp)
    (by change b ∈ [b,a,g • b,g • c]; simp)
    (by change g • b ∈ [b,a,g • b,g • c]; simp)
    (by change g • c ∈ [b,a,g • b,g • c]; simp)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
