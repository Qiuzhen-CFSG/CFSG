module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RankOneSeeds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NeighborIntersection

/-!
# The general opposite-seed separation in Chapter 11

The Sylow supplement of (11.5) and critical seed escape give generation of
L_alpha modulo Q_alpha by two opposite seeds. The core fixes the star, so
the seeds themselves are transitive. They centralize the intersection of
the neighboring-core intersection at beta with the remote alpha core.
At beta the centralizer is already transitive. Faithfulness forces that
intersection to vanish, proving the opening separation step of (11.6).

The exact (11.5) supplement is explicit; it follows from the earlier core
identities in the reduced-source consumer. These results apply to all actual
rank-one quotient rows and require no tree or finite-completion hypothesis.
They do not assert the remaining center identities, cardinalities or profiles.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.5)--(11.6), p.172, using (3.2)(c), p.73.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The two opposite seeds generate the intrinsic alpha local group modulo
 its actual core, using exactly the Sylow supplement from (11.5). -/
theorem source_rankOne_opposite_seed_generation (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hsupp : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    ((Z (family P) c ⊓ Q (family P) b) ⊔
      (Z (family P) (g • c) ⊓ Q (family P) (g • b))) ⊔ Q (family P) a =
        d.localGroup a := by
  let := finite_endpoints h
  let := source_center_elementary h c
  let : IsElementaryAbelian 2 (Z (family P) c ⊓ Q (family P) b : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have hab := source_critical_one_adjacent hc hb
  have habg : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [show g • a = a from hga] at hh
  have hnot := source_rankOne_centers_not_isPGroup h hB d hc hb hbc hac Mb
  have hesc : ¬ Z (family P) c ⊓ Q (family P) b ≤ Q (family P) a :=
    source_seed_not_le_opposite_core h hbc.symm hab.symm (by intro hp; apply hnot; rw [sup_comm]; exact hp)
  have hgen := source_elementary_escape_edge_generation h hB d hab habg
    (Ne.symm hgb) Ma (Z (family P) c ⊓ Q (family P) b)
    ((inf_le_right.trans (source_Z_Q_U h b).2).trans
      ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right))
    (inf_le_right.trans (Q_le_stabilizer _ b)) hesc
  have hm := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hsupp
  rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ←Z_translate,←Q_translate,←Q_translate,show g • a = a from hga] at hm
  have he : ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2).map
      (MulAut.conj g).toMonoidHom =
      (stabilizer (family P) a ⊓ stabilizer (family P) (g • b)).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      ←stabilizer_translate,←stabilizer_translate,show g • a = a from hga]
  rw [he] at hm
  rw [hm,←sup_assoc] at hgen
  exact hgen

/-- The opposite seeds themselves are transitive: the omitted local core
 fixes every neighbor, so it contributes nothing to the orbit. -/
theorem source_rankOne_opposite_seed_transitive (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hsupp : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    {v : Vertex (family P)} (hav : (graph (family P)).Adj a v) :
    ∃ w ∈ (Z (family P) c ⊓ Q (family P) b) ⊔
      (Z (family P) (g • c) ⊓ Q (family P) (g • b)), w • b = v := by
  let W := (Z (family P) c ⊓ Q (family P) b) ⊔
    (Z (family P) (g • c) ⊓ Q (family P) (g • b))
  have hab := source_critical_one_adjacent hc hb
  have hgen := source_rankOne_opposite_seed_generation h hB d hc hb hbc hac Ma Mb hsupp g hga hgb
  have hW : W ≤ stabilizer (family P) a := (le_sup_left.trans hgen.le).trans (d.local_le a)
  have hn : W ≤ normalizer (Q (family P) a : Set G) :=
    hW.trans (CommutingNontrivial.stabilizer_normalizes_Q (family P) a)
  obtain ⟨t,ht,htb⟩ := d.transitive a ⟨b,hab⟩ ⟨v,hav⟩
  have ht' : t ∈ (W : Set G) * (Q (family P) a : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right W (Q (family P) a) hn,hgen]
    exact ht
  obtain ⟨w,hw,q,hq,rfl⟩ := ht'
  have hqb : q • b = b := ((source_Z_Q_U h a).2.trans
    ((ballKernel_one_le_edge _ hab).trans inf_le_right)) hq
  exact ⟨w,hw,by simpa only [mul_smul,hqb] using htb⟩

/-- The opening vanishing step in (11.6), for every source rank-one row.
 The only Chapter 11 input beyond critical escape is the (11.5) supplement. -/
theorem source_rankOne_neighbor_intersection_separated (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hsupp : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a)
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    neighborCoreIntersection (family P) b ⊓ Q (family P) (g • c) = ⊥ := by
  let I := neighborCoreIntersection (family P) b
  let J := I ⊓ Q (family P) (g • c)
  let W := (Z (family P) c ⊓ Q (family P) b) ⊔
    (Z (family P) (g • c) ⊓ Q (family P) (g • b))
  have hab := source_critical_one_adjacent hc hb
  have hW : W ≤ centralizer (J : Set G) := by
    apply sup_le
    · exact inf_le_left.trans ((le_centralizer_iff.mp (source_core_centralizes_center h c)).trans
        (centralizer_le (inf_le_left.trans (neighborCoreIntersection_le _ hbc.symm))))
    · exact inf_le_left.trans
        ((le_centralizer_iff.mp (source_core_centralizes_center h (g • c))).trans
          (centralizer_le inf_le_right))
  have hIa : I ≤ Q (family P) a := neighborCoreIntersection_le _ hab
  have hIE : I ≤ stabilizer (family P) a ⊓ stabilizer (family P) b :=
    hIa.trans ((source_Z_Q_U h a).2.trans (ballKernel_one_le_edge _ hab))
  apply source_normalized_edge_eq_bot h hab J (inf_le_left.trans hIE)
  · intro v hv
    obtain ⟨w,hw,he⟩ := source_rankOne_opposite_seed_transitive h hB d hc hb hbc hac Ma Mb hsupp g hga hgb hv
    exact ⟨w,(hW.trans (Subgroup.centralizer_le_normalizer _)) hw,he⟩
  · intro v hv
    obtain ⟨w,hw,he⟩ := source_neighbor_core_centralizer_transitive h hB hc hb hv
    exact ⟨w,Subgroup.centralizer_le_normalizer _ (centralizer_le (show J ≤ I from inf_le_left) hw.2),he⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
