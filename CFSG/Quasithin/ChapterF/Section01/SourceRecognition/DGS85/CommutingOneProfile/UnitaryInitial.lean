module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.EscapingFourWalk
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NeighborActions

/-!
# The initial unitary turn at a commuting critical edge

The marked beta action gives two-walk transitivity at alpha. This supplies
the short-path premise of (11.4)--(11.5), selecting a linear alpha quotient
and the edge-core product. The linear center-escape argument then chooses
an actual nonbacktracking four-walk with vertices [g c,g b,a,b,c].
Both unitary covers and all positive fixed-field degrees are retained.
Four-walk transitivity is not asserted by this initial construction.
Source: DGS85 (11.4)--(11.6), pp.171--174.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem two_walk_transitive_of_edge_action
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (ht : ∀ x y : Vertex (family P), (graph (family P)).Adj b x →
      (graph (family P)).Adj b y → x ≠ a → y ≠ a →
      ∃ g ∈ stabilizer (family P) a ⊓ stabilizer (family P) b, g • x = y) :
    RootPathTransitive (graph (family P)) G a 2 := by
  intro p q hp hq
  let x := (p.1 : Vertex (family P))
  let y := (q.1 : Vertex (family P))
  let z := (p.2.1 : Vertex (family P))
  let w := (q.2.1 : Vertex (family P))
  obtain ⟨g,hga,hgx⟩ := locally_transitive (family P) p.1.property hab
  obtain ⟨k,hka,hky⟩ := locally_transitive (family P) q.1.property hab
  have hgadj : (graph (family P)).Adj b (g • z) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr p.2.1.property
    change (graph (family P)).Adj (g • x) (g • z) at hh
    rwa [hgx] at hh
  have hkadj : (graph (family P)).Adj b (k • w) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) k).map_adj_iff.mpr q.2.1.property
    change (graph (family P)).Adj (k • y) (k • w) at hh
    rwa [hky] at hh
  have hgz : g • z ≠ a := by
    intro he
    exact hp.1 ((MulAction.injective g) (he.trans (show g • a = a from hga).symm))
  have hkw : k • w ≠ a := by
    intro he
    exact hq.1 ((MulAction.injective k) (he.trans (show k • a = a from hka).symm))
  obtain ⟨t,ht,htz⟩ := ht (g • z) (k • w) hgadj hkadj hgz hkw
  refine ⟨k⁻¹*t*g,?_,?_⟩
  · change (k⁻¹*t*g) • a = a
    rw [mul_smul,mul_smul,show g • a = a from hga,show t • a = a from ht.1]
    exact inv_mem hka
  · change [a,x,z].map ((k⁻¹*t*g) • ·) = [a,y,w]
    simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true]
    refine ⟨?_,?_,?_⟩
    · rw [mul_smul,mul_smul,show g • a = a from hga,show t • a = a from ht.1]
      exact inv_mem hka
    · rw [mul_smul,mul_smul,hgx,show t • b = b from ht.2,←hky,inv_smul_smul]
    · rw [mul_smul,mul_smul,htz,inv_smul_smul]

/-- A unitary beta marking supplies the actual two-walk transitivity at alpha,
with both covers and every positive fixed-field degree. -/
theorem source_unitary_beta_two_walk_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m)) :
    RootPathTransitive (graph (family P)) G a 2 := by
  apply two_walk_transitive_of_edge_action hab
  intro x y hx hy hxa hya
  obtain ⟨g,hg,he⟩ := source_unitary_edge_transitive h hB d hab.symm hm mark hx hy hxa hya
  exact ⟨g,⟨hg.2,d.local_le b hg.1⟩,he⟩

/-- Source (11.4)--(11.5) with the unitary-beta path premise discharged.
The alpha row is selected from its full catalogue, not assumed linear. -/
theorem source_unitary_beta_core_product_and_alpha
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m)) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b ∧
      ∃ n, 1 < n ∧ ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n) := by
  have hab := source_critical_one_adjacent hc hb
  let p : BasedWalk (graph (family P)) 2 a := ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨Ne.symm hac,trivial⟩
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := by
    rcases mark with hi | hi
    · exact .projective_unitary m hm hi
    · exact .special_unitary m hm hi
  exact source_core_product_and_alpha_on_path h hB d hc hb hcomm hbc hac Ma Mb
    (source_unitary_beta_two_walk_transitive h hB d hab hm mark) p hp
    (by change a ∈ [a,b,c]; simp) (by change b ∈ [a,b,c]; simp) (by change c ∈ [a,b,c]; simp)

private theorem initial_neighbor_other (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (a b : Vertex (family P)) :
    ∃ c, (graph (family P)).Adj b c ∧ a ≠ c := by
  let := finite_endpoints h
  have hv := card_neighbors_of_indices (family P)
    (fun i => ((family P (!i)).subgroupOf (family P i)).index) (fun _ => rfl) b
  have hc : 1 < ((graph (family P)).neighborSet b).ncard := by
    rw [←Nat.card_coe_set_eq,hv]
    have := source_valence_ge_three h hS b.type
    omega
  obtain ⟨c,hc,hca⟩ := Set.exists_ne_of_one_lt_ncard hc a
  exact ⟨c,hc,Ne.symm hca⟩

private theorem initial_turn_walk {a b c : Vertex (family P)}
    (hab : (graph (family P)).Adj a b) (hbc : (graph (family P)).Adj b c)
    (hac : a ≠ c) (g : G) (hga : g ∈ stabilizer (family P) a)
    (hgb : g • b ≠ b) :
    ∃ p : BasedWalk (graph (family P)) 4 (g • c),
      p.Nonbacktracking ∧ p.vertices = [g • c,g • b,a,b,c] := by
  have hb'a : (graph (family P)).Adj (g • b) a := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab.symm
    change (graph (family P)).Adj (g • b) (g • a) at hh
    rwa [show g • a = a from hga] at hh
  have hc'b' : (graph (family P)).Adj (g • c) (g • b) :=
    (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc.symm
  refine ⟨⟨⟨g • b,hc'b'⟩,⟨⟨a,hb'a⟩,⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩⟩⟩,?_,rfl⟩
  change a ≠ g • c ∧ b ≠ g • b ∧ c ≠ a ∧ True
  exact ⟨fun he => hac ((MulAction.injective g) ((show g • a = a from hga).trans he)),
    Ne.symm hgb,Ne.symm hac,trivial⟩

/-- The escaping four-walk exists from the unitary beta marking alone.
No initial four-walk transitivity is assumed in this construction. -/
theorem source_unitary_beta_escaping_four_walk
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m)) :
    ∃ c, (graph (family P)).Adj b c ∧ a ≠ c ∧
      ∃ g ∈ stabilizer (family P) a, g • b ≠ b ∧
        ¬ Z (family P) b ≤ Q (family P) (g • b) ∧
        ∃ p : BasedWalk (graph (family P)) 4 (g • c),
          p.Nonbacktracking ∧ p.vertices = [g • c,g • b,a,b,c] := by
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨c,hbc,hac⟩ := initial_neighbor_other h hS a b
  obtain ⟨b',hab',hbb'⟩ := initial_neighbor_other h hS b a
  obtain ⟨g,hga,hgb⟩ := locally_transitive (family P) hab hab'
  have hgb' : g • b ≠ b := by rw [hgb]; exact Ne.symm hbb'
  obtain ⟨_,n,hn,hi⟩ := source_unitary_beta_core_product_and_alpha h hB d hc hb hcomm
    hbc hac Ma hm mark
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := by
    rcases mark with hi | hi
    · exact .projective_unitary m hm hi
    · exact .special_unitary m hm hi
  obtain ⟨t,hta,htb,hesc⟩ := source_linear_rankOne_center_escape h hB d hc hb hcomm
    hbc hac Ma Mb (ea.trans ep.symm) g hga hgb'
  exact ⟨c,hbc,hac,t,hta,htb,hesc,initial_turn_walk hab hbc hac t hta htb⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
