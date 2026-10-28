module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableS3Markings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.A5BetaSmallAlphaExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedSmallAlphaExclusions

/-!
# Excluding critical distance one for the small-solvable / S₃ pair

The directed alpha cannot be S₃: the commuting-one source obstruction
requires a nonbinary linear field. If alpha is the small-solvable endpoint,
the actual non-dihedral S₃ beta action is transitive on two-walks; source
core selection forces a linear alpha, contradicting the quotient orders
ten and twenty. Thus the original pair cannot have critical distance one.
No assertion excludes its genuine distance-three Ree/Tits configurations.
Source: DGS (1985), (11.4)--(11.5), pp.171--172;
Aschbacher--Smith F.1.12 and 15.2.8.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial CommutingOneProfile
open Theory.GroupTheory.AmalgamGraph
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

private theorem symmetricThree_beta_two_walk_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* Equiv.Perm (Fin 3)) :
    RootPathTransitive (graph (family P)) G a 2 := by
  apply two_walk_transitive_of_edge_action hab
  rcases source_edge_transitive_or_dihedral h hB d hab.symm (symmetricThree_rankOne_model eb) with ht | hd
  · intro x y hx hy hxa hya
    obtain ⟨g,hg,he⟩ := ht x y hx hy hxa hya
    exact ⟨g,⟨hg.2,d.local_le b hg.1⟩,he⟩
  · have he := Nat.card_congr (eb.symm.trans hd.some).toEquiv
    rw [Nat.card_perm,Nat.card_fin,DihedralGroup.nat_card] at he
    norm_num at he

private theorem small_alpha_symmetricThree_beta_exclusion
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (ha : Nonempty ((d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* DihedralGroup 5) ∨
      Nonempty ((d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SuzukiMatrixGroup 0))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* Equiv.Perm (Fin 3)) : False := by
  let := finite_endpoints h
  have hn := card_neighbors_of_indices (family P)
    (fun i => ((family P (!i)).subgroupOf (family P i)).index) (fun _ => rfl) b
  have hnb : 1 < ((graph (family P)).neighborSet b).ncard := by
    rw [←Nat.card_coe_set_eq,hn]
    have := source_valence_ge_three h hS b.type
    omega
  obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard hnb a
  have hab := source_critical_one_adjacent hc hb
  let p : BasedWalk (graph (family P)) 2 a := ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨hca,trivial⟩
  have Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)) := by
    rcases ha with he | he
    · exact .dihedral he
    · exact .suzuki 0 he
  obtain ⟨_,n,hn,hi⟩ := source_core_product_and_alpha_on_path h hB d hc hb hcomm
    hbc (Ne.symm hca) Ma (symmetricThree_rankOne_model eb)
    (symmetricThree_beta_two_walk_transitive h hB d hab eb)
    p hp (by change a ∈ [a,b,c]; simp) (by change b ∈ [a,b,c]; simp)
    (by change c ∈ [a,b,c]; simp)
  obtain ⟨K,hK,hfin,hcard,⟨e⟩⟩ := hi
  let := hK
  let := hfin
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hd : 3 ∣ Nat.card (d.localGroup a ⧸ pCore 2 (d.localGroup a)) := by
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_psl2_char_two K
  rcases ha with he | he
  · rw [Nat.card_congr he.some.toEquiv,DihedralGroup.nat_card] at hd
    norm_num at hd
  · rw [Nat.card_congr he.some.toEquiv,suzukiZero_card] at hd
    norm_num at hd

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => Reduction.reducedFamily L S

/-- The original small-solvable/S₃ pair cannot have critical distance one.
This conclusion preserves the genuine distance-three model alternatives. -/
theorem small_solvable_s3_distance_one_exclusion (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (hs : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* Equiv.Perm (Fin 3)))
    (hb : b F = 1) : False := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hpair : ∃ a beta : Vertex F, IsCriticalPair F a beta := source_exists_criticalPair ht
  obtain ⟨a,beta,hc⟩ := hpair
  have hab := source_critical_one_adjacent hc hb
  have hcomm := Reduction.reduced_critical_commuting_of_small_solvable h false hm hc
  have models (v : Vertex F) : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)) :=
    small_solvable_s3_graph_models h hm hs v
  by_cases ha : a.type = true
  · let ea := (symmetricThree_graph_quotient h true hs.some a ha).some.trans
      SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
    have hval : 3 ≤ Nat.card ((graph F).neighborSet beta) := by
      rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index)
        (fun _ => rfl)]
      exact source_valence_ge_three ht (Reduction.reduced_vertex_sylow h) beta.type
    obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet beta)
      (by rw [←Nat.card_coe_set_eq]; omega) a
    exact source_alpha_linear_field_card_ne_two ht (Reduction.reduced_borel_core_sylow h)
      d hc hb hcomm hbc hca.symm (models beta) ea (by norm_num [Nat.card_eq_fintype_card])
  · have ha' : a.type = false := Bool.eq_false_iff.mpr ha
    have hbeta : beta.type = true := by
      cases he : beta.type
      · exact False.elim (hab.1 (ha'.trans he.symm))
      · rfl
    exact small_alpha_symmetricThree_beta_exclusion ht (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) d hc hb hcomm
      (small_solvable_graph_quotients h false hm a ha')
      (symmetricThree_graph_quotient h true hs.some beta hbeta).some

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
