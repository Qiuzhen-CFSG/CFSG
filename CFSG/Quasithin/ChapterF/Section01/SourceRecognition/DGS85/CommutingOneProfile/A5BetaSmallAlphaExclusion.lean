module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceCoreSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NeighborActions
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.Suzuki.LinearSeparation

/-!
# Excluding a small-solvable critical alpha opposite A₅

The literal A₅ beta action gives transitivity on two-edge walks from alpha.
This is enough for the source core-product and alpha-selection argument:
alpha must have a characteristic-two linear quotient. Such a quotient has
order divisible by three, whereas D₁₀ and Sz(2) have orders ten and twenty.

This eliminates the small-alpha orientation of the Chapter 15 mixed pair
without reversing its directed critical edge or assuming a longer path
profile. The opposite orientation remains with the beta exclusion.
Source: DGS, *Groups and Graphs* (1985), (11.4)--(11.5), pp.171--172;
Aschbacher--Smith 15.2.4--8, printed pp.1106--1110.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups
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

private theorem a5_model {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 5)) : IsRankOneModel H := by
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact .linear 2 (by decide) ⟨GaloisField 2 2,inferInstance,inferInstance,
    (by simpa using hc),⟨e.trans e₄.symm⟩⟩

/-- An actual A₅ beta quotient supplies two-walk transitivity at alpha. -/
theorem source_a5_beta_two_walk_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* alternatingGroup (Fin 5)) :
    RootPathTransitive (graph (family P)) G a 2 := by
  apply two_walk_transitive_of_edge_action hab
  rcases source_edge_transitive_or_dihedral h hB d hab.symm (a5_model eb) with ht | hd
  · intro x y hx hy hxa hya
    obtain ⟨g,hg,he⟩ := ht x y hx hy hxa hya
    exact ⟨g,⟨hg.2,d.local_le b hg.1⟩,he⟩
  · have he := Nat.card_congr (eb.symm.trans hd.some).toEquiv
    rw [nat_card_alternatingGroup,DihedralGroup.nat_card] at he
    norm_num [Nat.factorial] at he

/-- In a directed commuting critical edge, a small-solvable alpha and A₅
beta are impossible. The required turn and short path are constructed. -/
theorem source_small_solvable_alpha_a5_beta_exclusion
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (ha : Nonempty ((d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* DihedralGroup 5) ∨
      Nonempty ((d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SuzukiMatrixGroup 0))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* alternatingGroup (Fin 5)) : False := by
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
    hbc (Ne.symm hca) Ma (a5_model eb) (source_a5_beta_two_walk_transitive h hB d hab eb)
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

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
