module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceCoreSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedLinearBetaProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourcePathParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.EscapingFourWalk
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearPaths
public import Theory.SpecificGroups.Suzuki.LinearSeparation

/-!
# The commuting-one profile from a linear beta marking

A genuine linear beta quotient makes two-edge walks starting at alpha
transitive. The source seed comparison on that walk gives the adjacent-core
product and selects alpha as linear, without a preselected alpha marking.
The original-inclusion application retains the beta field degree and gives
the full-Borel order, core profile and Chapter 14 tree-path inputs.

The alpha local catalogue remains explicit. Selection of beta from the
entire elementary branch, including its dihedral candidate, is separate.
Source: DGS, Groups and Graphs (1985), (11.3)--(11.7), pp.169--175,
and the path input (6.8), pp.123--124.
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

/-- The linear beta action supplies the two-edge path used for alpha selection. -/
theorem source_linear_beta_two_walk_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2^m)) :
    RootPathTransitive (graph (family P)) G a 2 := by
  apply two_walk_transitive_of_edge_action hab
  rcases source_edge_transitive_or_dihedral h hB d hab.symm (.linear m hm mark) with ht | hd
  · intro x y hx hy hxa hya
    obtain ⟨g,hg,he⟩ := ht x y hx hy hxa hya
    exact ⟨g,⟨hg.2,d.local_le b hg.1⟩,he⟩
  · obtain ⟨k,_,_,hk,⟨eb⟩⟩ := mark
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hk)
    have hh := three_dvd_card_psl2_char_two k
    rw [Nat.card_congr (eb.symm.trans hd.some).toEquiv,DihedralGroup.nat_card] at hh
    norm_num at hh

/-- The linear-beta source branch constructs the full core product and
alpha marking from the two-edge path; alpha is not assumed linear. -/
theorem source_linear_beta_core_product_and_alpha
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2^m)) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      Q (family P) a ⊔ Q (family P) b ∧
      ∃ n, 1 < n ∧ ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n) := by
  have hab := source_critical_one_adjacent hc hb
  let p : BasedWalk (graph (family P)) 2 a := ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨Ne.symm hac,trivial⟩
  exact source_core_product_and_alpha_on_path h hB d hc hb hcomm hbc hac Ma (.linear m hm mark)
    (source_linear_beta_two_walk_transitive h hB d hab hm mark) p hp
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

section Original
open Reduction NoncommutingProfile
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The original alpha quotient is linear over the square of the supplied
beta field. The actual subgroup inclusion and positive beta degree are retained. -/
theorem original_linear_beta_alpha_marking
    (h : HypothesisF11 L₀ S₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup F₀ a).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ a).map (G₀).subtype)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSL ((graphLocalGroup F₀ b).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ b).map (G₀).subtype)) 2 (2^m)) :
    ClassicalGroup.IsPSL ((graphLocalGroup F₀ a).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ a).map (G₀).subtype)) 2 (2^(2*m)) := by
  let d := reducedFullEarlierLocalTheorems h
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  obtain ⟨c,hbc,hac⟩ := initial_neighbor_other (reduced_triple h) (reduced_vertex_sylow h) a b
  obtain ⟨_,n,hn,ha⟩ := source_linear_beta_core_product_and_alpha (reduced_triple h)
    (reduced_borel_core_sylow h) d hc hb hcomm hbc hac (Ma.of_equiv eqa) hm (mark.of_mulEquiv eqb)
  have hnm := (reduced_linear_linear_parameters h d hc hb hcomm n m (by omega) hm ha
    (mark.of_mulEquiv eqb)).1
  rw [hnm] at ha
  exact ha.of_mulEquiv eqa.symm

variable (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀)
      (base (Reduction.reducedFamily L₀ S₀) false) (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false),
      Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
      (base (Reduction.reducedFamily L₀ S₀) false)).map (Reduction.G₀ L₀ S₀).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) false)).map (Reduction.G₀ L₀ S₀).subtype)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSL ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
      (base (Reduction.reducedFamily L₀ S₀) true)).map (Reduction.G₀ L₀ S₀).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) true)).map (Reduction.G₀ L₀ S₀).subtype)) 2 (2^m))

include h hc hb hcomm Ma hm mark

/-- Core and full-Borel orders from the beta marking alone, with alpha
selection discharged and the same beta degree throughout. -/
theorem original_linear_beta_core_profile :
    ClassicalGroup.IsPSL ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
      (Q F₀ (base F₀ false)).map (G₀).subtype = (Z F₀ (base F₀ false)).map (G₀).subtype ∧
      Nat.card ((Z F₀ (base F₀ true)).map (G₀).subtype) = 2^m ∧
      Nat.card ((Q F₀ (base F₀ false)).map (G₀).subtype) = (2^(2*m))^2 ∧
      Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) = (2^(2*m))^2 * 2^m ∧
      Nat.card (twoCore (commonBorel L₀ S₀)) = (2^(2*m))^2 * (2^m)^2 := by
  have ha := original_linear_beta_alpha_marking h hc hb hcomm Ma hm mark
  let d := reducedFullEarlierLocalTheorems h
  obtain ⟨_,hQa,hZb,hca,hcb,_⟩ := original_reduced_linear_linear_profile h d hc hb hcomm
    (2*m) m (by omega) hm ha mark
  exact ⟨ha,hQa,hZb,hca,hcb,(original_linear_linear_borel_core_order h d hc hb hcomm
    (2*m) m (by omega) hm ha mark).2⟩

/-- The actual corrected beta seed span and beta-core center, with alpha
selection discharged. The span uses Z_alpha intersect Q_beta. -/
theorem original_linear_beta_span_and_center :
    betaSpan ((stabilizer F₀ (base F₀ true)).map (G₀).subtype)
      ((Z F₀ (base F₀ false)).map (G₀).subtype) = (Q F₀ (base F₀ true)).map (G₀).subtype ∧
      centerIn ((Q F₀ (base F₀ true)).map (G₀).subtype) = (Z F₀ (base F₀ true)).map (G₀).subtype := by
  have ha := original_linear_beta_alpha_marking h hc hb hcomm Ma hm mark
  let d := reducedFullEarlierLocalTheorems h
  let ea := (d.localGroup (base F₀ false)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup (base F₀ true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hspan := (reduced_linear_linear_profile h d hc hb hcomm (2*m) m (by omega) hm
    (ha.of_mulEquiv eqa) (mark.of_mulEquiv eqb)).2.2.1
  obtain ⟨c,hbc,hac⟩ := initial_neighbor_other (reduced_triple h) (reduced_vertex_sylow h)
    (base F₀ false) (base F₀ true)
  refine ⟨?_,(original_reduced_linear_linear_centers h d hc hb hcomm hbc hac
    (2*m) m (by omega) hm ha mark).1⟩
  have he := congrArg (map (G₀).subtype) hspan
  dsimp only [betaSpan] at he ⊢
  rw [map_conjugateSpanBy,map_inf _ _ _ (G₀).subtype_injective] at he
  rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀).subtype_injective]
  exact he

/-- The selected alpha and supplied beta markings construct four-walk
transitivity using source 6.8 and the actual adjacent-core obstruction. -/
theorem original_linear_beta_four_walk_transitive :
    ∀ v : Vertex F₀, RootPathTransitive (graph F₀) G₀ v 4 := by
  have ha := original_linear_beta_alpha_marking h hc hb hcomm Ma hm mark
  let d := reducedFullEarlierLocalTheorems h
  let a := base F₀ false
  let b := base F₀ true
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  obtain ⟨ka,_,_,hka,⟨eα⟩⟩ := ha.of_mulEquiv eqa
  obtain ⟨kb,_,_,hkb,⟨eβ⟩⟩ := mark.of_mulEquiv eqb
  let : Fintype ka := Fintype.ofFinite ka
  let : Fintype kb := Fintype.ofFinite kb
  let : CharP ka 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hka)
  let : CharP kb 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hkb)
  let epa : SL(2,ka) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ka :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi ka)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let epb : SL(2,kb) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) kb :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi kb)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let K : Bool → Type := fun i => cond i kb ka
  let (i : Bool) : Field (K i) := by cases i <;> dsimp [K] <;> infer_instance
  let (i : Bool) : Finite (K i) := by cases i <;> dsimp [K] <;> infer_instance
  let (i : Bool) : CharP (K i) 2 := by cases i <;> dsimp [K] <;> infer_instance
  let e (i : Bool) : (graphLocalGroup F₀ (base F₀ i) ⧸
      pCore 2 (graphLocalGroup F₀ (base F₀ i))) ≃* SL(2,K i) := by
    cases i
    · exact eα.trans epa.symm
    · exact eβ.trans epb.symm
  obtain ⟨n,_,ht,i,p,hp,_,_,_,hcore,_⟩ := source_exists_linear_nonregular_path
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h) K e
  have hn : 4 ≤ n+1 := source_path_length_ge_four_of_core (reduced_triple h)
    (reduced_borel_core_sylow h) p hp hcore (reduced_graph_core_obstruction h)
  exact fun v => ht v 4 hn

private theorem original_linear_beta_escaping_four_walk :
    ∃ c, (graph F₀).Adj (base F₀ true) c ∧ (base F₀ false) ≠ c ∧
      ∃ g ∈ stabilizer F₀ (base F₀ false), g • (base F₀ true) ≠ (base F₀ true) ∧
        ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤
          (Q F₀ (g • (base F₀ true))).map (G₀).subtype ∧
        ∃ p : BasedWalk (graph F₀) 4 (g • c), p.Nonbacktracking ∧
          p.vertices = [g • c,g • (base F₀ true),base F₀ false,base F₀ true,c] := by
  let d := reducedFullEarlierLocalTheorems h
  let ea := (d.localGroup (base F₀ false)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup (base F₀ true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ := source_exists_escaping_four_walk
    (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) (B := (B₀ L₀ S₀).subgroupOf G₀)
    (a := base F₀ false) (b := base F₀ true)
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h) d hc hb hcomm
    (Ma.of_equiv eqa) (.linear m hm (mark.of_mulEquiv eqb))
    (original_linear_beta_four_walk_transitive h hc hb hcomm Ma hm mark)
  exact ⟨c,hbc,hac,g,hga,hgb,
    fun hh => hesc ((map_le_map_iff_of_injective (G₀).subtype_injective).mp hh),p,hp,hpv⟩

/-- Source r=4, s=5 and odd long-path fixers with no alpha marking,
escaping path or initial transitivity assumed. -/
theorem original_linear_beta_source_path_profile :
    HasSourcePathParameters (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) 4 5 ∧
      (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ :=
    original_linear_beta_escaping_four_walk h hc hb hcomm Ma hm mark
  exact original_borel_commuting_source_path_profile_from_local_catalogue h hc hb hcomm
    hbc hac g hga hgb hesc (original_linear_beta_four_walk_transitive h hc hb hcomm Ma hm mark (g • c))
    p hp (by rw [hpv]; simp) (by rw [hpv]; simp) (by rw [hpv]; simp)
    (by rw [hpv]; simp) (by rw [hpv]; simp) Ma (.linear m hm mark)

/-- The literal Chapter 14 consumer on the full-Borel universal tree;
its alpha marking and every Chapter 11 path premise have been discharged. -/
theorem original_linear_beta_tree_path_profile :
    BasedPathTransitive (X := (reducedAmalgam L₀ S₀).Universal)
      (sourceGraph (reducedAmalgam L₀ S₀)) 5 ∧
      ∀ {x y} (q : (sourceGraph (reducedAmalgam L₀ S₀)).Walk x y),
        q.IsPath → q.length = 5 →
          Odd (Nat.card (pathFixer (X := (reducedAmalgam L₀ S₀).Universal) q)) := by
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ :=
    original_linear_beta_escaping_four_walk h hc hb hcomm Ma hm mark
  exact commuting_tree_path_profile_from_local_catalogue h hc hb hcomm
    hbc hac g hga hgb hesc (original_linear_beta_four_walk_transitive h hc hb hcomm Ma hm mark (g • c))
    p hp (by rw [hpv]; simp) (by rw [hpv]; simp) (by rw [hpv]; simp)
    (by rw [hpv]; simp) (by rw [hpv]; simp) Ma (.linear m hm mark)

end Original
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
