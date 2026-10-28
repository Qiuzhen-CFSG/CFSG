module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SmallAlphaExclusions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoreGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearBetaCores
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RemoteLayerVanishing
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NeighborActions
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# Odd five-walk fixers in the general elementary branch

The two alpha cores on a beta turn meet in the beta center. The remote
layer theorem separates that center from the opposite beta core. A
2-subgroup fixing a five-edge chain lies in all three cores, so it is
trivial. Conjugating the middle edge and reversing walks gives odd
fixers in both orientations, including closed nonbacktracking walks.

Both linear fields are arbitrary. The genuine quotient isomorphisms and
the earlier escaping source path remain explicit; LinearPathParameters
selects the fields from the original full-Borel elementary branch.
Source: DGS85, Groups and Graphs (1985), (11.6)--(11.7), pp.172--175.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]
variable {k' : Type*} [Field k'] [Finite k'] [CharP k' 2]

/-- The actual three-core intersection that controls elementary five-walks. -/
theorem source_linear_three_core_intersection_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k'))
    {t w : Vertex (family P)} (hat : (graph (family P)).Adj a t) (htb : t ≠ b)
    (hbw : (graph (family P)).Adj b w) (haw : a ≠ w) :
    Q (family P) a ⊓ Q (family P) w ⊓ Q (family P) t = ⊥ := by
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  have hQa := source_linear_linear_core_eq_center h hB d hc hb hcomm hbc hac Ma ea Mb eb
  have hpair := (source_linear_rankOne_center_intersections h hB d hc hb hcomm hbw haw Ma Mb ea).1
  have hI := source_linear_linear_neighbor_intersection_eq_center h hB d hc hb hcomm hbc hac Ma ea Mb eb
  have hz := source_linear_rankOne_layer_eq_bot_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb ea g hga hgb hesc ht p hp ha hbp hgbp hgcp
  rw [hI] at hz
  have hag : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [show g • a = a from hga] at hh
  have htrans := (source_edge_transitive_or_dihedral h hB d hab Ma).resolve_right (by
    rintro ⟨e⟩
    exact source_alpha_dihedral_exclusion h hB d hc hb hcomm hbc hac Mb e)
  obtain ⟨u,hu,hut⟩ := htrans (g • b) t hag hat hgb htb
  have hub : u • b = b := hu.2
  have hd := congrArg (fun X : Subgroup G => X.map (MulAut.conj u).toMonoidHom) hz
  rw [Subgroup.map_inf _ _ _ (MulAut.conj u).injective,←Z_translate,←Q_translate,
    hub,hut,Subgroup.map_bot] at hd
  rw [hQa,hpair,hd]

private def turn_quotient_conjugate (d : EarlierLocalTheorems (family P))
    (a : Vertex (family P)) (g : G) :
    (d.localGroup (g • a) ⧸ pCore 2 (d.localGroup (g • a))) ≃*
      (d.localGroup a ⧸ pCore 2 (d.localGroup a)) := by
  let e := (MulEquiv.subgroupCongr (d.conjugate g a)).trans
    ((d.localGroup a).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  exact QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

/-- Odd fixers for all nonbacktracking five-edge chains with the given middle edge.
The extra source-path premises are used only for the earlier core structure. -/
theorem source_linear_five_edge_fixer_odd_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k'))
    {v₀ t w v₅ : Vertex (family P)}
    (h0t : (graph (family P)).Adj v₀ t) (hta : (graph (family P)).Adj t a)
    (hbw : (graph (family P)).Adj b w) (hw5 : (graph (family P)).Adj w v₅)
    (h0a : v₀ ≠ a) (htb : t ≠ b) (haw : a ≠ w) (hb5 : b ≠ v₅) :
    Odd (Nat.card (stabilizer (family P) v₀ ⊓ stabilizer (family P) t ⊓
      stabilizer (family P) a ⊓ stabilizer (family P) b ⊓
      stabilizer (family P) w ⊓ stabilizer (family P) v₅ : Subgroup G)) := by
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨u,hua,hub⟩ := locally_transitive (family P) hab hta.symm
  have hub' : u • b = t := hub
  have Mt : IsRankOneModel (d.localGroup t ⧸ pCore 2 (d.localGroup t)) := by
    rw [←hub']
    exact Mb.of_equiv (turn_quotient_conjugate d b u)
  obtain ⟨z,hzb,hza⟩ := locally_transitive (family P) hab.symm hbw
  have hza' : z • a = w := hza
  have Mw : IsRankOneModel (d.localGroup w ⧸ pCore 2 (d.localGroup w)) := by
    rw [←hza']
    exact Ma.of_equiv (turn_quotient_conjugate d a z)
  have hzero := source_linear_three_core_intersection_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hgbp hgcp ea eb
    hta.symm htb hbw haw
  let D := stabilizer (family P) v₀ ⊓ stabilizer (family P) t ⊓
    stabilizer (family P) a ⊓ stabilizer (family P) b ⊓
    stabilizer (family P) w ⊓ stabilizer (family P) v₅
  have hD0 : D ≤ stabilizer (family P) v₀ := fun _ hx => hx.1.1.1.1.1
  let : Finite D := Finite.of_injective (inclusion hD0) (inclusion_injective _)
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 hd
  let A := zpowers (x : G)
  have hpA : IsPGroup 2 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    change Nat.card (zpowers (x : G)) ∣ 2^1
    rw [Nat.card_zpowers,Subgroup.orderOf_coe,hx]; decide)
  have hAD : A ≤ D := zpowers_le.mpr x.property
  have hA0 : A ≤ stabilizer (family P) v₀ := hAD.trans hD0
  have hAt : A ≤ stabilizer (family P) t := hAD.trans (fun _ hx => hx.1.1.1.1.2)
  have hAa : A ≤ stabilizer (family P) a := hAD.trans (fun _ hx => hx.1.1.1.2)
  have hAb : A ≤ stabilizer (family P) b := hAD.trans (fun _ hx => hx.1.1.2)
  have hAw : A ≤ stabilizer (family P) w := hAD.trans (fun _ hx => hx.1.2)
  have hA5 : A ≤ stabilizer (family P) v₅ := hAD.trans inf_le_right
  have hAtQ := source_two_neighbor_two_group_le_core h hB d h0t hta h0a Mt A hpA hA0 hAt hAa
  have hAaQ := source_two_neighbor_two_group_le_core h hB d hta hab htb Ma A hpA hAt hAa hAb
  have hAwQ := source_two_neighbor_two_group_le_core h hB d hbw hw5 hb5 Mw A hpA hAb hAw hA5
  have hA : A = ⊥ := bot_unique ((le_inf (le_inf hAaQ hAwQ) hAtQ).trans hzero.le)
  have hx1 : x = 1 := Subtype.ext (mem_bot.mp (hA ▸ mem_zpowers (x : G)))
  simp only [hx1,orderOf_one] at hx
  omega

open SimpleGraph.Walk Theory.GroupTheory.WeakBNPair.RegularTree

private theorem bool_opposite_unique {a b c : Bool} (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem five_walk_fixer_odd_oriented
    {F : Bool → Subgroup G} [∀ i, Finite (F i)]
    {a b : Vertex F} (hab : (graph F).Adj a b)
    (hfix : ∀ {v₀ t w v₅ : Vertex F},
      (graph F).Adj v₀ t → (graph F).Adj t a → (graph F).Adj b w → (graph F).Adj w v₅ →
      v₀ ≠ a → t ≠ b → a ≠ w → b ≠ v₅ →
      Odd (Nat.card (stabilizer F v₀ ⊓ stabilizer F t ⊓ stabilizer F a ⊓
        stabilizer F b ⊓ stabilizer F w ⊓ stabilizer F v₅ : Subgroup G)))
    {x y : Vertex F} (q : (graph F).Walk x y) (hlen : q.length = 5)
    (hnb : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2))
    (ha : (q.getVert 2).type = a.type) : Odd (Nat.card (pathFixer (X := G) q)) := by
  have h23 := q.adj_getVert_succ (by omega : 2 < q.length)
  have hb : (q.getVert 3).type = b.type :=
    bool_opposite_unique h23.1 (ha ▸ hab.1)
  obtain ⟨s,hsa,hsb⟩ := incident_common_translate F hab.2
  obtain ⟨t,hta,htb⟩ := incident_common_translate F h23.2
  rw [ha] at hta
  rw [hb] at htb
  let u := t*s⁻¹
  have hua : u • a = q.getVert 2 := by
    rw [←hsa]
    change (t*s⁻¹) • (s • base F a.type) = _
    rw [mul_smul,inv_smul_smul,hta]
  have hub : u • b = q.getVert 3 := by
    rw [←hsb]
    change (t*s⁻¹) • (s • base F b.type) = _
    rw [mul_smul,inv_smul_smul,htb]
  let e := Subgroup.CosetGeometry.translationGraphIso F u⁻¹
  let p := q.map e.toHom
  have hpl : p.length = 5 := by rw [length_map,hlen]
  have hpa : p.getVert 2 = a := by
    change (q.map e.toHom).getVert 2 = _
    rw [getVert_map]
    change u⁻¹ • q.getVert 2 = a
    rw [←hua,inv_smul_smul]
  have hpb : p.getVert 3 = b := by
    change (q.map e.toHom).getVert 3 = _
    rw [getVert_map]
    change u⁻¹ • q.getVert 3 = b
    rw [←hub,inv_smul_smul]
  have hpn (i : ℕ) (hi : i+2 ≤ p.length) : p.getVert i ≠ p.getVert (i+2) := by
    change (q.map e.toHom).getVert i ≠ (q.map e.toHom).getVert (i+2)
    simp only [getVert_map]
    exact fun he => hnb i (by omega) (e.injective he)
  have hadj (i : ℕ) (hi : i < 5) := p.adj_getVert_succ (by omega : i < p.length)
  have ho := hfix (hadj 0 (by decide))
    (by simpa only [hpa] using hadj 1 (by decide))
    (by simpa only [hpb] using hadj 3 (by decide)) (hadj 4 (by decide))
    (by simpa only [hpa] using hpn 0 (by omega))
    (by simpa only [hpb] using hpn 1 (by omega))
    (by simpa only [hpa] using hpn 2 (by omega))
    (by simpa only [hpb] using hpn 3 (by omega))
  have hpo : Odd (Nat.card (pathFixer (X := G) p)) := by
    apply Odd.of_dvd_nat ho
    apply card_dvd_of_le
    intro x hx
    exact ⟨⟨⟨⟨⟨hx 0 (by omega),hx 1 (by omega)⟩,hpa ▸ hx 2 (by omega)⟩,
      hpb ▸ hx 3 (by omega)⟩,hx 4 (by omega)⟩,hx 5 (by omega)⟩
  have he := pathFixer_map_conj q p u⁻¹ (by rw [length_map]) (by
    intro i hi
    change u⁻¹ • q.getVert i = (q.map e.toHom).getVert i
    rw [getVert_map]
    rfl)
  rw [←he,card_map_of_injective (MulAut.conj u⁻¹).injective] at hpo
  exact hpo

private theorem five_walk_fixer_odd_of_middle_edge
    {F : Bool → Subgroup G} [∀ i, Finite (F i)]
    {a b : Vertex F} (hab : (graph F).Adj a b)
    (hfix : ∀ {v₀ t w v₅ : Vertex F},
      (graph F).Adj v₀ t → (graph F).Adj t a → (graph F).Adj b w → (graph F).Adj w v₅ →
      v₀ ≠ a → t ≠ b → a ≠ w → b ≠ v₅ →
      Odd (Nat.card (stabilizer F v₀ ⊓ stabilizer F t ⊓ stabilizer F a ⊓
        stabilizer F b ⊓ stabilizer F w ⊓ stabilizer F v₅ : Subgroup G)))
    {x y : Vertex F} (q : (graph F).Walk x y) (hlen : q.length = 5)
    (hnb : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) :
    Odd (Nat.card (pathFixer (X := G) q)) := by
  by_cases ha : (q.getVert 2).type = a.type
  · exact five_walk_fixer_odd_oriented hab hfix q hlen hnb ha
  have ha3 : (q.getVert 3).type = a.type :=
    bool_opposite_unique (q.adj_getVert_succ (by omega : 2 < q.length)).1 ha
  have hnb' : ∀ i, i+2 ≤ q.reverse.length →
      q.reverse.getVert i ≠ q.reverse.getVert (i+2) := by
    intro i hi
    rw [length_reverse,hlen] at hi
    simp only [getVert_reverse,hlen]
    convert (hnb (3-i) (by omega)).symm using 1 <;> congr 1 <;> omega
  have ho := five_walk_fixer_odd_oriented hab hfix q.reverse (by rwa [length_reverse]) hnb'
    (by simpa only [getVert_reverse,hlen] using ha3)
  rwa [pathFixer_reverse] at ho

/-- Every nonbacktracking five-walk has odd fixer, in both orientations and
without requiring the source graph to be a tree. -/
theorem source_linear_five_walk_fixer_odd_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k'))
    {x y : Vertex (family P)} (q : (graph (family P)).Walk x y) (hlen : q.length = 5)
    (hnb : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) :
    Odd (Nat.card (pathFixer (X := G) q)) := by
  let := finite_endpoints h
  apply five_walk_fixer_odd_of_middle_edge (source_critical_one_adjacent hc hb) ?_ q hlen hnb
  intro v₀ t w v₅ h0t hta hbw hw5 h0a htb haw hb5
  exact source_linear_five_edge_fixer_odd_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hgbp hgcp ea eb
    h0t hta hbw hw5 h0a htb haw hb5

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
