module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceFieldParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedCenterOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBetaCoreLayers

/-!
# Original field parameters and the full-Borel unitary application

The actual reduced-group inclusion preserves both relative indices in
(11.6)(d). Transporting the proved field equation also retains the alpha
quotient marking. On the nonelementary full-Borel branch the existing beta
selection supplies its fixed-field degree m, in either U3 or SU3. Alpha
then has field order 2^(2m), the alpha center has order 2^(4m), each seed
has order 2^(3m), and their pair span has order 2^(5m). The lower bound on
the whole beta core is now expressed in that same fixed field.

These are applications to the original quotients and inclusions. They do
not assert the remaining upper bound on the whole unitary core, the
natural alpha section, or the path-fixer clauses. The earlier local data,
rank-one catalogue and escaping source path retain their source producers.
Source: DGS85, Groups and Graphs (1985), (11.6)(c,d), (11.8),
printed pp.172--176; original reduction pp.95--96.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The full source field equation at the original inclusion, with its actual alpha marking. -/
theorem original_reduced_field_parameters_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b)
    (hesc : ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (g • b)).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    let qα := ((Q F₀ a).map (G₀).subtype).relIndex
      ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype)
    let qβ := ((Q F₀ b).map (G₀).subtype).relIndex ((Z F₀ a).map (G₀).subtype)
    qα = qβ^2 ∧
      ∃ n, 1 < n ∧ ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2^n) ∧ 2^n = qα := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  obtain ⟨he,n,hn,hi,hq⟩ := source_field_parameters_on_escaping_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp
  dsimp only
  simp only [←map_inf _ _ _ (G₀).subtype_injective,
    relIndex_map_map_of_injective _ _ (G₀).subtype_injective]
  exact ⟨he,n,hn,hi.of_mulEquiv eqa.symm,hq⟩

/-- A specified original unitary degree determines the alpha degree and all center and seed orders. -/
theorem original_reduced_unitary_field_orders_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b)
    (hesc : ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (g • b)).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (m : ℕ) (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^m) ∨
      IsSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^m)) :
    ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2^(2*m)) ∧
      ((Q F₀ a).map (G₀).subtype).relIndex
        ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype) = 2^(2*m) ∧
      Nat.card ((Z F₀ b).map (G₀).subtype) = 2^m ∧
      Nat.card ((Z F₀ a).map (G₀).subtype) = 2^(4*m) ∧
      Nat.card ((Z F₀ a).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype : Subgroup G) = 2^(3*m) ∧
      Nat.card (pairSpan ((Z F₀ a).map (G₀).subtype) ((Z F₀ c).map (G₀).subtype)
        ((Q F₀ b).map (G₀).subtype)) = 2^(5*m) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hzb := source_unitary_center_card_on_escaping_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp m hm
    (by
      rcases mark with hh | ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
      · exact Or.inl (hh.of_mulEquiv eqb)
      · exact Or.inr ⟨E,inferInstance,inferInstance,J,hcard,hconj,⟨eqb.trans e⟩⟩)
  have hzb' : Nat.card ((Z F₀ b).map (G₀).subtype) = 2^m := by
    rwa [card_map_of_injective (G₀).subtype_injective]
  obtain ⟨he,n,hn,hi,hq⟩ := original_reduced_field_parameters_on_escaping_path
    h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  obtain ⟨_,_,hβ,hseed,hza,hpair⟩ := original_reduced_center_orders_on_escaping_path
    h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hβ' := hβ.symm.trans hzb'
  have hα : ((Q F₀ a).map (G₀).subtype).relIndex
      ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype) = 2^(2*m) := by
    rw [he,hβ',←pow_mul,Nat.mul_comm m 2]
  have hn' : n = 2*m := Nat.pow_right_injective (by decide : 1 < 2) (hq.trans hα)
  rw [hn'] at hi
  refine ⟨hi,hα,hzb',?_,?_,?_⟩
  · rw [hza,hα,hβ',←pow_mul,←pow_add]
    congr 1
    omega
  · rw [hseed,hα,hβ',←pow_add]
    congr 1
    omega
  · rw [hpair,hα,hβ',←pow_mul,←pow_add]
    congr 1
    omega

/-- The actual nonelementary full-Borel branch, with both field markings and the source seed orders derived. -/
theorem original_borel_unitary_field_profile_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {c : Vertex F₀} (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (hbc : (graph F₀).Adj (base F₀ true) c) (hac : (base F₀ false) ≠ c)
    (Ma : IsRankOneModel ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ (base F₀ false)) (hgb : g • (base F₀ true) ≠ (base F₀ true))
    (hesc : ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤ (Q F₀ (g • (base F₀ true))).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : (base F₀ false) ∈ p.vertices) (hbp : (base F₀ true) ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • (base F₀ true) ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf
        (twoCore (commonBorel L₀ S₀))).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (twoCore (commonBorel L₀ S₀) ⧸
        ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (twoCore (commonBorel L₀ S₀)))) :
    ∃ m, 0 < m ∧
      ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
      (ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
      IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m)) ∧
      Nat.card ((Z F₀ (base F₀ true)).map (G₀).subtype) = 2^m ∧
      Nat.card ((Z F₀ (base F₀ false)).map (G₀).subtype) = 2^(4*m) ∧
      Nat.card ((Z F₀ (base F₀ false)).map (G₀).subtype ⊓
        (Q F₀ (base F₀ true)).map (G₀).subtype : Subgroup G) = 2^(3*m) ∧
      Nat.card (pairSpan ((Z F₀ (base F₀ false)).map (G₀).subtype) ((Z F₀ c).map (G₀).subtype)
        ((Q F₀ (base F₀ true)).map (G₀).subtype)) = 2^(5*m) ∧
      2^(5*m) < Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) ∧
      2^(4*m) < ((Z F₀ (base F₀ true)).map (G₀).subtype).relIndex
        ((Q F₀ (base F₀ true)).map (G₀).subtype) := by
  obtain ⟨m,hm,mark,_,hlower,hindex⟩ := original_borel_unitary_core_bounds_on_escaping_path
    h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne
  obtain ⟨hi,hα,hzb,hza,hseed,hpair⟩ := original_reduced_unitary_field_orders_on_escaping_path
    h d hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp m hm mark
  rw [hα] at hlower hindex
  have hfour : (2^(2*m))^2 = 2^(4*m) := by
    rw [←pow_mul]
    congr 1
    omega
  have hfive : (2^(2*m))^2 * 2^m = 2^(5*m) := by
    rw [hfour,←pow_add]
    congr 1
    omega
  rw [hfive] at hlower
  rw [hfour] at hindex
  exact ⟨m,hm,hi,mark,hzb,hza,hseed,hpair,hlower,hindex⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
