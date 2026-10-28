module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BetaCoreLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedSuzukiExclusion
public import Theory.Frattini.Intersection

/-!
# Original beta-core layers and the unitary lower bounds

Injective inclusion preserves the full beta core, its Frattini and derived
subgroups, and its central elementary quotient. The quotient equivalence
uses exactly the image of Z_beta as denominator. It also pulls back
nonelementarity of the original edge-core quotient, so the proved strict
core bounds apply with both original U3 and SU3 markings retained.

At the base edge the two-core is identified with O₂ of the full common
Borel. Thus that literal original branch hypothesis supplies the unitary
marking, exact beta-center order, and strict full-core and central-quotient
lower bounds. The source path, escape, local and catalogue inputs remain
explicit for their existing producers and final source assembly. Exact
unitary core orders, natural sections, special-group equalities and the
remaining general path and marked assembly duties are not inferred here.
Source: DGS85, Groups and Graphs (1985), reduction pp.95--96 and
(11.3)--(11.8), printed pp.169--176.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

private theorem mapped_denominator {H : Type*} [Group H]
    (R N : Subgroup H) (hNR : N ≤ R) (f : H →* G) (hf : Function.Injective f) :
    (N.subgroupOf R).map (R.equivMapOfInjective f hf).toMonoidHom =
      (N.map f).subgroupOf (R.map f) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact mem_map_of_mem f hy
  · intro hx
    obtain ⟨y,hy,heq⟩ := hx
    exact ⟨⟨y,hNR hy⟩,hy,Subtype.ext heq⟩

/-- The whole-core layers transport through the original inclusion; the
quotient denominator is exactly the image of the original beta center. -/
theorem original_reduced_beta_core_layers_on_escaping_path
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
    let R := (Q F₀ b).map (G₀).subtype
    let C := (Z F₀ b).map (G₀).subtype
    (frattini R).map R.subtype ≤ C ∧ ⁅R,R⁆ ≤ C ∧ ⁅⁅R,R⁆,R⁆ = ⊥ ∧
      (∀ x ∈ R, x^4 = 1) ∧ ⁅R,R⁆ ≠ ⊥ ∧
      ∃ hN : (C.subgroupOf R).Normal, letI := hN
        IsElementaryAbelian 2 (R ⧸ C.subgroupOf R) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  let htr := Reduction.reduced_triple h
  obtain ⟨hphi,hder,hcl,hpow,hnon,hN,he⟩ := source_beta_core_layers_on_escaping_path htr
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp
  change ((Z F₀ b).subgroupOf (Q F₀ b)).Normal at hN
  let := hN
  change IsElementaryAbelian 2 (Q F₀ b ⧸ (Z F₀ b).subgroupOf (Q F₀ b)) at he
  let := he
  change (frattini (Q F₀ b)).map (Q F₀ b).subtype ≤ Z F₀ b at hphi
  change ⁅Q F₀ b,Q F₀ b⁆ ≤ Z F₀ b at hder
  change ⁅⁅Q F₀ b,Q F₀ b⁆,Q F₀ b⁆ = ⊥ at hcl
  change ∀ x ∈ Q F₀ b, x^4 = 1 at hpow
  change ⁅Q F₀ b,Q F₀ b⁆ ≠ ⊥ at hnon
  let R := Q F₀ b
  let C := Z F₀ b
  let f := (G₀).subtype
  let e := R.equivMapOfInjective f (G₀).subtype_injective
  have hm := mapped_denominator R C ((source_Z_Q_U htr b).1.trans (map_subtype_le _)) f (G₀).subtype_injective
  have hn : ((C.map f).subgroupOf (R.map f)).Normal := by
    rw [←hm]
    exact Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let := hn
  let eq := QuotientGroup.congr _ _ e hm
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,hn,IsElementaryAbelian.of_surjective eq.toMonoidHom eq.surjective⟩
  · rw [frattini_image_map _ f (G₀).subtype_injective]
    exact map_mono hphi
  · rw [←map_commutator]
    exact map_mono hder
  · rw [←map_commutator,←map_commutator,hcl,Subgroup.map_bot]
  · rintro x ⟨y,hy,rfl⟩
    rw [←map_pow,hpow y hy,map_one]
  · intro hh
    apply hnon
    apply map_injective (G₀).subtype_injective
    rw [map_commutator,Subgroup.map_bot]
    exact hh

/-- The selected original U3 or SU3 row retains its exact beta-center
order and satisfies the strict full-core and central-quotient lower bounds. -/
theorem original_reduced_unitary_beta_core_bounds_on_escaping_path
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
    (hne : ∃ hN : (((Q F₀ b).map (G₀).subtype).subgroupOf
        (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 ((((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) ⧸
        ((Q F₀ b).map (G₀).subtype).subgroupOf
          (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype)))  :
    let qα := ((Q F₀ a).map (G₀).subtype).relIndex
      ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype)
    ∃ n, 0 < n ∧
      (ClassicalGroup.IsPSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^n) ∨
       IsSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^n)) ∧
      Nat.card ((Z F₀ b).map (G₀).subtype) = 2^n ∧
      qα^2 * 2^n < Nat.card ((Q F₀ b).map (G₀).subtype) ∧
      qα^2 < ((Z F₀ b).map (G₀).subtype).relIndex ((Q F₀ b).map (G₀).subtype) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  let htr := Reduction.reduced_triple h
  obtain ⟨n,hn,mark,hcard⟩ := original_reduced_unitary_beta_on_escaping_path h d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne
  let R := (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2
  let Qb := Q F₀ b
  have hQR : Qb ≤ R := by
    have hh := Noncommuting.graph_Q_le_edgeCore htr (source_critical_one_adjacent hc hb).symm
    change Q F₀ b ≤ (stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2 at hh
    change Q F₀ b ≤ (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2
    rwa [inf_comm (stabilizer F₀ b) (stabilizer F₀ a)] at hh
  let hN : (Qb.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Q _ b))
  have hnot : ¬ IsElementaryAbelian 2 (R ⧸ Qb.subgroupOf R) := by
    intro he
    let := he
    obtain ⟨hn',hh⟩ := hne
    let := hn'
    let e := R.equivMapOfInjective (G₀).subtype (G₀).subtype_injective
    let eq := QuotientGroup.congr _ _ e (mapped_denominator R Qb hQR (G₀).subtype (G₀).subtype_injective)
    exact hh (IsElementaryAbelian.of_surjective eq.toMonoidHom eq.surjective)
  have hl := source_nonElementary_beta_core_lower_bound_on_escaping_path htr
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp ⟨hN,hnot⟩
  have hz := source_center_card_eq_critical_index_on_escaping_path htr
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp
  change Nat.card (Z F₀ b) = (Q F₀ b).relIndex (Z F₀ a) at hz
  change ((Q F₀ a).relIndex (Z F₀ c ⊓ Q F₀ b))^2 * (Q F₀ b).relIndex (Z F₀ a) < Nat.card (Q F₀ b) ∧
    ((Q F₀ a).relIndex (Z F₀ c ⊓ Q F₀ b))^2 < (Z F₀ b).relIndex (Q F₀ b) at hl
  have hi : (Q F₀ b).relIndex (Z F₀ a) = 2^n := hz.symm.trans (by
    rwa [card_map_of_injective (G₀).subtype_injective] at hcard)
  dsimp only at hl ⊢
  rw [hi] at hl
  refine ⟨n,hn,mark,hcard,?_⟩
  simpa only [←map_inf _ _ _ (G₀).subtype_injective,
    relIndex_map_map_of_injective _ _ (G₀).subtype_injective,
    card_map_of_injective (G₀).subtype_injective] using hl

/-- The unitary core bounds apply to nonelementarity of the quotient of
O₂ of the full original common Borel by the actual beta-core image. -/
theorem original_borel_unitary_core_bounds_on_escaping_path
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
    let qα := ((Q F₀ (base F₀ false)).map (G₀).subtype).relIndex
      ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ (base F₀ true)).map (G₀).subtype)
    ∃ n, 0 < n ∧
      (ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^n) ∨
      IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^n)) ∧
      Nat.card ((Z F₀ (base F₀ true)).map (G₀).subtype) = 2^n ∧
      qα^2 * 2^n < Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) ∧
      qα^2 < ((Z F₀ (base F₀ true)).map (G₀).subtype).relIndex
        ((Q F₀ (base F₀ true)).map (G₀).subtype) := by
  let R := (stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2
  have htr := Reduction.reduced_triple h
  have hBG : Reduction.B₀ L₀ S₀ ≤ G₀ :=
    (show Reduction.B₀ L₀ S₀ ≤ Reduction.P₀ L₀ S₀ 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L₀ S₀) ≤ G₀ :=
    (show twoCore (commonBorel L₀ S₀) ≤ Reduction.B₀ L₀ S₀ from le_sup_right).trans hBG
  have hmap : R.map (G₀).subtype = twoCore (commonBorel L₀ S₀) := by
    dsimp only [R]
    rw [show stabilizer F₀ (base F₀ false) = F₀ false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F₀ (base F₀ true) = F₀ true from Subgroup.CosetGeometry.stabilizer_base _ _,
      show F₀ false ⊓ F₀ true = (Reduction.B₀ L₀ S₀).subgroupOf G₀ from htr.intersection,
      pCoreIn_subgroupOf 2 _ _ hBG,Reduction.B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  apply original_reduced_unitary_beta_core_bounds_on_escaping_path h d hc hb hcomm hbc hac Ma Mb
    g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  change ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (R.map (G₀).subtype)).Normal,
    letI := hN
    ¬ IsElementaryAbelian 2 (R.map (G₀).subtype ⧸
      ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (R.map (G₀).subtype))
  rw [hmap]
  exact hne

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
