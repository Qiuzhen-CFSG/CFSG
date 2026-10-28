module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SuzukiExclusion

/-!
# Original Suzuki exclusion and the full-Borel unitary alternative

The actual inclusion of the reduced completion transports both local
quotient markings to the source geometry, excludes every Suzuki parameter,
and returns the unitary alternative to the original beta quotient.
An explicit quotient equivalence transports nonelementarity of the
original edge radical modulo the original beta core. At the base edge,
that radical is identified with the two-core of the full common Borel.
The selected U3 or SU3 marking retains its positive fixed-field degree
and the beta center has exactly that field order.

The local data, catalogue, transitive source path and its escaping choice
remain explicit earlier-source inputs. No natural section, special-core
structure or completed unitary amalgam is inferred from these alternatives;
the remaining (11.8) layers, paths and marked assembly stay with this owner.
Source: DGS85, Groups and Graphs (1985), reduction pp.95--96,
(11.6)(c) and (11.8)(c), printed pp.174--176.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- Suzuki exclusion for the original marked beta quotient at every parameter. -/
theorem original_reduced_suzuki_exclusion_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b)
    (hesc : ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (g • b)).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (m : ℕ) (eb : ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eβ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqβ := QuotientGroup.congr _ _ eβ (pCore_map_iso 2 eβ)
  exact source_suzuki_exclusion_on_escaping_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) g hga hgb (fun hh => hesc (map_mono hh))
    ht p hp ha hbp hcp hgbp hgcp m (eqβ.trans eb)

private theorem nonElementary_of_mapped_quotient {H : Type*} [Group H]
    (R N : Subgroup H) (hNR : N ≤ R) (f : H →* G) (hf : Function.Injective f)
    [(N.subgroupOf R).Normal]
    (hne : ∃ hn : ((N.map f).subgroupOf (R.map f)).Normal, letI := hn
      ¬ IsElementaryAbelian 2 (R.map f ⧸ (N.map f).subgroupOf (R.map f))) :
    ¬ IsElementaryAbelian 2 (R ⧸ N.subgroupOf R) := by
  intro he
  obtain ⟨hn,hne⟩ := hne
  let := hn
  let := he
  let e := R.equivMapOfInjective f hf
  have hmap : (N.subgroupOf R).map e.toMonoidHom = (N.map f).subgroupOf (R.map f) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact mem_map_of_mem f hy
    · intro hx
      obtain ⟨y,hy,heq⟩ := hx
      exact ⟨⟨y,hNR hy⟩,hy,Subtype.ext heq⟩
  let eq := QuotientGroup.congr _ _ e hmap
  exact hne (IsElementaryAbelian.of_surjective eq.toMonoidHom eq.surjective)

/-- The original edge-core quotient selects U3 or SU3, retaining the actual
positive field parameter and beta-center order. -/
theorem original_reduced_unitary_beta_on_escaping_path
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
          (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype))) :
    ∃ n, 0 < n ∧
      (ClassicalGroup.IsPSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^n) ∨
      IsSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^n)) ∧
      Nat.card ((Z F₀ b).map (G₀).subtype) = 2^n := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  let htr := Reduction.reduced_triple h
  let R := (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2
  let hN : ((Q F₀ b).subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_right).trans (stabilizer_normalizes_Q _ _))
  have hQR : Q F₀ b ≤ R := by
    have hh := Noncommuting.graph_Q_le_edgeCore htr (source_critical_one_adjacent hc hb).symm
    change Q F₀ b ≤ (stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2 at hh
    rwa [inf_comm (stabilizer F₀ b) (stabilizer F₀ a)] at hh
  have hn := nonElementary_of_mapped_quotient R (Q F₀ b) hQR
    (G₀).subtype (G₀).subtype_injective hne
  obtain ⟨n,hnpos,mark⟩ := source_unitary_beta_on_escaping_path htr
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp ⟨hN,hn⟩
  have hcard := source_unitary_center_card_on_escaping_path htr
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp n hnpos mark
  refine ⟨n,hnpos,?_,?_⟩
  · rcases mark with hm | hm
    · exact Or.inl (hm.of_mulEquiv eqb.symm)
    · obtain ⟨E,hE,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
      exact Or.inr ⟨E,hE,hfin,J,hcard,hconj,⟨eqb.symm.trans e⟩⟩
  · rw [card_map_of_injective (G₀).subtype_injective]
    exact hcard

/-- The nonelementary branch on the full original Borel selects the actual
unitary beta marking and its field-sized center. -/
theorem original_borel_unitary_beta_on_escaping_path
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
    ∃ n, 0 < n ∧
      (ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^n) ∨
      IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^n)) ∧
      Nat.card ((Z F₀ (base F₀ true)).map (G₀).subtype) = 2^n := by
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
  apply original_reduced_unitary_beta_on_escaping_path h d hc hb hcomm hbc hac Ma Mb
    g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  change ∃ hN : (((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (R.map (G₀).subtype)).Normal,
    letI := hN
    ¬ IsElementaryAbelian 2 (R.map (G₀).subtype ⧸
      ((Q F₀ (base F₀ true)).map (G₀).subtype).subgroupOf (R.map (G₀).subtype))
  rw [hmap]
  exact hne

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
