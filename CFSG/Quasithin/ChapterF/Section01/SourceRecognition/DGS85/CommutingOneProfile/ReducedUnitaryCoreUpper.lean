module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryCoreUpper
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedFieldParameters

/-!
# Original unitary core and full-Borel upper bounds

The literal reduced-to-original inclusion transports the three-neighbor
intersection bound and its indices. For a unitary fixed-field degree m ≥ 2,
this bounds the actual beta core by 2^(7m) and the edge two-core by 2^(10m).
At the base edge that two-core is O₂ of the full original common Borel.
Both original unitary quotient markings and the same field degree are kept.
ReducedUnitaryCoreOrders supplies matching bounds for m ≥ 2. The binary
case and natural section still require their source arguments.
Source: DGS85, Groups and Graphs (1985), (11.8)(ii), printed p.176.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- All whole-core upper bounds through the original inclusion. -/
theorem original_reduced_unitary_core_upper_on_escaping_path
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
    (m : ℕ) (hm : 2 ≤ m)
    (mark : ClassicalGroup.IsPSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^m) ∨
      IsSU ((d.localGroup b).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup b).map (G₀).subtype)) 3 (2^m)) :
    let qα := ((Q F₀ a).map (G₀).subtype).relIndex
      ((Z F₀ c).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype)
    let qβ := ((Q F₀ b).map (G₀).subtype).relIndex ((Z F₀ a).map (G₀).subtype)
    ((Z F₀ b).map (G₀).subtype).relIndex ((Q F₀ b).map (G₀).subtype) ≤ qα^3 ∧
      Nat.card ((Q F₀ b).map (G₀).subtype) ≤ qα^3*qβ ∧
      Nat.card ((Q F₀ b).map (G₀).subtype) ≤ 2^(7*m) ∧
      Nat.card (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2).map (G₀).subtype) ≤ 2^(10*m) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hbound := source_unitary_core_upper_on_escaping_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp hm
    (by
      rcases mark with hh | ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
      · exact Or.inl (hh.of_mulEquiv eqb)
      · exact Or.inr ⟨E,inferInstance,inferInstance,J,hcard,hconj,⟨eqb.trans e⟩⟩)
  dsimp only
  simp only [←map_inf _ _ _ (G₀).subtype_injective,
    relIndex_map_map_of_injective _ _ (G₀).subtype_injective,
    card_map_of_injective (G₀).subtype_injective]
  exact hbound

/-- The upper bound for O₂ of the full original common Borel, with both
unitary covers and their original marking retained. -/
theorem original_borel_unitary_core_upper_on_escaping_path
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
    (m : ℕ) (hm : 2 ≤ m)
    (mark : ClassicalGroup.IsPSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
      IsSU ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 3 (2^m)) :
    Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) ≤ 2^(7*m) ∧
      Nat.card (twoCore (commonBorel L₀ S₀)) ≤ 2^(10*m) := by
  have hbound := (original_reduced_unitary_core_upper_on_escaping_path h d hc hb hcomm hbc hac
    Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp m hm mark).2.2
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
  exact ⟨hbound.1,hmap ▸ hbound.2⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
