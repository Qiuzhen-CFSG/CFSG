module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearPathFixers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBinaryBetaPaths

/-!
# Original linear quotient markings and long-walk fixers

Both actual linear quotient markings are pulled back through the original
reduced-group inclusion. They give the two valences and apply the three-core
argument to every five-walk; taking prefixes gives odd fixers for all longer
nonbacktracking walks. The original fixer image is retained literally.

ElementaryPathParameters uses these results after selecting both fields
from the full original Borel. The earlier local and escaping-path premises
remain explicit. Source: DGS85, Groups and Graphs (1985), (11.7)(f), pp.174--175.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon SimpleGraph.Walk
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

private theorem linear_coordinates {H : Type*} [Group H] {n : ℕ}
    (hM : ClassicalGroup.IsPSL H 2 (2^n)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      Nat.card k = 2^n ∧ Nonempty (H ≃* SL(2,k)) := by
  obtain ⟨k,hk,hfin,hcard,⟨e⟩⟩ := hM
  let := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let f : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact ⟨k,hk,hfin,inferInstance,hcard,⟨e.trans f.symm⟩⟩

/-- Actual valences at both original linear endpoints, for arbitrary fields. -/
theorem original_reduced_linear_neighbor_cards
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (markα : ClassicalGroup.IsPSL ((d.localGroup (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ false)).map (G₀).subtype)) 2 (2^n))
    (markβ : ClassicalGroup.IsPSL ((d.localGroup (base F₀ true)).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup (base F₀ true)).map (G₀).subtype)) 2 (2^m))
    (v : Vertex F₀) :
    Nat.card ((graph F₀).neighborSet v) = 2^(if v.type then m else n)+1 := by
  let ea₀ := (d.localGroup (base F₀ false)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea₀ (pCore_map_iso 2 ea₀)
  let eb₀ := (d.localGroup (base F₀ true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  have markα' := markα.of_mulEquiv eqa
  have markβ' := markβ.of_mulEquiv eqb
  have hab : (graph F₀).Adj (base F₀ false) (base F₀ true) :=
    ⟨Bool.false_ne_true,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,_,_,_,hk,⟨ea⟩⟩ := linear_coordinates markα'
  obtain ⟨k',_,_,_,hk',⟨eb⟩⟩ := linear_coordinates markβ'
  have hα := source_linear_neighbor_card (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hab.symm (.linear n hn markα') ea
  have hβ := source_linear_neighbor_card (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hab (.linear m hm markβ') eb
  rw [hk] at hα
  rw [hk'] at hβ
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F₀ v
  have he := Nat.card_congr
    ((Subgroup.CosetGeometry.translationGraphIso F₀ g).mapNeighborSet (base F₀ v.type))
  change Nat.card ((graph F₀).neighborSet (base F₀ v.type)) =
    Nat.card ((graph F₀).neighborSet (g • base F₀ v.type)) at he
  rw [hg] at he
  rw [←he]
  cases v.type
  · exact hα
  · exact hβ

/-- Odd long-walk fixers with both original linear quotient markings. -/
theorem original_reduced_linear_long_walk_fixer_odd_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (markα : ClassicalGroup.IsPSL ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)) 2 (2^n))
    (markβ : ClassicalGroup.IsPSL ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)) 2 (2^m))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b)
    (hesc : ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (g • b)).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    {x y : Vertex F₀} (q : (graph F₀).Walk x y) (hlen : 5 ≤ q.length)
    (hnb : ∀ i, i+2 ≤ q.length → q.getVert i ≠ q.getVert (i+2)) :
    Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  let eL := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)
  let eR := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)
  have markα' := markα.of_mulEquiv eqa
  have markβ' := markβ.of_mulEquiv eqb
  obtain ⟨k,_,_,_,_,⟨ea⟩⟩ := linear_coordinates markα'
  obtain ⟨k',_,_,_,_,⟨eb⟩⟩ := linear_coordinates markβ'
  have hlen5 : (q.take 5).length = 5 := by rw [take_length,Nat.min_eq_left hlen]
  have hnb5 : ∀ i, i+2 ≤ (q.take 5).length →
      (q.take 5).getVert i ≠ (q.take 5).getVert (i+2) := by
    intro i hi
    rw [hlen5] at hi
    simpa only [take_getVert,Nat.min_eq_right (show i ≤ 5 by omega),
      Nat.min_eq_right (show i+2 ≤ 5 by omega)] using hnb i (by omega)
  have ho : Odd (Nat.card (pathFixer (X := G₀) (q.take 5))) :=
    source_linear_five_walk_fixer_odd_on_escaping_path
      (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) d hc hb hcomm hbc hac
      (.linear n hn markα') (.linear m hm markβ')
      g hga hgb (fun hh => hesc (map_mono hh)) ht p hp ha hbp hgbp hgcp
      ea eb (q.take 5) hlen5 hnb5
  rw [card_map_of_injective (G₀).subtype_injective]
  let := finite_endpoints (Reduction.reduced_triple h)
  apply Odd.of_dvd_nat ho
  apply card_dvd_of_le
  intro x hx i hi
  rw [take_getVert]
  exact hx _ (Nat.min_le_left _ _ |>.trans hlen)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
