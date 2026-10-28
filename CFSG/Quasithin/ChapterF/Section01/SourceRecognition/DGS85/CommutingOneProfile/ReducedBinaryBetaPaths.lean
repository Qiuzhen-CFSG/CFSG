module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBinaryBetaProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedSourcePaths
public import Theory.GroupTheory.AmalgamGraph.PathSupplement
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# Source paths from intrinsic field-four/binary quotient markings

Orbit-stabilizer in the actual local quotient gives valences five and three.
Transport of the commuting critical pair makes every edge two-core have
order 64 and every nonbacktracking five-walk fixer odd. The edge core acts
freely on its 64 extensions, giving five-walk transitivity. Shorter walks
are regular, and odd longer fixers cannot act transitively on their even
sets of exits. The literal DGS convention, including the closed two-edge
return, therefore has r=4 and s=5.

These results apply to the reduced graph inside a finite original completion.
They use intrinsic local-group markings and do not require markings of the
original endpoint groups. Both path orientations, repeated vertices, the
full-Borel coset covering and the original reduced-to-ambient inclusion
are retained. The original graph need not be a tree. Field and row selection
for the complete Chapter 11 theorem remain further obligations.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
path convention p.60, regularity pp.73--74, (11.7)(c,f), pp.174--175.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.Walk
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A genuine linear local quotient gives q+1 actual neighbors. -/
theorem source_linear_neighbor_card (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k)) :
    Nat.card ((graph (family P)).neighborSet b) = Nat.card k + 1 := by
  let := finite_endpoints h
  let D := d.localGroup b
  let : Finite D := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  let q := eb.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hq : Function.Surjective q := eb.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 D := by
    rw [MonoidHom.ker_comp_of_injective _ _ eb.injective,QuotientGroup.ker_mk']
  let R := T.mapSurjective hq
  have hRT : (R : Subgroup SL(2,k)).comap q = T := by
    change ((T : Subgroup D).map q).comap q = _
    rw [Subgroup.comap_map_eq,hk,sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)]
  have hN : (normalizer (R : Set SL(2,k))).comap q = normalizer (T : Set D) := by
    change (normalizer ((R : Subgroup SL(2,k)) : Set SL(2,k))).comap q = _
    rw [comap_normalizer_eq_of_surjective _ hq,hRT]
    rfl
  have hidx : (normalizer (T : Set D)).index = Nat.card k + 1 := by
    rw [←hN,index_comap_of_surjective _ hq]
    have hqk : 1 < Nat.card k := Finite.one_lt_card
    have hi := (normalizer (R : Set SL(2,k))).card_mul_index
    have hn : Nat.card (normalizer (R : Set SL(2,k))) = Nat.card k * (Nat.card k - 1) :=
      Matrix.SpecialLinearGroup.card_sylow_normalizer_even R
    rw [hn,BenderSuzuki.External.huppert614_card_specialLinearGroup] at hi
    have hpoly : Nat.card k ^ 2 - 1 = (Nat.card k - 1) * (Nat.card k + 1) := by
      have hsub := Nat.sub_add_cancel (by omega : 1 ≤ Nat.card k)
      have hsq := Nat.sub_add_cancel (by nlinarith : 1 ≤ Nat.card k ^ 2)
      nlinarith
    rw [hpoly,←mul_assoc] at hi
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.mul_pos Nat.card_pos (by omega) : 0 < Nat.card k * (Nat.card k - 1)) hi
  have he := (source_edge_local_normalizer h d hab.symm Mb T hT).2
  have hstab : MulAction.stabilizer D a = normalizer (T : Set D) := he
  have horbit : MulAction.orbit D a = (graph (family P)).neighborSet b := by
    ext v
    constructor
    · rintro ⟨t,rfl⟩
      have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) (t : G)).map_adj_iff.mpr hab.symm
      change (graph (family P)).Adj ((t : G) • b) ((t : G) • a) at hh
      rwa [show (t : G) • b = b from d.local_le b t.property] at hh
    · intro hv
      obtain ⟨t,ht,hta⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨v,hv⟩
      exact ⟨⟨t,ht⟩,hta⟩
  rw [←horbit,Nat.card_congr (MulAction.orbitEquivQuotientStabilizer D a),
    ←index_eq_card,hstab,hidx]


variable [Finite G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => Reduction.reducedFamily L S
local notation "M" => Reduction.G₀ L S
local notation "α" => base F false
local notation "β" => base F true

private def local_quotient_conjugate (d : EarlierLocalTheorems F)
    (v : Vertex F) (g : M) :
    (d.localGroup (g • v) ⧸ pCore 2 (d.localGroup (g • v))) ≃*
      (d.localGroup v ⧸ pCore 2 (d.localGroup v)) := by
  let e := (MulEquiv.subgroupCongr (d.conjugate g v)).trans
    ((d.localGroup v).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  exact QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

/-- Transport of the intrinsic markings and commuting critical pair to
all edges in the original orientation. -/
theorem reduced_four_binary_edge_data (d : EarlierLocalTheorems F)
    (hc : IsCriticalPair F α β) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL (d.localGroup α ⧸ pCore 2 (d.localGroup α)) 2 4)
    (eb : (d.localGroup β ⧸ pCore 2 (d.localGroup β)) ≃* SL(2,ZMod 2))
    {a b : Vertex F} (hab : (graph F).Adj a b) (hat : a.type = false) :
    IsCriticalPair F a b ∧ ⁅Z F a,Z F b⁆ = ⊥ ∧
      ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 4 ∧
      Nonempty ((d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2)) := by
  have hbt : b.type = true := by
    have hn := hab.1
    rw [hat] at hn
    cases he : b.type <;> simp_all
  obtain ⟨g,hga,hgb⟩ := incident_common_translate F hab.2
  rw [hat] at hga
  rw [hbt] at hgb
  have hc' := criticalPair_translate F hc g
  rw [hga,hgb] at hc'
  have hm := commuting_centers_translate F α β g
  rw [hga,hgb,hcomm,Subgroup.map_bot] at hm
  have hma := ha.of_mulEquiv (local_quotient_conjugate d α g)
  have emb := (local_quotient_conjugate d β g).trans eb
  rw [hga] at hma
  rw [hgb] at emb
  exact ⟨hc',hm,hma,⟨emb⟩⟩

omit [Finite G] in
/-- The two actual local degrees from intrinsic reduced quotient markings. -/
theorem reduced_four_binary_neighbor_cards (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F)
    (ha : ClassicalGroup.IsPSL (d.localGroup α ⧸ pCore 2 (d.localGroup α)) 2 4)
    (eb : (d.localGroup β ⧸ pCore 2 (d.localGroup β)) ≃* SL(2,ZMod 2))
    (v : Vertex F) : Nat.card ((graph F).neighborSet v) = if v.type then 3 else 5 := by
  have hab : (graph F).Adj α β := ⟨Bool.false_ne_true,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hthree := source_binary_neighbor_card (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hab eb
  have hfive : Nat.card ((graph F).neighborSet α) = 5 := by
    obtain ⟨k,hk,hfin,hcard,⟨e⟩⟩ := ha
    let := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow
      (show Fintype.card k = 2^2 by simpa only [←Nat.card_eq_fintype_card,show (2:ℕ)^2 = 4 from rfl] using hcard)
    let f : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
      MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
    have hm : IsRankOneModel (d.localGroup α ⧸ pCore 2 (d.localGroup α)) :=
      .linear 2 (by decide) ⟨k,hk,hfin,hcard,⟨e⟩⟩
    have hh := source_linear_neighbor_card (Reduction.reduced_triple h)
      (Reduction.reduced_borel_core_sylow h) d hab.symm hm (e.trans f.symm)
    change Nat.card ((graph F).neighborSet α) = Nat.card k + 1 at hh
    rw [hcard] at hh
    exact hh
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  have he := Nat.card_congr
    ((Subgroup.CosetGeometry.translationGraphIso F g).mapNeighborSet (base F v.type))
  change Nat.card ((graph F).neighborSet (base F v.type)) =
    Nat.card ((graph F).neighborSet (g • base F v.type)) at he
  rw [hg] at he
  rw [←he]
  cases v.type
  · exact hfive
  · exact hthree

/-- Every reduced edge core has order 64, with its orientation transported
from the given intrinsic critical pair. -/
theorem reduced_four_binary_edge_core_card (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F)
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL (d.localGroup α ⧸ pCore 2 (d.localGroup α)) 2 4)
    (eb : (d.localGroup β ⧸ pCore 2 (d.localGroup β)) ≃* SL(2,ZMod 2))
    {a b : Vertex F} (hab : (graph F).Adj a b) :
    Nat.card ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) = 64 := by
  have hcase {v w : Vertex F} (hvw : (graph F).Adj v w) (hv : v.type = false) :
      Nat.card ((stabilizer F v ⊓ stabilizer F w).pCoreIn 2) = 64 := by
    obtain ⟨hc',hm,ha',⟨eb'⟩⟩ := reduced_four_binary_edge_data d hc hcomm ha eb hvw hv
    exact (reduced_linear_four_binary_profile h d hc' hb hm ha' eb').2.2.2.2.2
  by_cases hat : a.type = false
  · exact hcase hab hat
  have hbt : b.type = false := by
    have hn := hab.1
    cases he : a.type <;> cases he' : b.type <;> simp_all
  simpa only [inf_comm] using hcase hab.symm hbt

private theorem reduced_four_binary_five_walk_odd_oriented (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F)
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL (d.localGroup α ⧸ pCore 2 (d.localGroup α)) 2 4)
    (eb : (d.localGroup β ⧸ pCore 2 (d.localGroup β)) ≃* SL(2,ZMod 2))
    {a b : Vertex F} (p : (graph F).Walk a b) (hlen : p.length = 5)
    (hnb : ∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2))
    (hat : (p.getVert 2).type = false) :
    Odd (Nat.card (pathFixer (X := M) p)) := by
  let := finite_endpoints (Reduction.reduced_triple h)
  let : Finite (stabilizer F (p.getVert 0)) := inferInstance
  have hadj (i : ℕ) (hi : i < 5) := p.adj_getVert_succ (by omega : i < p.length)
  obtain ⟨hc',hm,ha',⟨eb'⟩⟩ := reduced_four_binary_edge_data d hc hcomm ha eb (hadj 2 (by decide)) hat
  have ho := reduced_linear_four_binary_five_edge_fixer_odd h d
    (hadj 0 (by decide)) (hadj 1 (by decide)) hc' hb hm
    (hadj 3 (by decide)) (hadj 4 (by decide))
    (hnb 0 (by omega)) (hnb 1 (by omega)) (hnb 2 (by omega)) (hnb 3 (by omega)) ha' eb'
  apply Odd.of_dvd_nat ho
  apply card_dvd_of_le
  intro x hx
  exact ⟨⟨⟨⟨⟨hx 0 (by omega),hx 1 (by omega)⟩,hx 2 (by omega)⟩,
    hx 3 (by omega)⟩,hx 4 (by omega)⟩,hx 5 (by omega)⟩

/-- Odd length-five fixers on the literal original reduced graph, in both
vertex orientations and with only consecutive backtracking excluded. -/
theorem reduced_four_binary_five_walk_fixer_odd (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F)
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL (d.localGroup α ⧸ pCore 2 (d.localGroup α)) 2 4)
    (eb : (d.localGroup β ⧸ pCore 2 (d.localGroup β)) ≃* SL(2,ZMod 2))
    {a b : Vertex F} (p : (graph F).Walk a b) (hlen : p.length = 5)
    (hnb : ∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2)) :
    Odd (Nat.card (pathFixer (X := M) p)) := by
  by_cases ht : (p.getVert 2).type = false
  · exact reduced_four_binary_five_walk_odd_oriented h d hc hb hcomm ha eb p hlen hnb ht
  have ht3 : (p.getVert 3).type = false := by
    have hh := (p.adj_getVert_succ (by omega : 2 < p.length)).1
    cases h2 : (p.getVert 2).type <;> cases h3 : (p.getVert 3).type <;> simp_all
  have hnb' : ∀ i, i+2 ≤ p.reverse.length →
      p.reverse.getVert i ≠ p.reverse.getVert (i+2) := by
    intro i hi
    rw [length_reverse,hlen] at hi
    simp only [getVert_reverse,hlen]
    convert (hnb (3-i) (by omega)).symm using 1 <;> congr 1 <;> omega
  have ho := reduced_four_binary_five_walk_odd_oriented h d hc hb hcomm ha eb p.reverse
    (by rwa [length_reverse]) hnb' (by simpa only [getVert_reverse,hlen] using ht3)
  rwa [pathFixer_reverse] at ho

/-- Every longer nonbacktracking walk has odd pointwise fixer. This includes
closed source paths and does not assume that the source graph is a tree. -/
theorem reduced_four_binary_long_walk_fixer_odd (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F)
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL (d.localGroup α ⧸ pCore 2 (d.localGroup α)) 2 4)
    (eb : (d.localGroup β ⧸ pCore 2 (d.localGroup β)) ≃* SL(2,ZMod 2))
    {a b : Vertex F} (p : (graph F).Walk a b) (hlen : 5 ≤ p.length)
    (hnb : ∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2)) :
    Odd (Nat.card (pathFixer (X := M) p)) := by
  have ht : (p.take 5).length = 5 := by rw [take_length,Nat.min_eq_left hlen]
  have ho := reduced_four_binary_five_walk_fixer_odd h d hc hb hcomm ha eb (p.take 5) ht (by
    intro i hi
    rw [ht] at hi
    simpa only [take_getVert, Nat.min_eq_right (show i ≤ 5 by omega),
      Nat.min_eq_right (show i+2 ≤ 5 by omega)] using hnb i (by omega))
  let := finite_endpoints (Reduction.reduced_triple h)
  apply Odd.of_dvd_nat ho
  apply card_dvd_of_le
  intro x hx i hi
  rw [take_getVert]
  exact hx _ (Nat.min_le_left _ _ |>.trans hlen)

/-- The literal five-path premise consumed by the regular apartment argument. -/
theorem reduced_four_binary_five_path_fixer_odd (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F)
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL (d.localGroup α ⧸ pCore 2 (d.localGroup α)) 2 4)
    (eb : (d.localGroup β ⧸ pCore 2 (d.localGroup β)) ≃* SL(2,ZMod 2))
    {a b : Vertex F} (p : (graph F).Walk a b) (hp : p.IsPath) (hlen : 5 ≤ p.length) :
    Odd (Nat.card (pathFixer (X := M) p)) :=
  reduced_four_binary_long_walk_fixer_odd h d hc hb hcomm ha eb p hlen (by
    intro i hi he
    have hh := hp.getVert_injOn (by omega : i ≤ p.length) hi he
    omega)


open SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open NoncommutingProfile

variable (h : HypothesisF11 L S) (d : EarlierLocalTheorems (Reduction.reducedFamily L S))
    (hc : IsCriticalPair (Reduction.reducedFamily L S)
      (base (Reduction.reducedFamily L S) false) (base (Reduction.reducedFamily L S) true))
    (hb : DGS85.b (Reduction.reducedFamily L S) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) false),
      Z (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) true)⁆ = ⊥)
    (ha : ClassicalGroup.IsPSL
      (d.localGroup (base (Reduction.reducedFamily L S) false) ⧸
        pCore 2 (d.localGroup (base (Reduction.reducedFamily L S) false))) 2 4)
    (eb : (d.localGroup (base (Reduction.reducedFamily L S) true) ⧸
      pCore 2 (d.localGroup (base (Reduction.reducedFamily L S) true))) ≃* SL(2,ZMod 2))

include h d hc hb hcomm ha eb

/-- Odd fixers in the length-indexed path representation used by covers. -/
theorem reduced_four_binary_based_fixer_odd
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a)
    (hp : p.Nonbacktracking) (hn : 5 ≤ n) : Odd (Nat.card (pathStabilizer F p)) :=
  based_fixer_odd_of_walk F
    (fun p hp hn => reduced_four_binary_long_walk_fixer_odd h d hc hb hcomm ha eb p hp hn)
    p hp hn

/-- The actual edge two-cores act transitively on five-walks from each
vertex orbit; all core-order and odd-fixer premises are discharged. -/
theorem reduced_four_binary_five_walk_transitive (a : Vertex F) :
    RootPathTransitive (graph F) M a 5 :=
  binary_graph_five_walk_transitive_of_edge_cores F (reduced_four_binary_neighbor_cards h d ha eb)
    (fun hab => reduced_four_binary_edge_core_card h d hc hb hcomm ha eb hab)
    (fun p hp => reduced_four_binary_based_fixer_odd h d hc hb hcomm ha eb p hp le_rfl) a

/-- Exact regularity of all nonbacktracking walks from intrinsic markings. -/
theorem reduced_four_binary_regular_iff
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a) (hp : p.Nonbacktracking) :
    Regular (A := M) p ↔ n ≤ 4 :=
  binary_graph_regular_iff_of_five_transitive F (reduced_four_binary_neighbor_cards h d ha eb)
    (reduced_four_binary_five_walk_transitive h d hc hb hcomm ha eb)
    (fun p hp hn => reduced_four_binary_based_fixer_odd h d hc hb hcomm ha eb p hp hn) p hp

/-- The literal Chapter 14 path premises on every marked coset cover.
The map and both endpoint stabilizers are the supplied covering data. -/
theorem reduced_four_binary_cover_path_profile
    {X : Type*} [Group X] (F₁ : Bool → Subgroup X) (f : X →* M)
    (c : CoverData F₁ F f) :
    BasedPathTransitive (X := X) (graph F₁) 5 ∧
      ∀ {a b} (p : (graph F₁).Walk a b), p.IsPath → p.length = 5 →
        Odd (Nat.card (pathFixer (X := X) p)) :=
  binary_graph_cover_path_profile F (reduced_four_binary_five_walk_transitive h d hc hb hcomm ha eb)
    (fun p hp => reduced_four_binary_based_fixer_odd h d hc hb hcomm ha eb p hp le_rfl) F₁ f c

/-- The exact source extrema r=4 and s=5, including the permitted closed
source paths, with odd stabilizers at every length at least five. -/
theorem reduced_four_binary_source_path_parameters :
    HasSourcePathParameters (P := fun i => (Reduction.P₀ L S i).subgroupOf M) 4 5 ∧
      ∀ {a b : Vertex F} (p : (graph F).Walk a b), IsSourcePath p → 5 ≤ p.length →
        Odd (Nat.card (pathFixer (X := M) p)) :=
  BinarySourceGeometry.source_path_parameters
    (fun i => (Reduction.P₀ L S i).subgroupOf M)
    (reduced_four_binary_neighbor_cards h d ha eb)
    (fun p hp => reduced_four_binary_regular_iff h d hc hb hcomm ha eb p hp)
    (fun p hl hn => reduced_four_binary_long_walk_fixer_odd h d hc hb hcomm ha eb p hl hn)

omit ha eb in
/-- The source path parameters and odd fixers after the literal inclusion
into the original completion. Both quotient markings are on their original images. -/
theorem original_reduced_four_binary_path_profile
    (ha : ClassicalGroup.IsPSL ((d.localGroup α).map (M).subtype ⧸
      pCore 2 ((d.localGroup α).map (M).subtype)) 2 4)
    (eb : ((d.localGroup β).map (M).subtype ⧸
      pCore 2 ((d.localGroup β).map (M).subtype)) ≃* SL(2,ZMod 2)) :
    HasSourcePathParameters (P := fun i => (Reduction.P₀ L S i).subgroupOf M) 4 5 ∧
      ∀ {a b : Vertex F} (p : (graph F).Walk a b), IsSourcePath p → 5 ≤ p.length →
        Odd (Nat.card ((pathFixer (X := M) p).map (M).subtype)) := by
  let ea := (d.localGroup α).equivMapOfInjective (M).subtype (M).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb₀ := (d.localGroup β).equivMapOfInjective (M).subtype (M).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb₀ (pCore_map_iso 2 eb₀)
  obtain ⟨hr,ho⟩ := reduced_four_binary_source_path_parameters h d hc hb hcomm
    (ha.of_mulEquiv eqa) (eqb.trans eb)
  refine ⟨hr,?_⟩
  intro a b p hp hl
  rw [card_map_of_injective (M).subtype_injective]
  exact ho p hp hl

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
