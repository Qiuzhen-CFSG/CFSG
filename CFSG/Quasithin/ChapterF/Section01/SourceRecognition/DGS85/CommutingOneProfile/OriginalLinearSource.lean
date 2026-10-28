module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.EscapingFourWalk
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourcePathParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.UnconditionalLinearPaths

/-!
# The original linear Chapter 11 branch without auxiliary source inputs

Both original linear quotient markings determine the actual graph actors
through the original starred inclusions. The full-catalogue 6.5 theorem
constructs the earlier-local record, and source 6.8 supplies four-walk
transitivity. The escaping four-walk is then constructed, discharging all
path, transporter, catalogue and earlier-local inputs in the linear
application of (11.7)(f).

The same original field markings give q_alpha=q_beta^2, Q_alpha=Z_alpha,
the corrected beta seed span, the beta-core center and the orders of both
cores and the whole original
Borel two-core. The path conclusion is applied to the actual universal
tree for Chapter 14. Neither an abstract normal-series type nor these
orders identify the marked amalgam. The original nonlinear branches,
compatible Cartans, exchange and final marked recognition remain separate.
Source: DGS, Groups and Graphs (1985), (6.8), pp.123--124,
(11.6)--(11.7), pp.172--175, and (14.1), p.210.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀
local notation "A" => reducedAmalgam L₀ S₀

variable (h : HypothesisF11 L₀ S₀)
    (K : Bool → Type) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L₀ i ⧸ pCore 2 (family L₀ i)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K i))

include h K e

private theorem original_linear_actor_model (i : Bool) :
    IsRankOneModel (graphLocalGroup F₀ (base F₀ i) ⧸
      pCore 2 (graphLocalGroup F₀ (base F₀ i))) := by
  have hm : IsRankOneModel (family L₀ i ⧸ pCore 2 (family L₀ i)) := by
    cases i
    · exact h.quotient 0
    · exact h.quotient 1
  exact hm.of_equiv ((reduced_graphLinearQuotient h i (e i)).trans (e i).symm)

private theorem original_linear_mapped_actor_model (i : Bool) :
    IsRankOneModel ((graphLocalGroup F₀ (base F₀ i)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ (base F₀ i)).map (G₀).subtype)) := by
  let a := (graphLocalGroup F₀ (base F₀ i)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  exact (original_linear_actor_model h K e i).of_equiv
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm

private theorem original_linear_four_transitive :
    ∀ v : Vertex F₀, RootPathTransitive (graph F₀) G₀ v 4 := by
  obtain ⟨n,hn,_,ht,_⟩ := reduced_exists_linear_long_path_unconditional h K e
  exact fun v => ht v 4 hn

private theorem original_linear_mapped_mark (i : Bool) {n : ℕ}
    (hcard : Nat.card (K i) = 2^n) :
    ClassicalGroup.IsPSL ((graphLocalGroup F₀ (base F₀ i)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ (base F₀ i)).map (G₀).subtype)) 2 (2^n) := by
  let a := (graphLocalGroup F₀ (base F₀ i)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let qa := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  exact ⟨K i,inferInstance,inferInstance,hcard,
    ⟨qa.symm.trans (reduced_graphLinearQuotient h i (e i))⟩⟩

omit h e in
private theorem original_field_degrees :
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ Nat.card (K false) = 2^n ∧ Nat.card (K true) = 2^m := by
  let : Fintype (K false) := Fintype.ofFinite _
  let : Fintype (K true) := Fintype.ofFinite _
  obtain ⟨n,_,hn⟩ := FiniteField.card (K false) 2
  obtain ⟨m,_,hm⟩ := FiniteField.card (K true) 2
  exact ⟨n,m,n.property,m.property,by simpa only [Nat.card_eq_fintype_card] using hn,
    by simpa only [Nat.card_eq_fintype_card] using hm⟩

variable (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false) (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1) (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false),Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)

include hc hb hcomm

/-- The escaping source walk is constructed from the original linear
endpoint markings, with no enlarged catalogue or path premise. -/
theorem original_linear_escaping_four_walk :
    ∃ c, (graph F₀).Adj (base F₀ true) c ∧ (base F₀ false) ≠ c ∧
      ∃ g ∈ stabilizer F₀ (base F₀ false), g • (base F₀ true) ≠ (base F₀ true) ∧
        ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤
          (Q F₀ (g • (base F₀ true))).map (G₀).subtype ∧
        ∃ p : BasedWalk (graph F₀) 4 (g • c), p.Nonbacktracking ∧
          p.vertices = [g • c,g • (base F₀ true),base F₀ false,base F₀ true,c] := by
  let d := reducedFullEarlierLocalTheorems h
  have ma : IsRankOneModel (d.localGroup (base F₀ false) ⧸ pCore 2 (d.localGroup (base F₀ false))) := by
    change IsRankOneModel (graphLocalGroup F₀ (base F₀ false) ⧸ pCore 2 (graphLocalGroup F₀ (base F₀ false)))
    exact original_linear_actor_model h K e false
  have mb : IsRankOneModel (d.localGroup (base F₀ true) ⧸ pCore 2 (d.localGroup (base F₀ true))) := by
    change IsRankOneModel (graphLocalGroup F₀ (base F₀ true) ⧸ pCore 2 (graphLocalGroup F₀ (base F₀ true)))
    exact original_linear_actor_model h K e true
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ := source_exists_escaping_four_walk
    (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) (B := (B₀ L₀ S₀).subgroupOf G₀)
    (a := base F₀ false) (b := base F₀ true)
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    d hc hb hcomm ma mb
    (original_linear_four_transitive h K e)
  exact ⟨c,hbc,hac,g,hga,hgb,
    fun hh => hesc ((map_le_map_iff_of_injective (G₀).subtype_injective).mp hh),p,hp,hpv⟩

/-- Source (11.7)(f) in the original linear branch. All earlier-local,
catalogue, escaping-path and initial-transitivity premises are discharged. -/
theorem original_borel_linear_source_path_profile :
    HasSourcePathParameters (P := fun i => (Reduction.P₀ L₀ S₀ i).subgroupOf G₀) 4 5 ∧
      (∀ x : Vertex F₀, RootPathTransitive (graph F₀) G₀ x 5) ∧
      ∀ {x y : Vertex F₀} (q : (graph F₀).Walk x y), IsSourcePath q → 5 ≤ q.length →
        Odd (Nat.card ((pathFixer (X := G₀) q).map (G₀).subtype)) := by
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ :=
    original_linear_escaping_four_walk h K e hc hb hcomm
  exact original_borel_commuting_source_path_profile_from_local_catalogue h hc hb hcomm
    hbc hac g hga hgb hesc (original_linear_four_transitive h K e (g • c)) p hp
    (by rw [hpv]; simp) (by rw [hpv]; simp) (by rw [hpv]; simp)
    (by rw [hpv]; simp) (by rw [hpv]; simp)
    (original_linear_mapped_actor_model h K e false)
    (original_linear_mapped_actor_model h K e true)

/-- The actual Chapter 14 path inputs on the original full-Borel universal
tree, with every Chapter 11 path and local-catalogue premise discharged. -/
theorem original_linear_tree_path_profile :
    BasedPathTransitive (X := (A).Universal) (sourceGraph A) 5 ∧
      ∀ {x y} (q : (sourceGraph A).Walk x y), q.IsPath → q.length = 5 →
        Odd (Nat.card (pathFixer (X := (A).Universal) q)) := by
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ :=
    original_linear_escaping_four_walk h K e hc hb hcomm
  exact commuting_tree_path_profile_from_local_catalogue h hc hb hcomm
    hbc hac g hga hgb hesc (original_linear_four_transitive h K e (g • c)) p hp
    (by rw [hpv]; simp) (by rw [hpv]; simp) (by rw [hpv]; simp)
    (by rw [hpv]; simp) (by rw [hpv]; simp)
    (original_linear_mapped_actor_model h K e false)
    (original_linear_mapped_actor_model h K e true)

/-- The field ratio and complete elementary core orders in the original
linear markings, including the two-core of the whole original Borel. -/
theorem original_borel_linear_core_profile :
    Nat.card (K false) = Nat.card (K true)^2 ∧
      (Q F₀ (base F₀ false)).map (G₀).subtype = (Z F₀ (base F₀ false)).map (G₀).subtype ∧
      centerIn ((Q F₀ (base F₀ true)).map (G₀).subtype) = (Z F₀ (base F₀ true)).map (G₀).subtype ∧
      Nat.card ((Z F₀ (base F₀ true)).map (G₀).subtype) = Nat.card (K true) ∧
      Nat.card ((Q F₀ (base F₀ false)).map (G₀).subtype) = Nat.card (K false)^2 ∧
      Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) = Nat.card (K false)^2 * Nat.card (K true) ∧
      Nat.card (twoCore (commonBorel L₀ S₀)) = Nat.card (K false)^2 * Nat.card (K true)^2 := by
  obtain ⟨n,m,hn,hm,hna,hmb⟩ := original_field_degrees K
  have ma := original_linear_mapped_mark h K e false hna
  have mb := original_linear_mapped_mark h K e true hmb
  obtain ⟨hnm,hQa,hZb,hca,hcb,_⟩ := original_reduced_linear_linear_profile h
    (reducedFullEarlierLocalTheorems h) hc hb hcomm n m hn hm ma mb
  have hS := (original_linear_linear_borel_core_order h (reducedFullEarlierLocalTheorems h)
    hc hb hcomm n m hn hm ma mb).2
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ :=
    original_linear_escaping_four_walk h K e hc hb hcomm
  have hcenter := (original_reduced_linear_linear_centers h (reducedFullEarlierLocalTheorems h)
    hc hb hcomm hbc hac n m hn hm ma mb).1
  refine ⟨?_,hQa,hcenter,?_,?_,?_,?_⟩
  · rw [hna,hmb,hnm,←pow_mul,Nat.mul_comm m 2]
  · exact hZb.trans hmb.symm
  · simpa only [hna] using hca
  · simpa only [hna,hmb] using hcb
  · simpa only [hna,hmb] using hS

/-- The original field degree also controls both actual graph valences;
its alpha/beta orientation is fixed by the given critical edge. -/
theorem original_linear_field_and_valences :
    ∃ m : ℕ, 0 < m ∧ Nat.card (K false) = 2^(2*m) ∧ Nat.card (K true) = 2^m ∧
      ∀ x : Vertex F₀, Nat.card ((graph F₀).neighborSet x) = 2^(if x.type then m else 2*m)+1 := by
  obtain ⟨n,m,hn,hm,hna,hmb⟩ := original_field_degrees K
  have ma := original_linear_mapped_mark h K e false hna
  have mb := original_linear_mapped_mark h K e true hmb
  have hnm := (original_linear_linear_borel_core_order h (reducedFullEarlierLocalTheorems h)
    hc hb hcomm n m hn hm ma mb).1
  subst n
  exact ⟨m,hm,hna,hmb,original_reduced_linear_neighbor_cards h
    (reducedFullEarlierLocalTheorems h) hn hm ma mb⟩

/-- The corrected Chapter 11 seed span is the whole original beta core.
The seed is Z_alpha intersect Q_beta, and conjugation uses the full beta
stabilizer with its literal reduced-to-original inclusion. -/
theorem original_linear_beta_seed_span :
    betaSpan ((stabilizer F₀ (base F₀ true)).map (G₀).subtype)
      ((Z F₀ (base F₀ false)).map (G₀).subtype) =
        (Q F₀ (base F₀ true)).map (G₀).subtype := by
  obtain ⟨n,m,hn,hm,hna,hmb⟩ := original_field_degrees K
  let d := reducedFullEarlierLocalTheorems h
  have ma : ClassicalGroup.IsPSL (d.localGroup (base F₀ false) ⧸
      pCore 2 (d.localGroup (base F₀ false))) 2 (2^n) :=
    ⟨K false,inferInstance,inferInstance,hna,⟨reduced_graphLinearQuotient h false (e false)⟩⟩
  have mb : ClassicalGroup.IsPSL (d.localGroup (base F₀ true) ⧸
      pCore 2 (d.localGroup (base F₀ true))) 2 (2^m) :=
    ⟨K true,inferInstance,inferInstance,hmb,⟨reduced_graphLinearQuotient h true (e true)⟩⟩
  have hspan := (reduced_linear_linear_profile h d hc hb hcomm n m hn hm ma mb).2.2.1
  have he := congrArg (map (G₀).subtype) hspan
  dsimp only [betaSpan] at he ⊢
  rw [map_conjugateSpanBy,map_inf _ _ _ (G₀).subtype_injective] at he
  rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀).subtype_injective]
  exact he

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
