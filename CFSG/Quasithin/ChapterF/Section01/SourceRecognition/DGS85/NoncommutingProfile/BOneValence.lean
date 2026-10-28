module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOnePathCores
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Valence and short-path extension in the noncommuting b=1 graph

The actual local actor is transitive on neighbors, and the stabilizer of its
marked neighbor is exactly the preimage of the marked SL₂ Sylow normalizer.
Its index is q+1, giving q forward exits at every nonempty path in both
vertex orbits. Bipartiteness then supplies a new exit at lengths at most
four: only one already visited vertex can remain among the q exits.

These are the neighbor counts used by the path-regularity argument in
DGS, *Groups and Graphs* (1985), (10.5)(c,d), p.156, with the definitions
on pp.73--74. No tree or finite-completion assumption is introduced.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem sl2_sylow_normalizer_index (T : Sylow 2 SL(2,k)) :
    (normalizer (T : Set SL(2,k))).index = Nat.card k + 1 := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have hc := (normalizer (T : Set SL(2,k))).card_mul_index
  change Nat.card (normalizer (T : Set SL(2,k))) * (normalizer (T : Set SL(2,k))).index = Nat.card SL(2,k) at hc
  have hN : Nat.card (normalizer (T : Set SL(2,k))) = Nat.card k * (Nat.card k - 1) :=
    Matrix.SpecialLinearGroup.card_sylow_normalizer_even T
  rw [hN,
    BenderSuzuki.External.huppert614_card_specialLinearGroup] at hc
  have hpoly : Nat.card k ^ 2 - 1 = (Nat.card k - 1) * (Nat.card k + 1) := by
    have hsub : Nat.card k - 1 + 1 = Nat.card k := Nat.sub_add_cancel (by omega)
    have hsq : Nat.card k ^ 2 - 1 + 1 = Nat.card k ^ 2 := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  rw [hpoly,←mul_assoc] at hc
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos Nat.card_pos (by omega) : 0 < Nat.card k * (Nat.card k - 1)) hc

/-- The marked natural quotient computes the actual graph valence. -/
theorem base_neighbor_card_of_action (h : LocallyRankOneTriple P B) (i : Bool)
    (c : BOneActionData (family P) (base (family P) i) (base (family P) (!i)) k W)
    (hn : B ≤ normalizer (c.actor : Set G))
    (hcore : Q (family P) (base (family P) (!i)) = Z (family P) (base (family P) (!i))) :
    Nat.card ((graph (family P)).neighborSet (base (family P) i)) = Nat.card k + 1 := by
  let v := base (family P) i
  let w := base (family P) (!i)
  have he : MulAction.orbit c.actor w = (graph (family P)).neighborSet v := by
    ext u
    constructor
    · rintro ⟨g,rfl⟩
      have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) (g : G)).map_adj_iff.mpr c.adjacent
      change (graph (family P)).Adj ((g : G) • base (family P) i) ((g : G) • base (family P) (!i)) at hh
      rw [c.actor_le g.property] at hh
      exact hh
    · intro hu
      obtain ⟨g,hg⟩ := base_actor_neighbor_transitive h i c hn u hu
      exact ⟨g,hg⟩
  have hs : MulAction.stabilizer c.actor w =
      (normalizer (c.imageSylow : Set SL(2,k))).comap c.quotient := by
    ext g
    exact (base_actor_fixes_neighbor_iff h i c hn hcore g).symm
  rw [←he]
  change (MulAction.orbit c.actor w).ncard = _
  rw [←MulAction.index_stabilizer,hs,
    index_comap_of_surjective _ c.onto]
  exact sl2_sylow_normalizer_index c.imageSylow

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
    (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))

local instance bOneValenceAlgebra1 {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

include h c₀ c₁ hn₀ hn₁

/-- Equal fields give the same valence at every vertex in both source orbits. -/
theorem neighbor_card_of_actions (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    (v : Vertex (family P)) :
    Nat.card ((graph (family P)).neighborSet v) = Nat.card k₀ + 1 := by
  obtain ⟨hQ₀,hQ₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  have he := Nat.card_congr
    ((Subgroup.CosetGeometry.translationGraphIso (family P) g).mapNeighborSet (base (family P) v.type))
  change Nat.card ((graph (family P)).neighborSet (base (family P) v.type)) =
    Nat.card ((graph (family P)).neighborSet (g • base (family P) v.type)) at he
  rw [hg] at he
  rw [←he]
  cases v.type
  · exact base_neighbor_card_of_action h false c₀ hn₀ hQ₁
  · rw [base_neighbor_card_of_action h true c₁ hn₁ hQ₀,paired_field_orders_eq h c₀ c₁ E₀]

/-- Actual forward neighbors excluding the preceding vertex. -/
def pathExits {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) : Set (Vertex (family P)) :=
  (graph (family P)).neighborSet b \ {p.penultimate}

/-- The natural quotient gives exactly q exits from every nonempty path. -/
theorem pathExits_card (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b) (hp : ¬p.Nil) :
    Nat.card (pathExits p) = Nat.card k₀ := by
  rw [Nat.card_coe_set_eq,pathExits,Set.ncard_sdiff_singleton_of_mem
    (show p.penultimate ∈ (graph (family P)).neighborSet b from (p.adj_penultimate hp).symm)]
  rw [←Nat.card_coe_set_eq,neighbor_card_of_actions h c₀ c₁ hn₀ hn₁ E₀]
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.Walk
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
    (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))
local instance bOneValenceAlgebra2 {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

private theorem type_eq_two_steps {u v w : Vertex (family P)}
    (huv : (graph (family P)).Adj u v) (hvw : (graph (family P)).Adj v w) : u.type = w.type := by
  have h₁ := huv.1
  have h₂ := hvw.1
  cases hu : u.type <;> cases hv : v.type <;> cases hw : w.type <;> simp_all

include h c₀ c₁ hn₀ hn₁ in
/-- Bipartiteness and valence at least three extend every path of length at most four.
This is proved on the source graph; no tree assumption is needed. -/
theorem short_path_has_new_exit
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    {a b : Vertex (family P)} (p : (graph (family P)).Walk a b)
    (hpos : 0 < p.length) (hlen : p.length ≤ 4) :
    ∃ z ∈ pathExits p, z ∉ p.support := by
  have hc := pathExits_card h c₀ c₁ hn₀ hn₁ E₀ p (not_nil_iff_lt_length.mpr hpos)
  have hgt : 1 < (pathExits p).ncard := by
    rw [←Nat.card_coe_set_eq,hc]
    exact Finite.one_lt_card
  obtain ⟨z,hz,hzn⟩ := Set.exists_ne_of_one_lt_ncard hgt (p.getVert (p.length-3))
  refine ⟨z,hz,?_⟩
  change (graph (family P)).Adj b z ∧ z ≠ p.penultimate at hz
  intro hm
  obtain ⟨j,rfl,hj⟩ := mem_support_iff_exists_getVert.mp hm
  have hbad (he : b.type = (p.getVert j).type) : False := hz.1.1 he
  have htwo (k : ℕ) (hk : k+1 < p.length) : (p.getVert k).type = (p.getVert (k+2)).type :=
    type_eq_two_steps (p.adj_getVert_succ (by omega)) (p.adj_getVert_succ hk)
  have hlast : p.getVert p.length = b := p.getVert_length
  have hprev : p.getVert (p.length-1) ≠ p.getVert j := hz.2.symm
  have hskip : p.getVert (p.length-3) ≠ p.getVert j := hzn.symm
  have hl : p.length = 1 ∨ p.length = 2 ∨ p.length = 3 ∨ p.length = 4 := by omega
  rcases hl with hl | hl | hl | hl
  · have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · exact hprev (by rw [hl])
    · exact hbad (by rw [hl] at hlast; rw [hlast])
  · have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · exact hbad (by have hh := htwo 0 (by omega); rw [hl] at hlast; simpa only [hlast] using hh.symm)
    · exact hprev (by rw [hl])
    · exact hbad (by rw [hl] at hlast; rw [hlast])
  · have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl | rfl | rfl
    · exact hskip (by rw [hl])
    · exact hbad (by have hh := htwo 1 (by omega); rw [hl] at hlast; simpa only [hlast] using hh.symm)
    · exact hprev (by rw [hl])
    · exact hbad (by rw [hl] at hlast; rw [hlast])
  · have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hj' with rfl | rfl | rfl | rfl | rfl
    · exact hbad (by
        have hh := (htwo 0 (by omega)).trans (htwo 2 (by omega))
        rw [hl] at hlast
        simpa only [hlast] using hh.symm)
    · exact hskip (by rw [hl])
    · exact hbad (by have hh := htwo 2 (by omega); rw [hl] at hlast; simpa only [hlast] using hh.symm)
    · exact hprev (by rw [hl])
    · exact hbad (by rw [hl] at hlast; rw [hlast])

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
