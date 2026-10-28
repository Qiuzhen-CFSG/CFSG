module
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound
public import Theory.GroupTheory.CoprimeIndexMarking
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.AmalgamGraph.LocalAction

/-!
# Path fixers supplement the normal Sylow of an edge

In a rank-two coset graph with finite vertex groups, orbit--stabilizer
computes the index of a transitive nonbacktracking-path fixer in every edge
contained in the path. Edge transitivity gives the same order for these
edge groups. If each forward valence is a power of p and the edge has a
normal Sylow p-subgroup, coprime indices give the literal product of the
path fixer and that core. The completion and graph may be infinite.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 3.4 and 6.7, pp.74 and 123. Path transitivity is an explicit input;
no tree assumption is used.
-/

public section
open Subgroup
open scoped Pointwise
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

private theorem type_flip {v w : Vertex F} (h : (graph F).Adj v w) : w.type = !v.type := by
  have hn := h.1
  cases hv : v.type <;> cases hw : w.type <;> simp_all

private theorem forwardCount_power (p : ℕ) (degree : Bool → ℕ)
    (hd : ∀ i, ∃ k, degree i - 1 = p^k) (n : ℕ) (i : Bool) :
    ∃ k, BasedWalk.forwardCount degree n i = p^k := by
  induction n generalizing i with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    obtain ⟨k,hk⟩ := hd i
    obtain ⟨l,hl⟩ := ih (!i)
    exact ⟨k+l, by rw [BasedWalk.forwardCount,hk,hl,pow_add]⟩

private theorem core_sup_of_power_relIndex (p : ℕ) [Fact p.Prime]
    (E H : Subgroup G) [Finite E] (hHE : H ≤ E)
    (hs : ∃ T : Sylow p E, (T : Subgroup E) = pCore p E)
    (hi : ∃ n, H.relIndex E = p^n) : H ⊔ E.pCoreIn p = E := by
  obtain ⟨T,hT⟩ := hs
  obtain ⟨n,hn⟩ := hi
  have hcop : (H.subgroupOf E).index.Coprime (pCore p E).index := by
    change (H.relIndex E).Coprime (pCore p E).index
    rw [hn, ← hT]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr T.not_dvd_index |>.pow_left n
  have hgen := sup_eq_top_of_coprime_index (H.subgroupOf E) (pCore p E) hcop
  have hm := congrArg (fun K : Subgroup E => K.map E.subtype) hgen
  rw [map_sup, map_subgroupOf_eq_of_le hHE, ← MonoidHom.range_eq_map, E.range_subtype] at hm
  exact hm

/-- Every edge group is a conjugate of the same marked base edge group. -/
theorem edgeStabilizer_map_base {v w : Vertex F} (hvw : (graph F).Adj v w) :
    ∃ g : G, stabilizer F v ⊓ stabilizer F w =
      (F false ⊓ F true).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hv, hw⟩ := incident_common_translate F hvw.2
  have hb : F v.type ⊓ F w.type = F false ⊓ F true := by
    have hne := hvw.1
    cases hi : v.type <;> cases hj : w.type
    · exact (hne (hi.trans hj.symm)).elim
    · rfl
    · exact inf_comm _ _
    · exact (hne (hi.trans hj.symm)).elim
  refine ⟨g, ?_⟩
  rw [← hv, ← hw, stabilizer_translate, stabilizer_translate]
  change (MulAction.stabilizer G (Subgroup.CosetGeometry.base F v.type)).map _ ⊓
    (MulAction.stabilizer G (Subgroup.CosetGeometry.base F w.type)).map _ = _
  rw [stabilizer_base, stabilizer_base,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hb]

/-- Edge stabilizers have the same order even when the completion is infinite. -/
theorem card_edgeStabilizer {v w : Vertex F} (hvw : (graph F).Adj v w) :
    Nat.card (stabilizer F v ⊓ stabilizer F w : Subgroup G) =
      Nat.card (F false ⊓ F true : Subgroup G) := by
  obtain ⟨g, hg⟩ := edgeStabilizer_map_base F hvw
  rw [hg]
  exact card_map_of_injective (MulAut.conj g).injective

/-- A path fixer lies in every edge group whose endpoints occur in the path. -/
theorem pathStabilizer_le_edge {n : ℕ} {v a b : Vertex F}
    (p : BasedWalk (graph F) n v) (ha : a ∈ p.vertices) (hb : b ∈ p.vertices) :
    pathStabilizer F p ≤ stabilizer F a ⊓ stabilizer F b := by
  intro g hg
  exact ⟨hg a ha, hg b hb⟩

/-- Orbit--stabilizer gives the path index in any edge contained in the path. -/
theorem pathStabilizer_relIndex_edge (degree : Bool → ℕ)
    (hi : ∀ i, ((F (!i)).subgroupOf (F i)).index = degree i)
    [∀ i, Finite (F i)] {v a b : Vertex F} {n : ℕ}
    (ht : RootPathTransitive (graph F) G v (n+1))
    (p : BasedWalk (graph F) (n+1) v) (hp : p.Nonbacktracking)
    (hab : (graph F).Adj a b) (ha : a ∈ p.vertices) (hb : b ∈ p.vertices) :
    (pathStabilizer F p).relIndex (stabilizer F a ⊓ stabilizer F b) =
      BasedWalk.forwardCount degree n (!v.type) := by
  let E := stabilizer F a ⊓ stabilizer F b
  let E₀ := F false ⊓ F true
  let H := pathStabilizer F p
  have hHE : H ≤ E := pathStabilizer_le_edge F p ha hb
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F a from inf_le_left))
    (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHE) (inclusion_injective _)
  have hEi : E₀ ≤ F v.type := by
    cases v.type
    · exact inf_le_left
    · exact inf_le_right
  have hcount := card_paths_mul_card_fixer F ht p hp
  let : ∀ x : Vertex F, Finite ((graph F).neighborSet x) :=
    fun x => Theory.GroupTheory.AmalgamGraph.finite_neighbors F x
  rw [BasedWalk.card_nonbacktracking_succ (graph F) (fun x => x.type) degree
    (type_flip F) (card_neighbors_of_indices F degree hi) n v] at hcount
  have hroot : Nat.card (stabilizer F v) = Nat.card (F v.type) := by
    obtain ⟨g,hg⟩ := exists_smul_base F v
    rw [←hg, stabilizer_translate]
    change Nat.card ((MulAction.stabilizer G (Subgroup.CosetGeometry.base F v.type)).map _) = _
    rw [stabilizer_base]
    exact card_map_of_injective (MulAut.conj g).injective
  have hE : degree v.type * Nat.card E = Nat.card (stabilizer F v) := by
    rw [card_edgeStabilizer F hab, hroot]
    have hh := ((F (!v.type)).subgroupOf (F v.type)).index_mul_card
    rw [hi v.type] at hh
    have he : (F (!v.type)).subgroupOf (F v.type) = E₀.subgroupOf (F v.type) := by
      cases v.type <;> ext x <;> simp [E₀]
    rw [he, Nat.card_congr (subgroupOfEquivOfLe hEi).toEquiv] at hh
    exact hh
  have hpos : 0 < degree v.type := by
    rw [← hi v.type]
    exact Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hH : H.relIndex E * Nat.card H = Nat.card E := by
    have hh := (H.subgroupOf E).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hHE).toEquiv] at hh
    exact hh
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card H from Nat.card_pos)
  rw [hH]
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hE]
  exact (by simpa only [mul_assoc] using hcount.symm)

/-- Prime-power branching makes a path fixer supplement a normal Sylow in
any edge contained in the path. -/
theorem pathStabilizer_sup_core (prime : ℕ) [Fact prime.Prime]
    (degree : Bool → ℕ)
    (hi : ∀ i, ((F (!i)).subgroupOf (F i)).index = degree i)
    (hd : ∀ i, ∃ k, degree i - 1 = prime^k)
    [∀ i, Finite (F i)] {v a b : Vertex F} {n : ℕ}
    (ht : RootPathTransitive (graph F) G v (n+1))
    (p : BasedWalk (graph F) (n+1) v) (hp : p.Nonbacktracking)
    (hab : (graph F).Adj a b) (ha : a ∈ p.vertices) (hb : b ∈ p.vertices)
    (hs : ∃ T : Sylow prime (stabilizer F a ⊓ stabilizer F b : Subgroup G),
      (T : Subgroup (stabilizer F a ⊓ stabilizer F b : Subgroup G)) =
        pCore prime (stabilizer F a ⊓ stabilizer F b : Subgroup G)) :
    pathStabilizer F p ⊔ (stabilizer F a ⊓ stabilizer F b).pCoreIn prime =
      stabilizer F a ⊓ stabilizer F b := by
  let : Finite (stabilizer F a ⊓ stabilizer F b : Subgroup G) :=
    Finite.of_injective (inclusion (show stabilizer F a ⊓ stabilizer F b ≤
      stabilizer F a from inf_le_left)) (inclusion_injective _)
  apply core_sup_of_power_relIndex prime _ _ (pathStabilizer_le_edge F p ha hb) hs
  rw [pathStabilizer_relIndex_edge F degree hi ht p hp hab ha hb]
  exact forwardCount_power prime degree hd n (!v.type)

/-- The supplement is the literal set product, in the source order. -/
theorem pathStabilizer_mul_core (prime : ℕ) [Fact prime.Prime]
    (degree : Bool → ℕ)
    (hi : ∀ i, ((F (!i)).subgroupOf (F i)).index = degree i)
    (hd : ∀ i, ∃ k, degree i - 1 = prime^k)
    [∀ i, Finite (F i)] {v a b : Vertex F} {n : ℕ}
    (ht : RootPathTransitive (graph F) G v (n+1))
    (p : BasedWalk (graph F) (n+1) v) (hp : p.Nonbacktracking)
    (hab : (graph F).Adj a b) (ha : a ∈ p.vertices) (hb : b ∈ p.vertices)
    (hs : ∃ T : Sylow prime (stabilizer F a ⊓ stabilizer F b : Subgroup G),
      (T : Subgroup (stabilizer F a ⊓ stabilizer F b : Subgroup G)) =
        pCore prime (stabilizer F a ⊓ stabilizer F b : Subgroup G)) :
    (stabilizer F a ⊓ stabilizer F b : Set G) =
      (pathStabilizer F p : Set G) *
        ((stabilizer F a ⊓ stabilizer F b).pCoreIn prime : Set G) := by
  let E := stabilizer F a ⊓ stabilizer F b
  have hn : E ≤ normalizer (E.pCoreIn prime : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore prime E).le_normalizer_map E.subtype
  rw [← coe_mul_of_left_le_normalizer_right _ _
    ((pathStabilizer_le_edge F p ha hb).trans hn),
    pathStabilizer_sup_core F prime degree hi hd ht p hp hab ha hb hs]
  rfl
end Subgroup.CosetGeometry.RankTwo
