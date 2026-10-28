module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictPathSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoPathCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.NonbinaryCartanCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.NonbinaryCartanReflection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan

/-!
# The strict distance-two Cartan centralizer for tree reflections

The actual nonsolvable left endpoint makes its field nonbinary. The
strict core-layer theorem supplies a nonbinary right field as well.
Transport those exact quotient markings to every vertex, propagate the
full-Cartan core centralizer along a seven-path, and use its odd fixer.
No chosen tree reflection or quotient involution is assumed in this step.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(10.10), printed p.164, and the Cartan lift in (14.2), pp.210--211.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true

/-- The strict original source supplies nonbinary fields for both local
types, with quotient markings at every vertex. -/
theorem original_bTwo_strict_nonbinary_markings
    (h : HypothesisF11 L S) {u : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n)) :
    ∃ (K : Bool → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Finite (K i))
      (_ : ∀ i, CharP (K i) 2), (∀ i, 4 ≤ Nat.card (K i)) ∧
      ∀ v : Vertex F, Nonempty
        ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type)) := by
  let H := reduced_triple h
  let _ := finite_endpoints H
  have hval (x : Vertex F) : 3 ≤ Nat.card ((graph F).neighborSet x) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) x.type
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet α)
    (by rw [←Nat.card_coe_set_eq]; have := hval α; omega) β
  obtain ⟨k,f,fin,ch,alg,c,hactor,hk,m,hm,hright,_⟩ :=
    original_core_layers h hc hne hb hβu ht htne hns
  obtain ⟨k₀,f₀,fin₀,h₀,⟨e₀⟩⟩ := hlinear
  obtain ⟨k₁,f₁,fin₁,h₁,⟨e₁⟩⟩ := hright
  let _ := f₀
  let _ := fin₀
  let _ := f₁
  let _ := fin₁
  let _ : Fintype k₀ := Fintype.ofFinite k₀
  let _ : Fintype k₁ := Fintype.ofFinite k₁
  let _ : CharP k₀ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₀)
  let _ : CharP k₁ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₁)
  let K : Bool → Type := fun i => if i then k₁ else k₀
  let _ : ∀ i, Field (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, Finite (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, CharP (K i) 2 := fun i => by cases i <;> assumption
  let eOrig : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i) := by
    intro i
    cases i
    · exact e₀
    · exact e₁
  let eSL (i : Bool) : SL(2,K i) ≃* PSL(2,K i) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K i))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let eBase (i : Bool) := (reduced_graphLinearQuotient h i (eOrig i)).trans (eSL i).symm
  have hcore : c.actor.pCoreIn 2 = Q F α := by
    rw [hactor]
    exact CommutingTrivial.graphLocalGroup_core H α
  have hker : c.quotient.ker = pCore 2 c.actor := by
    rw [c.kernel]
    change (Q F α).subgroupOf c.actor = pCore 2 c.actor
    rw [←hcore]
    exact comap_map_eq_self_of_injective c.actor.subtype_injective _
  let eA := MulEquiv.subgroupCongr hactor
  let eQ := QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)
  let eFields := (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (eQ.trans (eBase false)))
  have hcard : Nat.card k = Nat.card k₀ := Matrix.SL2.field_card_eq_of_equiv eFields
  have hK (i : Bool) : 4 ≤ Nat.card (K i) := by
    cases i
    · change 4 ≤ Nat.card k₀
      have hk₀ : 2 < Nat.card k₀ := hcard ▸ hk
      have hn : 2 ≤ n := by
        rw [h₀] at hk₀
        by_contra hn
        have hn' : n = 0 ∨ n = 1 := by omega
        rcases hn' with rfl | rfl <;> norm_num at hk₀
      rw [h₀]
      exact (show 2^2 ≤ 2^n from Nat.pow_le_pow_right (by decide) hn)
    · change 4 ≤ Nat.card k₁
      rw [h₁]
      exact (show 2^2 ≤ 2^m from Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨K,inferInstance,inferInstance,inferInstance,hK,
    fun v => ⟨source_linear_quotient_at H K eBase v⟩⟩

/-- Every full edge Cartan in the original strict branch has trivial
centralizer in either incident vertex core. The actual left marking,
strict hypotheses and both original vertex types are retained. -/
theorem original_bTwo_strict_cartan_core_centralizer
    (h : HypothesisF11 L S) {u : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
    {v w : Vertex F} (hvw : (graph F).Adj v w)
    (C : Subgroup (G₀ L S)) [IsMulCommutative C]
    (hCE : C ≤ stabilizer F v ⊓ stabilizer F w)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer F v ⊓ stabilizer F w).pCoreIn 2))
    (hg : C ⊔ (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 =
      stabilizer F v ⊓ stabilizer F w) :
    Q F v ⊓ centralizer (C : Set (G₀ L S)) = ⊥ := by
  let H := reduced_triple h
  obtain ⟨K,fK,finK,chK,hK,e⟩ :=
    original_bTwo_strict_nonbinary_markings h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨hpar,hodd⟩ := original_bTwo_strict_path_parameters_of_linear_left
    h hc hne hb hβu hns hlinear
  have hval (x : Vertex F) : 3 ≤ Nat.card ((graph F).neighborSet x) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) x.type
  have hs : sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) = 7 :=
    (sourceS_spec H (reduced_vertex_sylow h)).2.unique hpar.2
  have htwo (x : Vertex F) : RootPathTransitive (graph F) (G₀ L S) x 2 :=
    sourceS_transitive H (reduced_vertex_sylow h) x (by omega)
  apply ApartmentExchange.full_cartan_core_centralizer_eq_bot H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) htwo K
    (fun v => Classical.choice (e v)) hK hvw C hCE ho hd hg 6
  intro p hp
  have hsimple : p.toWalk.IsPath := Theory.GroupAction.CubicTree.isPath_of_short_rightRegular
    hval 7 (fun m hm x q hq =>
      (sourceS_short_regular H (reduced_vertex_sylow h) q (by omega) hq).2) p le_rfl hp
  have he : pathFixer (X := G₀ L S) p.toWalk = pathStabilizer F p := by
    ext x
    rw [mem_pathFixer_support,support_toWalk]
    rfl
  rw [←he]
  exact hodd p.toWalk (Or.inl hsimple)
    (show 7 ≤ p.toWalk.length from by rw [length_toWalk])

/-- Construct the original local involution for any full Cartan of a
strict source edge, retaining its full-Cartan normalizer and endpoint action. -/
theorem original_bTwo_strict_cartan_reflection
    (h : HypothesisF11 L S) {u : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
    {v w : Vertex F} (hvw : (graph F).Adj v w)
    (C : Subgroup (G₀ L S)) [IsMulCommutative C]
    (hCE : C ≤ stabilizer F v ⊓ stabilizer F w)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer F v ⊓ stabilizer F w).pCoreIn 2))
    (hg : C ⊔ (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 =
      stabilizer F v ⊓ stabilizer F w) :
    ∃ g ∈ graphLocalGroup F v,
      g ∈ normalizer (C : Set (G₀ L S)) ∧ g*g=1 ∧ g • v=v ∧ g • w≠w := by
  obtain ⟨K,fK,finK,chK,hK,e⟩ :=
    original_bTwo_strict_nonbinary_markings h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  have hs := noncommuting_source_length_ge_four h hc hne
  exact ApartmentExchange.exists_full_cartan_reflection (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw
    (sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h) w (by omega))
    (Classical.choice (e v)) (by have := hK v.type; omega) C hCE ho hd hg
    (original_bTwo_strict_cartan_core_centralizer h hc hne hb hβu hns hlinear hvw C hCE ho hd hg)

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile OriginalExtension SuzukiContainment
open Theory.GroupTheory RankTwoAmalgam
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily (reducedAmalgam L S)

private theorem strict_middle_eq_overlap : originalMiddle A = T false ⊓ T true := by
  exact (Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).symm

private theorem strict_middle_le_endpoint (i : Bool) : originalMiddle A ≤ T i := by
  rw [strict_middle_eq_overlap]
  cases i
  · exact inf_le_left
  · exact inf_le_right

/-- Each original universal endpoint contains the required involution,
normalizing the same prescribed full Cartan. -/
theorem original_bTwo_strict_tree_reflection
    (h : HypothesisF11 L S) {u : Vertex F}
    (hc : IsCriticalPair F (base F false) u) (hne : ⁅Z F (base F false),Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj (base F true) u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
    (c : CompatibleCartans L (reducedSylow L S)) (i : Bool) :
    ∃ t : (reducedAmalgam L S).Universal, t • base T i = base T i ∧
      t • base T (!i) ≠ base T (!i) ∧ t*t=1 ∧
      t ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal) := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let U := (twoGroup L S).map φ
  let E := F false ⊓ F true
  let : Finite (F false) := (finite_endpoints (reduced_triple h)) false
  let : Finite (F true) := (finite_endpoints (reduced_triple h)) true
  let _ : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let _ : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  let _ := cartan_abelian h c
  let _ : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hmapE : (originalMiddle A).map φ = E := by
    rw [strict_middle_eq_overlap]
    exact cov.map_inf
  have hCE : C ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hUE : U ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hUnorm : E ≤ normalizer (U : Set (G₀ L S)) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hUcore : U ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hUE hUnorm
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  have hd : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨m,hm⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hm]; exact ho.coprime_two_right.pow_right m)
  have hg : C ⊔ E.pCoreIn 2 = E := by
    apply le_antisymm (sup_le hCE (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    calc
      E = U ⊔ C := he.symm
      _ ≤ C ⊔ E.pCoreIn 2 :=
        sup_le (hUcore.trans le_sup_right) le_sup_left
  have hEi : E = stabilizer F (base F i) ⊓ stabilizer F (base F (!i)) := by
    have hi : stabilizer F (base F i) = F i :=
      Subgroup.CosetGeometry.stabilizer_base F i
    have hni : stabilizer F (base F (!i)) = F (!i) :=
      Subgroup.CosetGeometry.stabilizer_base F (!i)
    rw [hi, hni]
    cases i
    · rfl
    · exact inf_comm _ _
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨g,_,hgC,hgsq,hgfix,hgmove⟩ := original_bTwo_strict_cartan_reflection
    h hc hne hb hβu hns hlinear hadj C (hEi ▸ hCE) ho (hEi ▸ hd) (hEi ▸ hg)
  have hgFi : g ∈ F i := by
    rw [←Subgroup.CosetGeometry.stabilizer_base F i]
    exact hgfix
  have hgimage : g ∈ (T i).map φ := (cov.map_eq i).symm ▸ hgFi
  obtain ⟨t,ht,htg⟩ := hgimage
  have hfix : t • base T i = base T i := by
    have hh := ht
    rw [←Subgroup.CosetGeometry.stabilizer_base T i] at hh
    exact hh
  have hmove : t • base T (!i) ≠ base T (!i) := by
    intro he
    have hh := congrArg cov.vertex he
    apply hgmove
    have hh' : φ t • base F (!i) = base F (!i) := by
      simpa only [cov.vertex_smul, cov.vertex_base] using hh
    rw [← htg]
    exact hh'
  have hsq : t*t=1 := by
    have he : φ (t*t) = φ 1 := by rw [map_mul,htg,hgsq,map_one]
    exact congrArg Subtype.val (cov.injective i
      (a₁ := ⟨t*t,(T i).mul_mem ht ht⟩) (a₂ := 1) he)
  have hKi : cartan c ≤ T i := (cartan_le c).trans (strict_middle_le_endpoint i)
  let Ki := (cartan c).subgroupOf (T i)
  let f : T i →* G₀ L S := φ.comp (T i).subtype
  have hf : Function.Injective f := cov.injective i
  have hKmap : Ki.map f = C := by
    change Ki.map (φ.comp (T i).subtype) = C
    rw [←Subgroup.map_map,map_subgroupOf_eq_of_le hKi]
  have htKi : (⟨t,ht⟩ : T i) ∈ normalizer (Ki : Set (T i)) := by
    have hh : (⟨t,ht⟩ : T i) ∈ (normalizer (Ki.map f : Set (G₀ L S))).comap f := by
      change f ⟨t,ht⟩ ∈ normalizer (Ki.map f : Set (G₀ L S))
      rw [hKmap]
      exact htg.symm ▸ hgC
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective hf] at hh
    exact hh
  have hnorm := Ki.le_normalizer_map (T i).subtype (mem_map_of_mem (T i).subtype htKi)
  rw [map_subgroupOf_eq_of_le hKi] at hnorm
  exact ⟨t,hfix,hmove,hsq,hnorm⟩

/-- Simultaneous reflections for the same original CompatibleCartans,
with precisely the four inputs consumed by the source root construction. -/
theorem original_bTwo_strict_tree_reflections
    (h : HypothesisF11 L S) {u : Vertex F}
    (hc : IsCriticalPair F (base F false) u) (hne : ⁅Z F (base F false),Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj (base F true) u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ t : Bool → (reducedAmalgam L S).Universal,
      (∀ i, t i • base T i = base T i) ∧
      (∀ i, t i • base T (!i) ≠ base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal)) := by
  choose t htfix htmove htsq htnorm using
    (fun i => original_bTwo_strict_tree_reflection h hc hne hb hβu hns hlinear c i)
  exact ⟨t,htfix,htmove,htsq,htnorm⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
