module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FullElementaryMarkedProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.NonbinaryCartanReflection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.NonbinaryCartanCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan

/-!
# Full Cartan reflections in the nonbinary elementary source branch

The elementary Chapter 11 profile supplies the actual two linear quotient
markings and odd five-path fixers. Unless the beta quotient is PSL2(2),
both coefficient fields have at least four elements. Transport the markings
to every vertex and propagate the full-Cartan core centralizer along a
five-path. Its odd fixer kills that two-group. A full-Cartan neighbor
transporter then squares into this trivial centralizer, so is an involution.

The literal original Borel quotient supplies both local catalogues; no
catalogue, nonsolvability, reflection or centralizer premise is assumed.
NonbinaryElementaryRoots transports the involutions to the universal cover
and constructs the actual Chapter 14 four-path root actions. This is the
reflection input used there, not all the additional clauses of (14.2).
The binary case, nonelementary catalogue exclusions, exchange, root signs
and final marked assembly remain separate obligations.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175,
(14.1)--(14.2), pp.210--211. The full-Cartan transport argument is shared
with ApartmentExchange.NonbinaryCartanCentralizer/NonbinaryCartanReflection.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction NoncommutingProfile CommutingNontrivial
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (Reduction.G₀ L S))
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily (reducedAmalgam L S)
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype ⧸
        pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype)) 2 2)
include h hc hb hcomm helem hnb

private theorem elementary_nonbinary_markings :
    ∃ (K : Bool → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Finite (K i))
      (_ : ∀ i, CharP (K i) 2), (∀ i, 4 ≤ Nat.card (K i)) ∧
      ∀ v : Vertex F, Nonempty
        ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,K v.type)) := by
  obtain ⟨m,hm,markB,markA,_⟩ :=
    original_borel_elementary_orders_and_paths_of_source h hc hb hcomm helem
  have hm2 : 2 ≤ m := by
    by_contra hn
    have he : m = 1 := by omega
    subst m
    exact hnb (by simpa using markB)
  obtain ⟨k₀,f₀,fin₀,h₀,⟨e₀⟩⟩ := markA
  obtain ⟨k₁,f₁,fin₁,h₁,⟨e₁⟩⟩ := markB
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
  let eOrig : ∀ i, ((graphLocalGroup F (base F i)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F (base F i)).map (G₀).subtype)) ≃* PSL(2,K i) := by
    intro i
    cases i
    · exact e₀
    · exact e₁
  let eBase (i : Bool) : (graphLocalGroup F (base F i) ⧸
      pCore 2 (graphLocalGroup F (base F i))) ≃* SL(2,K i) :=
    let j := (graphLocalGroup F (base F i)).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
    (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans ((eOrig i).trans
      (MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K i))
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm)
  have hK (i : Bool) : 4 ≤ Nat.card (K i) := by
    cases i
    · change 4 ≤ Nat.card k₀
      rw [h₀]
      exact (show 2^2 ≤ 2^(2*m) from Nat.pow_le_pow_right (by decide) (by omega))
    · change 4 ≤ Nat.card k₁
      rw [h₁]
      exact (show 2^2 ≤ 2^m from Nat.pow_le_pow_right (by decide) hm2)
  exact ⟨K,inferInstance,inferInstance,inferInstance,hK,
    fun v => ⟨source_linear_quotient_at (reduced_triple h) K eBase v⟩⟩

/-- Every full edge Cartan has trivial centralizer in either incident core. -/
theorem original_elementary_nonbinary_cartan_core_centralizer
    {v w : Vertex F} (hvw : (graph F).Adj v w)
    (C : Subgroup G₀) [IsMulCommutative C]
    (hCE : C ≤ stabilizer F v ⊓ stabilizer F w)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer F v ⊓ stabilizer F w).pCoreIn 2))
    (hg : C ⊔ (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 =
      stabilizer F v ⊓ stabilizer F w) :
    Q F v ⊓ centralizer (C : Set G₀) = ⊥ := by
  let H := reduced_triple h
  obtain ⟨K,fK,finK,chK,hK,e⟩ := elementary_nonbinary_markings h hc hb hcomm helem hnb
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨_,_,_,_,_,_,_,_,_,hpar,htrans,hodd⟩ :=
    original_borel_elementary_orders_and_paths_of_source h hc hb hcomm helem
  have hval (x : Vertex F) : 3 ≤ Nat.card ((graph F).neighborSet x) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three H (reduced_vertex_sylow h) x.type
  have hs : sourceS (P := fun i => (P₀ L S i).subgroupOf G₀) = 5 :=
    (sourceS_spec H (reduced_vertex_sylow h)).2.unique hpar.2
  have htwo (x : Vertex F) : RootPathTransitive (graph F) G₀ x 2 :=
    sourceS_transitive H (reduced_vertex_sylow h) x (by omega)
  apply ApartmentExchange.full_cartan_core_centralizer_eq_bot H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) htwo K
    (fun v => Classical.choice (e v)) hK hvw C hCE ho hd hg 4
  intro p hp
  have hsimple : p.toWalk.IsPath := Theory.GroupAction.CubicTree.isPath_of_short_rightRegular
    hval 5 (fun m hm x q hq =>
      (sourceS_short_regular H (reduced_vertex_sylow h) q (by omega) hq).2) p le_rfl hp
  have he : pathFixer (X := G₀) p.toWalk = pathStabilizer F p := by
    ext x
    rw [mem_pathFixer_support,support_toWalk]
    rfl
  rw [←he,Nat.card_congr ((pathFixer (X := G₀) p.toWalk).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective).toEquiv]
  exact hodd p.toWalk (Or.inl hsimple)
    (show 5 ≤ p.toWalk.length from by rw [length_toWalk])

/-- The original local involution normalizes the entire Cartan and moves the marked neighbor. -/
theorem original_elementary_nonbinary_cartan_reflection
    {v w : Vertex F} (hvw : (graph F).Adj v w)
    (C : Subgroup G₀) [IsMulCommutative C]
    (hCE : C ≤ stabilizer F v ⊓ stabilizer F w)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer F v ⊓ stabilizer F w).pCoreIn 2))
    (hg : C ⊔ (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 =
      stabilizer F v ⊓ stabilizer F w) :
    ∃ g ∈ graphLocalGroup F v,
      g ∈ normalizer (C : Set G₀) ∧ g*g=1 ∧ g • v=v ∧ g • w≠w := by
  obtain ⟨K,fK,finK,chK,hK,e⟩ := elementary_nonbinary_markings h hc hb hcomm helem hnb
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨_,_,_,_,_,_,_,_,_,hpar,_⟩ :=
    original_borel_elementary_orders_and_paths_of_source h hc hb hcomm helem
  have hs : sourceS (P := fun i => (P₀ L S i).subgroupOf G₀) = 5 :=
    (sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).2.unique hpar.2
  exact ApartmentExchange.exists_full_cartan_reflection (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hvw
    (sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h) w (by omega))
    (Classical.choice (e v)) (by have := hK v.type; omega) C hCE ho hd hg
    (original_elementary_nonbinary_cartan_core_centralizer h hc hb hcomm helem hnb hvw C hCE ho hd hg)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
