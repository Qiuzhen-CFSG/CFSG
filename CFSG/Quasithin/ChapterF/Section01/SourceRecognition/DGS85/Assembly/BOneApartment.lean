module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneReflections

/-!
# Constructed natural apartments in the original noncommuting b=1 branch

Both natural actions and their actor markings come from the critical pair.
Original nonsolvability supplies the nonbinary scalars; the reflection
selection constructs both moving involutions normalizing the whole chosen
Cartan. The Chapter 10 path alternatives then give r=3,s=4 or r=4,s=5,
next-length transitivity and odd fixers in the actual universal tree.
The resulting roots are literally the two-cores of paths in the same
reflection apartment, with both endpoint markings and the full Cartan fixed.

No natural coordinates, field-size bound, compatible Cartan, reflection
witness or root-element witness remains in `apartment_of_critical_bOne`.
Exchange, fusion with the chosen long-path roots, and the Borel-image root
signs still require proof before constructing a faithful marked split
quotient. This is earlier geometry, not a complete recognition theorem.

Source: DGS, Groups and Graphs (1985), (10.5), pp.156--157, and
(14.1)--(14.2) and the ensuing apartment notation, pp.210--211.
-/

open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree NaturalCubic Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open Subgroup.CosetGeometry.RankTwo hiding base

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Constructed source geometry at both marked endpoints. The root paths
belong to the same whole-Cartan apartment. Exchange and quotient root signs
are not included in these earlier data. -/
structure NaturalApartment (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (c : CompatibleCartans L (reducedSylow L S)) where
  length : ℕ
  length_eq : length = 3 ∨ length = 4
  parameters : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S))
    length (length+1)
  roots : Bool → LocalRootAction (X := (reducedAmalgam L S).Universal)
    (sourceGraph (reducedAmalgam L S))
  first : ∀ i, (roots i).a = base (Universal.cosetFamily (reducedAmalgam L S)) i
  second : ∀ i, (roots i).b = base (Universal.cosetFamily (reducedAmalgam L S)) (!i)
  normalizes : ∀ i, (roots i).reflection ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal)
  square : ∀ i, (roots i).reflection * (roots i).reflection = 1
  centralizes : ∀ i z, z ∈ cartan c →
    z ∈ RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 → Commute (roots i).reflection z
  transitive : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
    (sourceGraph (reducedAmalgam L S)) (length+1)
  odd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
    p.IsPath → p.length = length+1 →
      Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p))
  paths : ∀ i, ∃ a, ∃ p : (sourceGraph (reducedAmalgam L S)).Walk a
      (base (Universal.cosetFamily (reducedAmalgam L S)) i),
    p.IsPath ∧ p.length = length ∧
    p.penultimate = base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
    cartan c ≤ pathFixer (X := (reducedAmalgam L S).Universal) p ∧
    (roots i).root = (pathFixer (X := (reducedAmalgam L S).Universal) p).pCoreIn 2 ∧
    ∀ z ∈ p.support, z ∈ cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]

/-- Both whole-Cartan reflections and both genuine path roots are selected
from the source natural profile. Original nonsolvability supplies the
nonbinary scalars used in reflection selection. -/
theorem apartment_of_profile (h : HypothesisF11 L S)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i))
    (p : C2Source.Profile L S k₀ k₁ W₀ W₁)
    (E₁ : let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
      W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (c : CompatibleCartans L (reducedSylow L S)) : Nonempty (NaturalApartment L S c) := by
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
  obtain ⟨hQ₀,hQ₁⟩ := paired_cores_eq_centers_of_actions (reduced_triple h) p.left p.right
  obtain ⟨t₀,_,hf₀,hm₀,hs₀,_,hn₀,hc₀⟩ := exists_full_cartan_reflection h false p.left c
    p.left_actor hQ₀ hQ₁ p.natural
    (field_gt_two_of_nonsolvable h false p.left p.left_actor (hns 0))
  obtain ⟨t₁,_,hf₁,hm₁,hs₁,_,hn₁,hc₁⟩ := exists_full_cartan_reflection h true p.right c
    p.right_actor hQ₁ hQ₀ E₁
    (field_gt_two_of_nonsolvable h true p.right p.right_actor (hns 1))
  let t : Bool → (reducedAmalgam L S).Universal := fun i => if i then t₁ else t₀
  have hfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i := by
    intro i; cases i <;> assumption
  have hmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i) := by
    intro i; cases i <;> assumption
  have hsquare : ∀ i, t i*t i = 1 := by intro i; cases i <;> assumption
  have hnorm : ∀ i, t i ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal) := by
    intro i; cases i <;> assumption
  have hcentral : ∀ i z, z ∈ cartan c → z ∈ RankTwo.ballKernel
      (Universal.cosetFamily (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 → Commute (t i) z := by
    intro i; cases i <;> assumption
  obtain ⟨n,hn,hparam,ht,ho⟩ : ∃ n : ℕ, (n = 3 ∨ n = 4) ∧
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) n (n+1) ∧
      BasedPathTransitive (X := (reducedAmalgam L S).Universal) (sourceGraph (reducedAmalgam L S)) (n+1) ∧
      ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b), p.IsPath → p.length = n+1 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)) := by
    rcases original_bOne_tree_path_alternatives h p.left p.right p.left_actor p.right_actor p.natural E₁ with
      ⟨_,_,hr,ht,ho⟩ | ⟨_,_,hr,ht,ho⟩
    · exact ⟨3,Or.inl rfl,hr,ht,ho⟩
    · exact ⟨4,Or.inr rfl,hr,ht,ho⟩
  have hn2 : 1 < n := by omega
  have hnorm₀ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (p.left.actor : Set _) := by
    rw [p.left_actor]; exact reduced_borel_normalizes_source_actor h 0
  have hnorm₁ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (p.right.actor : Set _) := by
    rw [p.right_actor]; exact reduced_borel_normalizes_source_actor h 1
  have thick (v a b : SourceVertex (reducedAmalgam L S)) :
      ∃ z, (sourceGraph (reducedAmalgam L S)).Adj v z ∧ z ≠ a ∧ z ≠ b := by
    have hc := Nat.card_congr (Equiv.ofBijective _ ((bOne_tree_cover h).neighbor_bijective v))
    have hv := neighbor_card_of_actions (reduced_triple h) p.left p.right hnorm₀ hnorm₁ p.natural
      ((bOne_tree_cover h).vertex v)
    have hcount : Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet v) = Nat.card k₀+1 := hc.trans hv
    have hpair : ({a,b} : Set (SourceVertex (reducedAmalgam L S))).ncard ≤ 2 := by
      simpa using Set.ncard_insert_le a ({b} : Set (SourceVertex (reducedAmalgam L S)))
    have hgt : ({a,b} : Set (SourceVertex (reducedAmalgam L S))).ncard <
        ((sourceGraph (reducedAmalgam L S)).neighborSet v).ncard := by
      rw [Nat.card_coe_set_eq] at hcount
      rw [hcount]
      have : 1 < Nat.card k₀ := Finite.one_lt_card
      omega
    obtain ⟨z,hz,hne⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hgt
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at hne
    exact ⟨z,hz,hne⟩
  have hthick : ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
      z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
      z ≠ t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) := fun _ => thick _ _ _
  let roots := pathRoots h c n hn2 t hfix hmove hsquare hnorm ht hthick
  refine ⟨{
    length := n
    length_eq := hn
    parameters := hparam
    roots := roots
    first := pathRoots_a h c n hn2 t hfix hmove hsquare hnorm ht hthick
    second := pathRoots_b h c n hn2 t hfix hmove hsquare hnorm ht hthick
    normalizes := pathRoots_normalizes h c n hn2 t hfix hmove hsquare hnorm ht hthick
    square := pathRoots_square h c n hn2 t hfix hmove hsquare hnorm ht hthick
    centralizes := ?_
    transitive := ht
    odd := ho
    paths := ?_ }⟩
  · intro i z hz hk
    rw [pathRoots_reflection]
    exact hcentral i z hz hk
  · intro i
    let r := reflectionPath c t hfix hmove hnorm n (by omega) i
    exact ⟨r.start,r.walk,r.isPath,r.length_eq,r.previous,r.fixed,
      pathRoots_root h c n hn2 t hfix hmove hsquare hnorm ht hthick i,
      pathRoots_supported h c n hn2 t hfix hmove hsquare hnorm ht hthick i⟩

/-- All natural-profile, field, Cartan and reflection inputs are constructed
from the original nonsolvable distance-one noncommuting critical branch. -/
theorem apartment_of_critical_bOne
    (h : HypothesisF11 L S)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i))
    {v w : RankTwo.Vertex (reducedFamily L S)} (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1) :
    Nonempty (NaturalApartment L S (chosenCartans h)) := by
  obtain ⟨k₀,_,_,_,k₁,_,_,_,⟨p⟩⟩ := profile_of_nonsolvable_parabolics h hns hc hne hb
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
  exact apartment_of_profile h hns p (LinearEquiv.refl (ZMod 2) _) (chosenCartans h)

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
