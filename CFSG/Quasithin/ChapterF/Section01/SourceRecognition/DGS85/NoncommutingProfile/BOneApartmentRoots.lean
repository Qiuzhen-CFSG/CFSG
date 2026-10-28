module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourcePathRoots

/-!
# Applying the b=1 profile to the actual apartment roots

The source valence q+1 proves thickness of the universal tree through its
literal coset covering. The two alternatives of (10.5) supply four- or
five-path transitivity and odd stabilizers there. Applying the existing
Chapter 14 construction therefore gives roots that are exactly O₂ of
three- or four-path stabilizers, based at the original oriented edge.

The paths retain pointwise fixation by the chosen compatible Cartan, and
the roots retain both selected reflections. Their Chapter 14 reflection
choices remain explicit; no exchange, quotient recognition or ambient
completion conclusion is assumed or asserted.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.156--157, and the
root construction (14.1)--(14.2), pp.210--211.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam OriginalExtension SuzukiContainment
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : HypothesisF11 L S)
    (c₀ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) k₀ W₀)
    (c₁ : BOneActionData (reducedFamily L S) (base (reducedFamily L S) true)
      (base (reducedFamily L S) false) k₁ W₁)
    (hactor₀ : c₀.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
    (hactor₁ : c₁.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S))
local instance bOneRootsAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
include h c₀ c₁ hactor₀ hactor₁ E₀

private theorem tree_thick (v a b : SourceVertex (reducedAmalgam L S)) :
    ∃ z, (sourceGraph (reducedAmalgam L S)).Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hn₀ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₀.actor : Set (G₀ L S)) := by
    rw [hactor₀]
    exact reduced_borel_normalizes_source_actor h 0
  have hn₁ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₁.actor : Set (G₀ L S)) := by
    rw [hactor₁]
    exact reduced_borel_normalizes_source_actor h 1
  let cov := bOne_tree_cover h
  have hc := Nat.card_congr (Equiv.ofBijective _ (cov.neighbor_bijective v))
  have hv := neighbor_card_of_actions (reduced_triple h) c₀ c₁ hn₀ hn₁ E₀ (cov.vertex v)
  have hcount : Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet v) = Nat.card k₀ + 1 :=
    hc.trans hv
  have hgt : 2 < ((sourceGraph (reducedAmalgam L S)).neighborSet v).ncard := by
    rw [←Nat.card_coe_set_eq,hcount]
    have : 1 < Nat.card k₀ := Finite.one_lt_card
    omega
  by_contra hnone
  have hs : (sourceGraph (reducedAmalgam L S)).neighborSet v ⊆ {a,b} := by
    intro z hz
    by_cases hza : z = a
    · exact Or.inl hza
    · exact Or.inr (by by_contra hzb; exact hnone ⟨z,hz,hza,hzb⟩)
  have hle := Set.ncard_le_ncard hs
  have hpair : ({a,b} : Set (SourceVertex (reducedAmalgam L S))).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le a ({b} : Set (SourceVertex (reducedAmalgam L S)))
  omega

include E₁ in
/-- Apply both b=1 alternatives to the actual Chapter 14 root construction.
The roots are radicals of paths of length three or four, and retain the
chosen source Cartan, reflections and original endpoint markings. -/
theorem original_bOne_pathRoots
    (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i * t i = 1)
    (htnorm : ∀ i, t i ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal)) :
    ∃ n : ℕ, (n = 3 ∨ n = 4) ∧
      ∃ roots : Bool → LocalRootAction (X := (reducedAmalgam L S).Universal)
        (sourceGraph (reducedAmalgam L S)),
        (∀ i, (roots i).a = base (Universal.cosetFamily (reducedAmalgam L S)) i) ∧
        (∀ i, (roots i).b = base (Universal.cosetFamily (reducedAmalgam L S)) (!i)) ∧
        (∀ i, (roots i).reflection = t i) ∧
        (∀ i, ∃ a, ∃ p : (sourceGraph (reducedAmalgam L S)).Walk a
            (base (Universal.cosetFamily (reducedAmalgam L S)) i),
          p.IsPath ∧ p.length = n ∧ p.penultimate = base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
          cartan c ≤ pathFixer (X := (reducedAmalgam L S).Universal) p ∧
          (roots i).root = (pathFixer (X := (reducedAmalgam L S).Universal) p).pCoreIn 2) ∧
        (∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
          p.IsPath → p.length = n+1 →
            Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p))) := by
  have he : ∃ n : ℕ, (n = 3 ∨ n = 4) ∧
      BasedPathTransitive (X := (reducedAmalgam L S).Universal)
        (sourceGraph (reducedAmalgam L S)) (n+1) ∧
      ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
        p.IsPath → p.length = n+1 →
          Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)) := by
    rcases original_bOne_tree_path_alternatives h c₀ c₁ hactor₀ hactor₁ E₀ E₁ with
      ⟨_,_,_,ht,ho⟩ | ⟨_,_,_,ht,ho⟩
    · exact ⟨3,Or.inl rfl,ht,ho⟩
    · exact ⟨4,Or.inr rfl,ht,ho⟩
  obtain ⟨n,hn,ht,ho⟩ := he
  have hn2 : 1 < n := by omega
  have hthick : ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
      z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
      z ≠ t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) :=
    fun i => tree_thick h c₀ c₁ hactor₀ hactor₁ E₀ _ _ _
  let roots := pathRoots h c n hn2 t htfix htmove htsq htnorm ht hthick
  refine ⟨n,hn,roots,?_,?_,?_,?_,ho⟩
  · exact pathRoots_a h c n hn2 t htfix htmove htsq htnorm ht hthick
  · exact pathRoots_b h c n hn2 t htfix htmove htsq htnorm ht hthick
  · exact pathRoots_reflection h c n hn2 t htfix htmove htsq htnorm ht hthick
  · intro i
    let p := reflectionPath c t htfix htmove htnorm n (by omega) i
    exact ⟨p.start,p.walk,p.isPath,p.length_eq,p.previous,p.fixed,
      pathRoots_root h c n hn2 t htfix htmove htsq htnorm ht hthick i⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
