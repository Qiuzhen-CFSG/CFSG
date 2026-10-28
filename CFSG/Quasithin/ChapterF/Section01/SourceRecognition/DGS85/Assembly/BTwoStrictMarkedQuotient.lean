module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictPathThicknessSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceWeylParameter

/-!
# The strict source marked hexagon quotient

The original strict distance-two hypotheses give seven-path transitivity
and odd seven-path fixers. Source valence supplies a third neighbor for
any chosen reflection. Thus the actual six-path radicals give the finite
marked quotient, both endpoint inclusion squares, the whole reduced Borel,
and split data. Its Weyl rotation has order six.

The same-Cartan reflection choices, exchange and quotient root signs remain
explicit earlier-source inputs. No finite-model comparison is assumed.
Source: DGS, *Groups and Graphs* (1985), (10.10), p.164; (14.1)--(14.2),
pp.210--211; (3.6)--(3.7), pp.77--80.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2) (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
  (c : CompatibleCartans L (reducedSylow L S))
  (t : Bool → (reducedAmalgam L S).Universal)
  (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
    base (Universal.cosetFamily (reducedAmalgam L S)) i)
  (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
    base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
  (htsq : ∀ i, t i * t i = 1)
  (htnorm : ∀ i, t i ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal))

theorem strict_tree_path_transitive_source
    {u : Vertex (reducedFamily L S)} (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
    (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false), Z (reducedFamily L S) u⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 2) (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ}
    (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n)) :
    BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 7 := by
  have hprofile := @original_bTwo_strict_tree_path_profile_of_linear_left
    G _ L S h u hc hne hb hβu hns n hlinear
  intro a b c p q hp hq hpl hql
  exact hprofile.2.1 p q hp hq hpl hql

theorem strict_tree_path_fixers_odd_source
    {u : Vertex (reducedFamily L S)} (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
    (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false), Z (reducedFamily L S) u⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 2) (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ}
    (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n)) :
    ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length = 7 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)) := by
  have hprofile := @original_bTwo_strict_tree_path_profile_of_linear_left
    G _ L S h u hc hne hb hβu hns n hlinear
  intro a b p hp hl
  exact hprofile.2.2 p hp hl

/-- The roots are the actual two-cores of the six-path stabilizers; all
transitivity, thickness and path-factorization premises are discharged. -/
def strictPathRoots : Bool → LocalRootAction (X := (reducedAmalgam L S).Universal)
    (sourceGraph (reducedAmalgam L S)) :=
  pathRoots h c 6 (by decide) t htfix htmove htsq htnorm
    (@strict_tree_path_transitive_source G _ L S u h hc hne hb hβu hns n hlinear)
    (strict_path_thickness_source h t htfix htmove)

-- Keep dependencies explicit in section-variable types. In particular,
-- notation capturing `L`, `S`, or the roots hides their binder dependencies.
variable
  (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
    (sourceGraph (reducedAmalgam L S))
    (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 6)
  (hsign : ∀ (i : Bool) (x : (reducedAmalgam L S).Universal), x ∈ reflectionGroup c t →
    (∀ r ∈ (strictPathRoots h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm i).root,
      quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
        (reflectionGroup c t)) 6 (x⁻¹*r*x) ∈ (originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
            (reflectionGroup c t)) 6)) ∨
    (∀ r ∈ (strictPathRoots h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm i).root,
      quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
        (reflectionGroup c t)) 6 ((t i*x)⁻¹*r*(t i*x)) ∈
          (originalMiddle (reducedAmalgam L S)).map
            (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
              (reflectionGroup c t)) 6)))

/-- The finite strict quotient retains both marked endpoints and the whole Borel. -/
def strictFiniteQuotient : MarkedQuotient
    (recognitionEndpoints (reducedAmalgam L S)) :=
  pathFiniteQuotient h c 6 (by decide) t htfix htmove htsq htnorm
    (@strict_tree_path_transitive_source G _ L S u h hc hne hb hβu hns n hlinear)
    (strict_path_thickness_source h t htfix htmove)
    (@strict_tree_path_fixers_odd_source G _ L S u h hc hne hb hβu hns n hlinear)
    hexchange hsign

/-- Both endpoint inclusion squares and the entire middle map are preserved. -/
def strictFiniteMarkedIso : Iso (reducedAmalgam L S)
    (strictFiniteQuotient h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm
      hexchange hsign).standardAmalgam := by
  exact pathFiniteMarkedIso h c 6 (by decide) t htfix htmove htsq htnorm
    (@strict_tree_path_transitive_source G _ L S u h hc hne hb hβu hns n hlinear)
    (strict_path_thickness_source h t htfix htmove)
    (@strict_tree_path_fixers_odd_source G _ L S u h hc hne hb hβu hns n hlinear)
    hexchange hsign

/-- Splitness and saturation hold on that same finite source quotient. -/
def strictFiniteSplitData : SplitData
    (strictFiniteQuotient h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm
      hexchange hsign).tits := by
  exact pathFiniteSplitData h c 6 (by decide) t htfix htmove htsq htnorm
    (@strict_tree_path_transitive_source G _ L S u h hc hne hb hβu hns n hlinear)
    (strict_path_thickness_source h t htfix htmove)
    (@strict_tree_path_fixers_odd_source G _ L S u h hc hne hb hβu hns n hlinear)
    hexchange hsign

/-- The strict source path length becomes the exact Weyl rotation order. -/
theorem strictFiniteQuotient_rotation :
    rotationOrder
      (strictFiniteQuotient h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm
        hexchange hsign) = 6 := by
  exact pathFiniteQuotient_simple_product_order h c 6 (by decide) t htfix htmove htsq htnorm
    (@strict_tree_path_transitive_source G _ L S u h hc hne hb hβu hns n hlinear)
    (strict_path_thickness_source h t htfix htmove)
    (@strict_tree_path_fixers_odd_source G _ L S u h hc hne hb hβu hns n hlinear) hexchange hsign

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
