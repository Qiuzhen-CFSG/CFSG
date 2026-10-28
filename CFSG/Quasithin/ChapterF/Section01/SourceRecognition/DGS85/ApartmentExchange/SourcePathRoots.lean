module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReflectionPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedQuotient

/-!
# Genuine long-path roots in the source finite split quotient

For the reduced F.1.11 pair choose compatible Cartans by the proved source
construction. Given the two same-Cartan involutions and regular s-path
transitivity, construct paths of length r = s-1 in their actual apartment.
Their pointwise stabilizers factor as their own two-cores times K. Thus these
literal long-path radicals, together with the chosen reflections, give both
local root actions. The whole source Borel and both original endpoint maps
then enter the finite marked split quotient constructed in `ReducedQuotient`.

No local root-action witness, path-product equation or split factorization
is assumed. The remaining inputs are the reflection choices, local thickness,
odd s-path stabilizers, s-path transitivity, exchange and quotient root signs.
The full (14.2) choice, including local-kernel centralization and the prescribed
involution conjugacy used later in (14.17), and the (14.19) exceptional/regular
alternative remain source obligations. This does not prove Theorem D or
finite-model recognition.

Source: DGS, *Groups and Graphs* (1985), Part II, (14.1)--(14.2) and the
root definitions, pp.210--211; (3.6)--(3.7), pp.77--80; Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))

variable (n : ℕ) (hn : 1 < n)
variable (t : Bool → (reducedAmalgam L S).Universal)
variable (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
  base (Universal.cosetFamily (reducedAmalgam L S)) i)
variable (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
  base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
variable (htsq : ∀ i, t i * t i = 1)
variable (htnorm : ∀ i, t i ∈
  Subgroup.normalizer (cartan c : Set (reducedAmalgam L S).Universal))
variable (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (n+1))
variable (hthick : ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
  (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
  z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
  z ≠ t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i))

/-- Construct both local actions using the actual two-cores of chosen long-path stabilizers. -/
def pathRoots : Bool → LocalRootAction (X := (reducedAmalgam L S).Universal)
    (sourceGraph (reducedAmalgam L S)) := fun i =>
  let p := reflectionPath c t htfix htmove htnorm n (by omega) i
  pathRootAction (Universal.cosetGraph_isTree (reducedAmalgam L S)
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic p.walk p.isPath
    (by
      intro hnil
      have hz : p.walk.length = 0 := hnil.length_eq_zero
      rw [p.length_eq] at hz
      omega)
    (source_action (reducedAmalgam L S))
    (by rw [p.length_eq]; exact htrans) (cartan c) (t i) (htfix i)
    (by simpa only [p.previous] using htmove i) (htsq i)
    (by
      intro k hk
      rw [p.previous]
      apply reflectionApartment_fixed c t htnorm k hk
      exact cartanApartment_preserves (reducedAmalgam L S) (reflectionGroup c t)
        (reflectionGroup_mem c t i)
        (cartanApartment_base (reducedAmalgam L S) (reflectionGroup c t) (!i)))
    (pathFixer_factorization c h p.walk p.previous p.fixed)
    (by simpa only [p.previous] using hthick i)


/-- Each root is based at the original marked endpoint. -/
theorem pathRoots_a (i : Bool) : ((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).a =
    base (Universal.cosetFamily (reducedAmalgam L S)) i := rfl

/-- The preceding path vertex is the other original endpoint. -/
theorem pathRoots_b (i : Bool) : ((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).b =
    base (Universal.cosetFamily (reducedAmalgam L S)) (!i) :=
  (reflectionPath c t htfix htmove htnorm n (by omega) i).previous

/-- The construction retains the given reflection lifts exactly. -/
theorem pathRoots_reflection (i : Bool) : ((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).reflection = t i := rfl

/-- The root is literally O₂ of the same chosen path stabilizer. -/
theorem pathRoots_root (i : Bool) : ((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).root =
    (pathFixer (X := (reducedAmalgam L S).Universal)
      (reflectionPath c t htfix htmove htnorm n (by omega) i).walk).pCoreIn 2 := rfl

/-- Constructing roots does not change the chosen reflection apartment group. -/
theorem pathRoots_apartmentGroup : apartmentGroup c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) = reflectionGroup c t := rfl

/-- The defining path lies in this same apartment, as required for later root-sign arguments. -/
theorem pathRoots_supported (i : Bool) :
    ∀ z ∈ (reflectionPath c t htfix htmove htnorm n (by omega) i).walk.support,
      z ∈ cartanApartment (reducedAmalgam L S)
        (apartmentGroup c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick)) :=
  (reflectionPath c t htfix htmove htnorm n (by omega) i).supported

/-- The constructed actions retain normalization of the same source Cartan. -/
theorem pathRoots_normalizes (i : Bool) : ((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).reflection ∈
    Subgroup.normalizer (cartan c : Set (reducedAmalgam L S).Universal) := htnorm i

/-- The constructed actions retain the original involutions. -/
theorem pathRoots_square (i : Bool) : ((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).reflection * ((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).reflection = 1 := htsq i

variable (hodd : ∀ {a b} (q : (sourceGraph (reducedAmalgam L S)).Walk a b),
  q.IsPath → q.length = n+1 →
    Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) q)))
variable (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S))
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick))) n)
variable (hsign : ∀ i x, x ∈ apartmentGroup c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) →
  (∀ r ∈ ((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick))) n (x⁻¹*r*x) ∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick))) n)) ∨
  (∀ r ∈ ((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick))) n
    ((((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).reflection*x)⁻¹*r*(((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).reflection*x)) ∈
      (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
        (cartanApartment (reducedAmalgam L S) (apartmentGroup c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick))) n)))

include h c n hn t htfix htmove htsq htnorm htrans hthick hodd hexchange hsign
/-- The actual long-path roots feed the finite quotient with exactly two marked simple reflections and both parabolic equations. -/
def pathFiniteQuotient : Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
    (recognitionEndpoints (reducedAmalgam L S)) := by
  exact finiteQuotient h c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_normalizes h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_a h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_b h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_square h c n hn t htfix htmove htsq htnorm htrans hthick)
    n hn hodd htrans hexchange hsign

/-- The quotient marking preserves both original reduced endpoint inclusions and the full middle map. -/
def pathFiniteMarkedIso : RankTwoAmalgam.Iso (reducedAmalgam L S)
    (pathFiniteQuotient h c n hn t htfix htmove htsq htnorm htrans hthick
      hodd hexchange hsign).standardAmalgam := by
  exact finiteMarkedIso h c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_normalizes h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_a h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_b h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_square h c n hn t htfix htmove htsq htnorm htrans hthick)
    n hn hodd htrans hexchange hsign

/-- The same actual quotient is split and saturated, with all source split-factorization premises discharged. -/
def pathFiniteSplitData : Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
    (pathFiniteQuotient h c n hn t htfix htmove htsq htnorm htrans hthick
      hodd hexchange hsign).tits := by
  exact finiteSplitData h c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_normalizes h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_a h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_b h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_square h c n hn t htfix htmove htsq htnorm htrans hthick)
    n hn hodd htrans hexchange hsign

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
