module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.WeylParameter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourcePathRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.DihedralWords

/-!
# The source apartment parameter in the marked finite quotient

Apply the periodic-line calculation to the actual reduced F.1.11 pair and
its chosen long-path roots. The two original simple reflections have product
of order n, the same n used for the length-n roots and length-2n apartment
identifications. The earlier regular profiles supply n = r = s-1.

Using the existing marked finite-dihedral coordinates, this gives an actual
isomorphism to `DihedralGroup n` carrying the original ordered simple
reflections to `sr 0` and `sr 1`. This discharges the geometric parameter
identification needed by finite root-coordinate recognition. It changes
neither endpoint inclusion nor the whole original Borel map.

Reflection selection, the regular-path inputs, Chapter 14 exchange and
quotient root signs remain explicit in the same finite-quotient constructor.
The parameter theorem is downstream of that construction and cannot supply
those premises or finish (14.19) or Theorem D.

Source: DGS, *Groups and Graphs* (1985), Part II, (3.6)--(3.7), pp.77--80,
(14.1)--(14.2), pp.210--211, and Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
variable (roots : Bool → LocalRootAction (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)))

variable (hnormalizes : ∀ i, (roots i).reflection ∈
  Subgroup.normalizer (cartan c : Set (reducedAmalgam L S).Universal))

variable (ha : ∀ i, (roots i).a = base (Universal.cosetFamily (reducedAmalgam L S)) i)
variable (hb : ∀ i, (roots i).b = base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
variable (hinv : ∀ i, (roots i).reflection * (roots i).reflection = 1)
variable (n : ℕ) (hn : 1 < n)
variable (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
  p.IsPath → p.length = n+1 →
    Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)))
variable (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (n+1))
variable (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S))
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n)
variable (hsign : ∀ i x, x ∈ apartmentGroup c roots →
  (∀ r ∈ (roots i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n (x⁻¹*r*x) ∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n)) ∨
  (∀ r ∈ (roots i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n
    (((roots i).reflection*x)⁻¹*r*((roots i).reflection*x)) ∈
      (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
        (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n)))

/-- The actual reduced source quotient has the same marked Weyl parameter as its apartment. -/
theorem finiteQuotient_simple_product_order :
    let d := finiteQuotient h c roots hnormalizes ha hb hinv n hn hodd htrans hexchange hsign
    orderOf (d.simple 0 * d.simple 1) = n := by
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  exact periodic_simple_product_order (reducedAmalgam L S) roots ha hb
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))
    (apartmentGroup c roots) (cartan c) (reflection_mem_apartmentGroup c roots)
    (cartan_le c) (apartmentGroup_normalizes c roots hnormalizes) le_rfl hinv n
    (cartan_le_apartmentGroup c roots) hn (cartan_hall c) hodd htrans hexchange
    (original_core_eq_bot h) hsign

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

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

/-- The chosen long-path roots and the literal source finite quotient retain r = s-1 as the Weyl parameter. -/
theorem pathFiniteQuotient_simple_product_order :
    let d := pathFiniteQuotient h c n hn t htfix htmove htsq htnorm htrans hthick
      hodd hexchange hsign
    orderOf (d.simple 0 * d.simple 1) = n := by
  exact finiteQuotient_simple_product_order h c
    (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_normalizes h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_a h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_b h c n hn t htfix htmove htsq htnorm htrans hthick)
    (pathRoots_square h c n hn t htfix htmove htsq htnorm htrans hthick)
    n hn hodd htrans hexchange hsign


open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

private theorem cast_dihedral_sr {a b : ℕ} (he : a = b) (k : ℕ) :
    (MulEquiv.cast (M := DihedralGroup) he) (.sr (k : ZMod a)) = .sr (k : ZMod b) := by
  cases he
  rfl

local notation "pathD" => pathFiniteQuotient h c n hn t htfix htmove htsq htnorm htrans
  hthick hodd hexchange hsign

/-- The actual source Weyl group has dihedral coordinates with the proved source parameter. -/
def pathFiniteQuotient_weylEquiv : Weyl (pathD) ≃* DihedralGroup n :=
  (weylEquiv (pathD)).trans
    (MulEquiv.cast (M := DihedralGroup)
      (show rotationOrder (pathD) = n from
        pathFiniteQuotient_simple_product_order h c n hn t htfix htmove htsq htnorm htrans
          hthick hodd hexchange hsign))

/-- The first original endpoint keeps the zero reflection under the source dihedral coordinates. -/
theorem pathFiniteQuotient_weylEquiv_zero :
    pathFiniteQuotient_weylEquiv h c n hn t htfix htmove htsq htnorm htrans
      hthick hodd hexchange hsign ((pathD).simple 0) = .sr 0 := by
  unfold pathFiniteQuotient_weylEquiv
  rw [MulEquiv.trans_apply, weylEquiv_simple_zero]
  simpa only [Nat.cast_zero] using cast_dihedral_sr
    (show rotationOrder (pathD) = n from pathFiniteQuotient_simple_product_order h c n hn t
      htfix htmove htsq htnorm htrans hthick hodd hexchange hsign) 0

/-- The second original endpoint keeps the unit reflection, without reversing the markings. -/
theorem pathFiniteQuotient_weylEquiv_one :
    pathFiniteQuotient_weylEquiv h c n hn t htfix htmove htsq htnorm htrans
      hthick hodd hexchange hsign ((pathD).simple 1) = .sr 1 := by
  unfold pathFiniteQuotient_weylEquiv
  rw [MulEquiv.trans_apply, weylEquiv_simple_one]
  simpa only [Nat.cast_one] using cast_dihedral_sr
    (show rotationOrder (pathD) = n from pathFiniteQuotient_simple_product_order h c n hn t
      htfix htmove htsq htnorm htrans hthick hodd hexchange hsign) 1

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
