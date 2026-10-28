module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryTreeRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedQuotient

/-!
# The finite quotient from the original unitary roots

The original PSU₃/SU₃ marking constructs the actual length-four local roots
on the universal reduced amalgam.  This extension feeds those roots into the
literal apartment quotient.  Cartans, the two reflection lifts, apartment exchange and the
root-sign alternative remain explicit inputs. The Chapter 11 profile
discharges odd five-path fixers and based five-path transitivity.  The resulting quotient keeps
both original endpoint maps and the whole original Borel map, together with
the source split factorization and saturation.

This compares the source amalgam with its geometric finite quotient.
Concrete unitary model recognition and the remaining Chapter 14 exchange
and sign obligations still require their source proofs.
Source: DGS85, Groups and Graphs (1985), (11.8)(g), pp.176--177,
(14.1)--(14.2), pp.210--211, and (3.6)--(3.7), pp.77--80.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan

variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}

variable (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀)
      (base (Reduction.reducedFamily L₀ S₀) false)
      (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) false),
        Z (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (Ma : IsRankOneModel
      ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) false)).map
          (Reduction.G₀ L₀ S₀).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
          (base (Reduction.reducedFamily L₀ S₀) false)).map
            (Reduction.G₀ L₀ S₀).subtype)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU
        ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
          (base (Reduction.reducedFamily L₀ S₀) true)).map
            (Reduction.G₀ L₀ S₀).subtype ⧸
          pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
            (base (Reduction.reducedFamily L₀ S₀) true)).map
              (Reduction.G₀ L₀ S₀).subtype)) 3 (2^m) ∨
      IsSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
        (base (Reduction.reducedFamily L₀ S₀) true)).map
          (Reduction.G₀ L₀ S₀).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀)
          (base (Reduction.reducedFamily L₀ S₀) true)).map
            (Reduction.G₀ L₀ S₀).subtype)) 3 (2^m))
    (cartans : CompatibleCartans L₀ (reducedSylow L₀ S₀))
    (t : Bool → (reducedAmalgam L₀ S₀).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) i = base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i) ≠ base (Universal.cosetFamily (reducedAmalgam L₀ S₀)) (!i))
    (htsq : ∀ i, t i * t i = 1)
    (htnorm : ∀ i, t i ∈ normalizer (cartan cartans : Set (reducedAmalgam L₀ S₀).Universal))

include h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm

noncomputable def originalUnitaryRoots : Bool → LocalRootAction (X := (reducedAmalgam L₀ S₀).Universal)
    (sourceGraph (reducedAmalgam L₀ S₀)) := by
  exact original_unitary_pathRoots_from_marking h hc hb hcomm Ma hm mark cartans t
    htfix htmove htsq htnorm

variable
    (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L₀ S₀).Universal) (sourceGraph (reducedAmalgam L₀ S₀))
      (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
        (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm))) 4)
    (hsign : ∀ i x, x ∈ apartmentGroup cartans
        (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm) →
      (∀ r ∈ (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
          htfix htmove htsq htnorm i).root, quotientMap (reducedAmalgam L₀ S₀)
        (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
          (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
          4 (x⁻¹*r*x) ∈
        (originalMiddle (reducedAmalgam L₀ S₀)).map (quotientMap (reducedAmalgam L₀ S₀)
          (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
            (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
            4)) ∨
      (∀ r ∈ (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
          htfix htmove htsq htnorm i).root, quotientMap (reducedAmalgam L₀ S₀)
        (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
          (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
          4
          (((originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
            htfix htmove htsq htnorm i).reflection*x)⁻¹*r*
            ((originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t
              htfix htmove htsq htnorm i).reflection*x)) ∈
        (originalMiddle (reducedAmalgam L₀ S₀)).map (quotientMap (reducedAmalgam L₀ S₀)
          (cartanApartment (reducedAmalgam L₀ S₀) (apartmentGroup cartans
            (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)))
            4)))

include h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm hexchange hsign

/-- The actual finite marked quotient obtained from the source unitary roots. -/
def originalUnitaryFiniteQuotient :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
      (recognitionEndpoints (reducedAmalgam L₀ S₀)) := by
  exact finiteQuotient h cartans
    (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)
    (ReducedCartan.pathRoots_normalizes h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    (ReducedCartan.pathRoots_a h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    (ReducedCartan.pathRoots_b h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    (ReducedCartan.pathRoots_square h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    4 (by decide)
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).2
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
    hexchange hsign

/-- The quotient retains both original endpoint maps and the full Borel map. -/
def originalUnitaryFiniteMarkedIso :
    RankTwoAmalgam.Iso (reducedAmalgam L₀ S₀) (originalUnitaryFiniteQuotient h hc hb hcomm Ma hm mark
      cartans t htfix htmove htsq htnorm hexchange hsign).standardAmalgam := by
  unfold originalUnitaryFiniteQuotient
  exact finiteMarkedIso h cartans
    (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)
    (ReducedCartan.pathRoots_normalizes h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    (ReducedCartan.pathRoots_a h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    (ReducedCartan.pathRoots_b h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    (ReducedCartan.pathRoots_square h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    4 (by decide)
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).2
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
    hexchange hsign

/-- The same quotient carries the original split factorization and saturation. -/
def originalUnitaryFiniteSplitData :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
      (originalUnitaryFiniteQuotient h hc hb hcomm Ma hm mark cartans t htfix htmove
        htsq htnorm hexchange hsign).tits := by
  unfold originalUnitaryFiniteQuotient
  exact finiteSplitData h cartans
    (originalUnitaryRoots h hc hb hcomm Ma hm mark cartans t htfix htmove htsq htnorm)
    (ReducedCartan.pathRoots_normalizes h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    (ReducedCartan.pathRoots_a h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    (ReducedCartan.pathRoots_b h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    (ReducedCartan.pathRoots_square h cartans 4 (by decide) t htfix htmove htsq htnorm
      (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
      (original_unitary_tree_thickness_from_marking h hc hb hcomm Ma hm mark t))
    4 (by decide)
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).2
    (original_unitary_tree_path_profile_from_marking h hc hb hcomm Ma hm mark).1
    hexchange hsign

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
