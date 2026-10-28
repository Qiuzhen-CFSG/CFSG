module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Restriction.Model.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Restriction.Model.Natural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Restriction.Model.Dual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Restriction.ModelQuotient

/-!
# Assembly of the homogeneous model restriction

The proved standard-flag calculations, for the natural and dual doubled modules,
give two natural rank-one factors on the adjacent orbit of a fixed generating
seed. The assembly transports these coordinates through the actual representation
equivalence and arbitrary flag. Innerness of SL₂(2) automorphisms matches every
prescribed surjection whose kernel is the intrinsic parabolic two-core.

`homogeneous_orbit_coordinates` completes this finite representation calculation.
Its application `secondOrbit_coordinates` supplies fixedness, generation and
the quotient kernel from the proved geometric APIs on the actual starred module.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(5), printed pp.911--912.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Once the two concrete standard calculations are established, the literal
homogeneous splitting gives coordinates for every flag, orientation and quotient. -/
theorem homogeneous_orbit_coordinates_of_standard_calculations
    (hnatural : StandardOrbitCalculation (BinaryLinearThree.W.prod BinaryLinearThree.W))
    (hdual : StandardOrbitCalculation (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual))
    (ρ : Representation (ZMod 2) SL V)
    (hsplit : Nonempty (ρ.Equiv (BinaryLinearThree.W.prod BinaryLinearThree.W)) ∨
      Nonempty (ρ.Equiv (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual)))
    (flag : SL) (i : Bool) (E : Submodule (ZMod 2) V)
    (hfixed : E ≤ BinaryOffender.fixedSpace ρ (modelParabolic flag i))
    (hgen : Seed.orbitSpace ρ ⊤ E = ⊤)
    (q : modelParabolic flag (!i) →* SL2) (hq : Function.Surjective q)
    (hker : q.ker = pCore 2 (modelParabolic flag (!i))) :
    OrbitCoordinates ρ (modelParabolic flag (!i)) E q := by
  have transfer {X : Type} [AddCommGroup X] [Module (ZMod 2) X]
      (σ : Representation (ZMod 2) SL X) (hσ : StandardOrbitCalculation σ)
      (e : ρ.Equiv σ) : OrbitCoordinates ρ (modelParabolic flag (!i)) E q := by
    have he (g : SL) (v : V) : e (ρ g v) = σ g (e v) :=
      LinearMap.congr_fun (e.isIntertwining' g) v
    apply orbit_coordinates_of_equiv ρ σ e _ E q
    apply orbit_coordinates_of_standard σ hσ flag i _ _ _ q hq hker
    · rintro _ ⟨v, hv, rfl⟩ a
      change σ a.val (e v) = e v
      rw [← he]
      exact congrArg e (hfixed hv a)
    · have h := orbitSpace_map ρ σ e.toLinearEquiv.toLinearMap he ⊤ E
      rw [hgen, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective] at h
      exact h.symm
  rcases hsplit with h | h
  · obtain ⟨e⟩ := h
    exact transfer _ hnatural e
  · obtain ⟨e⟩ := h
    exact transfer _ hdual e

/-- Every fixed generating seed in a doubled natural or doubled dual module
has two natural rank-one factors on its adjacent parabolic orbit. The coordinates
intertwine the full action through the supplied quotient, for every flag and
either orientation. -/
theorem homogeneous_orbit_coordinates
    (ρ : Representation (ZMod 2) SL V)
    (hsplit : Nonempty (ρ.Equiv (BinaryLinearThree.W.prod BinaryLinearThree.W)) ∨
      Nonempty (ρ.Equiv (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual)))
    (flag : SL) (i : Bool) (E : Submodule (ZMod 2) V)
    (hfixed : E ≤ BinaryOffender.fixedSpace ρ (modelParabolic flag i))
    (hgen : Seed.orbitSpace ρ ⊤ E = ⊤)
    (q : modelParabolic flag (!i) →* SL2) (hq : Function.Surjective q)
    (hker : q.ker = pCore 2 (modelParabolic flag (!i))) :
    ∃ e : Seed.orbitSpace ρ (modelParabolic flag (!i)) E ≃ₗ[ZMod 2]
        (Fin 2 → Fin 2 → ZMod 2),
      ∀ (a : modelParabolic flag (!i))
        (v w : Seed.orbitSpace ρ (modelParabolic flag (!i)) E),
        (w : V) = ρ a.val (v : V) → ∀ j : Fin 2,
          e w j = (q a).val.mulVec (e v j) :=
  homogeneous_orbit_coordinates_of_standard_calculations
    natural_standard_orbit_calculation dual_standard_orbit_calculation
    ρ hsplit flag i E hfixed hgen q hq hker


section Consumer
open Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The concrete standard calculations suffice on the actual starred module.
Geometry supplies the fixed seed and generation, and the descended prescribed
quotient supplies surjectivity and the intrinsic kernel. These are not extra
premises of the finite calculation. -/
theorem secondOrbit_coordinates_of_standard_calculations
    (hnatural : StandardOrbitCalculation (BinaryLinearThree.W.prod BinaryLinearThree.W))
    (hdual : StandardOrbitCalculation (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual))
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (MS93.V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s)
    (hsplit : Nonempty ((starRepresentation (geometry := geometry) d).toRepresentation.Equiv
        (BinaryLinearThree.W.prod BinaryLinearThree.W)) ∨
      Nonempty ((starRepresentation (geometry := geometry) d).toRepresentation.Equiv
        (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual))) :
    OrbitCoordinates (starRepresentation (geometry := geometry) d).toRepresentation
      (modelParabolic f.flag (!f.first)) (edgeSpace (geometry := geometry) d)
      (modelQuotient f) :=
  homogeneous_orbit_coordinates_of_standard_calculations hnatural hdual _ hsplit
    f.flag f.first _ (edgeSpace_le_fixed common radius hb s hbc d f hest)
    (edgeSpace_generates d) (modelQuotient f) (modelQuotient_surjective f)
    (modelQuotient_kernel f)

/-- On the actual starred module, homogeneous splitting gives the full natural
coordinates required for the second-star restriction in MS93 (4.6.12)(5).
The fixed seed, generation and prescribed quotient premises are all discharged. -/
theorem secondOrbit_coordinates
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (MS93.V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s)
    (hsplit : Nonempty ((starRepresentation (geometry := geometry) d).toRepresentation.Equiv
        (BinaryLinearThree.W.prod BinaryLinearThree.W)) ∨
      Nonempty ((starRepresentation (geometry := geometry) d).toRepresentation.Equiv
        (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual))) :
    OrbitCoordinates (starRepresentation (geometry := geometry) d).toRepresentation
      (modelParabolic f.flag (!f.first)) (edgeSpace (geometry := geometry) d)
      (modelQuotient f) :=
  homogeneous_orbit_coordinates _ hsplit f.flag f.first _
    (edgeSpace_le_fixed common radius hb s hbc d f hest) (edgeSpace_generates d)
    (modelQuotient f) (modelQuotient_surjective f) (modelQuotient_kernel f)

end Consumer

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction
