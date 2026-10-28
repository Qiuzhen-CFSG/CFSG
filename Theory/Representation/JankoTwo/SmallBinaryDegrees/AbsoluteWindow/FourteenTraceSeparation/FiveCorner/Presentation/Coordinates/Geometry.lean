module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.SchreierData
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Edges
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Orbits
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# From checked generator edges to the literal J₂ coset geometry

Right generator transitions imply coverage by P times the proposed rows,
using the actual defining pair of J₂. Since |P| times 24192 equals |J₂|,
coverage is bijective. Its inverse supplies the exact right-coset equality
criterion, without normality. The independent root and subgroup-word walks
then give the saved representatives and double-coset coverage.

The unconditional `rightCosetGeometry` supplies the checked edge and orbit
certificates to this construction. It discharges exactly the geometry input of
literalCoordinates_of_certificates, using the unchanged subgroup and tables.
Source: the retained ATLAS coset discovery in Presentation/source/README.md;
local application: Guralnick--Malle Proposition 5.1.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry
open Sporadic.LeechRelated.J2

namespace SchreierCertificate
variable (S : SchreierCertificate)

def normalForm (z : subgroup × Point) : Carrier := (z.1 : Carrier) * S.repr z.2

private theorem covered_mul_letter {g : Carrier}
    (hg : ∃ z, S.normalForm z = g) (l : Fin 4) :
    ∃ z, S.normalForm z = g * letter l := by
  obtain ⟨⟨p, x⟩, rfl⟩ := hg
  obtain ⟨q, hq⟩ := S.edge x l
  refine ⟨⟨p * q, step l x⟩, ?_⟩
  change (p : Carrier) * (q : Carrier) * S.repr (step l x) =
    ((p : Carrier) * S.repr x) * letter l
  rw [mul_assoc, ← hq, mul_assoc]

theorem normalForm_surjective : Function.Surjective S.normalForm := by
  intro g
  have hg : g ∈ Subgroup.closure ({GeneratorPair.a, GeneratorPair.b} : Set Carrier) := by
    rw [GeneratorPair.closure_pair_eq_top]
    trivial
  refine Subgroup.closure_induction_right (p := fun x _ => ∃ z, S.normalForm z = x)
    ?_ ?_ ?_ hg
  · exact ⟨(1, 0), by simp [normalForm, S.at_zero]⟩
  · intro x _ y hy hx
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact S.covered_mul_letter hx 2
    · have hy' : y = GeneratorPair.b := Set.mem_singleton_iff.mp hy
      subst y
      exact S.covered_mul_letter hx 3
  · intro x _ y hy hx
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact S.covered_mul_letter hx 0
    · have hy' : y = GeneratorPair.b := Set.mem_singleton_iff.mp hy
      subst y
      exact S.covered_mul_letter hx 1

theorem normalForm_bijective : Function.Bijective S.normalForm := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨S.normalForm_surjective, ?_⟩
  rw [Nat.card_prod, card_subgroup, Nat.card_fin,
    ExceptionalParabolics.FirstParabolic.card_carrier]

def normalFormEquiv : subgroup × Point ≃ Carrier :=
  Equiv.ofBijective S.normalForm S.normalForm_bijective

def coset (g : Carrier) : Point := (S.normalFormEquiv.symm g).2

theorem coset_normalForm (p : subgroup) (x : Point) :
    S.coset ((p : Carrier) * S.repr x) = x :=
  congrArg Prod.snd (S.normalFormEquiv.symm_apply_apply (p, x))

theorem decomposition (g : Carrier) :
    g = ((S.normalFormEquiv.symm g).1 : Carrier) * S.repr (S.coset g) :=
  (S.normalFormEquiv.apply_symm_apply g).symm

theorem coset_one : S.coset 1 = 0 := by
  simpa only [S.at_zero, OneMemClass.coe_one, one_mul] using S.coset_normalForm 1 0

theorem coset_mul_left (p : subgroup) (g : Carrier) :
    S.coset ((p : Carrier) * g) = S.coset g := by
  have hg := S.decomposition g
  calc
    S.coset ((p : Carrier) * g) = S.coset
        (((p * (S.normalFormEquiv.symm g).1 : subgroup) : Carrier) *
          S.repr (S.coset g)) := by
      congr 1
      calc
        (p : Carrier) * g = (p : Carrier) *
            (((S.normalFormEquiv.symm g).1 : Carrier) * S.repr (S.coset g)) :=
          congrArg ((p : Carrier) * ·) hg
        _ = _ := by rw [Subgroup.coe_mul, mul_assoc]
    _ = S.coset g := S.coset_normalForm _ _

theorem coset_eq_iff (g h : Carrier) :
    S.coset g = S.coset h ↔ h * g⁻¹ ∈ subgroup := by
  constructor
  · intro he
    have hg := S.decomposition g
    have hh := S.decomposition h
    rw [he] at hg
    have hprod : h * g⁻¹ = ((S.normalFormEquiv.symm h).1 : Carrier) *
        ((S.normalFormEquiv.symm g).1 : Carrier)⁻¹ := by
      calc
        _ = (((S.normalFormEquiv.symm h).1 : Carrier) * S.repr (S.coset h)) *
            (((S.normalFormEquiv.symm g).1 : Carrier) * S.repr (S.coset h))⁻¹ :=
          congrArg₂ (fun a b : Carrier => a * b⁻¹) hh hg
        _ = _ := by simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
    rw [hprod]
    exact subgroup.mul_mem (S.normalFormEquiv.symm h).1.property
      (subgroup.inv_mem (S.normalFormEquiv.symm g).1.property)
  · intro he
    have ht := S.coset_mul_left ⟨h * g⁻¹, he⟩ g
    simpa only [inv_mul_cancel_right] using ht.symm

theorem coset_letter (g : Carrier) (l : Fin 4) :
    S.coset (g * letter l) = step l (S.coset g) := by
  obtain ⟨q, hq⟩ := S.edge (S.coset g) l
  calc
    S.coset (g * letter l) = S.coset
        ((((S.normalFormEquiv.symm g).1 * q : subgroup) : Carrier) *
          S.repr (step l (S.coset g))) := by
      congr 1
      calc
        g * letter l = (((S.normalFormEquiv.symm g).1 : Carrier) *
            S.repr (S.coset g)) * letter l := congrArg (· * letter l) (S.decomposition g)
        _ = _ := by rw [mul_assoc, hq, Subgroup.coe_mul, mul_assoc]
    _ = _ := S.coset_normalForm _ _

theorem coset_word (g : Carrier) (w : List (Fin 4)) :
    S.coset (g * word w) = walk w (S.coset g) := by
  induction w generalizing g with
  | nil => simp [word, walk]
  | cons l w ih =>
    simpa [word, walk, List.foldl_cons, ← mul_assoc, S.coset_letter] using
      ih (g * letter l)

theorem coset_representative (O : OrbitCertificate) (i : Fin 1008) :
    S.coset (representative i) = root i := by
  simpa only [one_mul, S.coset_one, O.representatives, representative] using
    S.coset_word 1 (representativeWord i)

theorem double_cover (O : OrbitCertificate) (g : Carrier) :
    ∃ p q : subgroup,
      g = (p : Carrier) * representative (orbit (S.coset g)) * (q : Carrier) := by
  obtain ⟨t, ht⟩ := O.orbits (S.coset g)
  let q := CoefficientTheory.subgroupElement t
  have hc : S.coset (representative (orbit (S.coset g)) * (q : Carrier)) = S.coset g := by
    rw [show (q : Carrier) = word (subgroupWord t) from (word_subgroupWord t).symm,
      S.coset_word, S.coset_representative O, ht]
  have hp := (S.coset_eq_iff _ g).mp hc
  refine ⟨⟨_, hp⟩, q, ?_⟩
  change g = (g * (representative (orbit (S.coset g)) * (q : Carrier))⁻¹) *
    representative (orbit (S.coset g)) * (q : Carrier)
  simp only [mul_assoc, inv_mul_cancel, mul_one]

def rightCosetGeometry (O : OrbitCertificate) : RightCosetGeometry where
  coset := S.coset
  coset_one := S.coset_one
  coset_eq_iff := S.coset_eq_iff
  coset_letter := S.coset_letter
  coset_representative := S.coset_representative O
  double_cover := S.double_cover O

end SchreierCertificate

/-- The precise fixed-table obligations suffice for the original geometric
contract. Final assembly must supply both finite proofs. -/
def rightCosetGeometry_of_checks (h : EdgeChecks) (O : OrbitCertificate) :
    RightCosetGeometry :=
  (schreierCertificate_of_edgeChecks h).rightCosetGeometry O

/-- The fixed action is the actual right-coset geometry of the literal order-25
subgroup of J₂, including the saved representatives and double-coset coverage.
Both finite inputs are discharged by kernel-checked certificates. -/
def rightCosetGeometry : RightCosetGeometry :=
  rightCosetGeometry_of_checks edgeChecks orbitCertificate

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry
