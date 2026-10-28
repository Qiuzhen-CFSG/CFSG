module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Parabolics
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-!
# The marked relative Weyl group and the actual standard apartment

The standard apartment is the normalizer orbit of the two standard parabolic
cosets in the existing Ree graph. We specify the required dihedral quotient
with both simple reflections marked, and the group-translation assertion for
sixteen-cycles. These are separate, unproved inputs to the final construction.

The actual fixed torus has odd order. Thus containment of the standard
apartment's pointwise fixer in that torus would prove its oddness. Group
conjugation then transports oddness to every apartment once the translation
assertion is proved. None of these reductions assumes normalizer coverage.

Source: GLS3 §§2.3 and 2.6, `refs/KGroup/GLS3/chapter2.tex`, for the BN-pair
apartment construction used in finite Borel–Tits (GLS3 3.1.3).
-/

@[expose] public section
noncomputable section
namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
open Subgroup LargeLocalSeeds Parabolics SectionGeometry.BNPair
attribute [local instance] borel_inf_normalizerWords_normal

open scoped Pointwise

/-- A marked isomorphism of the actual normalizer quotient with the relative
Weyl group of order sixteen. The linear reflection is `sr 0`, the Suzuki
reflection is `sr 1`; their product is the rotation `r 1`. -/
def HasOctagonalWeylGroup (m : ℕ) : Prop :=
  ∃ e : WeylQuotient m ≃* DihedralGroup 8,
    e (simpleReflection m .linear) = DihedralGroup.sr 0 ∧
    e (simpleReflection m .suzuki) = DihedralGroup.sr 1

/-- The standard apartment consists of the vertices in the normalizer orbit
of the two standard parabolic cosets. No cycle assertion is part of this definition. -/
def standardApartment (m : ℕ) : Set (Vertex m) :=
  {v | ∃ n ∈ normalizerWords m, ∃ s : Side,
    n • CosetGeometry.base (ConverseParabolics.parabolic m) s = v}

/-- Every sixteen-cycle is an actual group translate of the normalizer apartment. -/
def ApartmentTranslates (m : ℕ) : Prop :=
  ∀ v (p : (incidenceGraph m).Walk v v), p.IsCycle → p.length = 16 →
    ∃ g : Model m, g • standardApartment m = {w | w ∈ p.support}

theorem base_mem_standardApartment (m : ℕ) (s : Side) :
    CosetGeometry.base (ConverseParabolics.parabolic m) s ∈ standardApartment m :=
  ⟨1, (normalizerWords m).one_mem, s, one_smul _ _⟩

/-- Fixing every standard apartment vertex in particular fixes both standard
parabolic cosets, whose common stabilizer is the full root-defined Borel. -/
theorem standardApartment_fixer_le_borel (m : ℕ) (hm : 1 ≤ m) :
    fixingSubgroup (Model m) (standardApartment m) ≤ borel m := by
  rw [← parabolic_inf_eq_borel m hm]
  apply le_inf
  all_goals
    intro x hx
    rw [← CosetGeometry.stabilizer_base (ConverseParabolics.parabolic m)]
    exact (mem_fixingSubgroup_iff _).mp hx _ (base_mem_standardApartment m _)

/-- Oddness of the actual fixed torus; it is a subgroup of the odd split torus. -/
theorem fixedTorus_card_odd (m : ℕ) : Odd (Nat.card (fixedTorus m)) :=
  Parabolics.fixedTorus_odd_card m (splitTorus_card_odd m)

/-- Bounding the actual fixer by the fixed torus suffices; no exact stabilizer
or whole-group order calculation is required. -/
theorem standardApartment_fixer_odd_of_le_fixedTorus (m : ℕ)
    (hle : fixingSubgroup (Model m) (standardApartment m) ≤ fixedTorus m) :
    Odd (Nat.card (fixingSubgroup (Model m) (standardApartment m))) :=
  (fixedTorus_card_odd m).of_dvd_nat (card_dvd_of_le hle)

/-- Apartment conjugacy transports oddness of the actual pointwise fixer to
every sixteen-cycle in the specified coset graph. Both inputs remain explicit. -/
theorem oddApartmentStabilizers_of_apartment_translates {m : ℕ}
    (htrans : ApartmentTranslates m)
    (hodd : Odd (Nat.card (fixingSubgroup (Model m) (standardApartment m)))) :
    OddApartmentStabilizers m := by
  intro v p hp hlen
  obtain ⟨g, hg⟩ := htrans v p hp hlen
  rw [← Nat.card_congr (SubMulAction.fixingSubgroupEquivFixingSubgroup hg).toEquiv]
  exact hodd

end ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
