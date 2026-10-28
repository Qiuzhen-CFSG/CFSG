module

public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.ElementaryAbelian.Quotient

/-!
# The central omega layer and split torus in the unitary model

For the standard ternary Hermitian form in characteristic two, a root element
has square one exactly when its first coordinate vanishes. Its second coordinate
then lies in the fixed field. Thus the first omega subgroup of the explicit root
Sylow is the additive fixed field, embedded by the actual projective matrices.
The split torus is the image of the multiplicative fixed field in the diagonal
matrices; its action on the central coordinate has weight minus two.

Source: Aschbacher–Smith, Proposition 16.5.1, printed p.1194, first paragraph;
Hermitian root and torus coordinates from Huppert II.10.12.
-/

@[expose] public section

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.Unitary
open BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

abbrev fixedField := FixedBy.subfield E J.conj

theorem fixedField_mem (b : fixedField J) : J.conj (b : E) = b := b.property

variable [CharP E 2]

/-- The additive fixed field inside the Hermitian Heisenberg coordinates. -/
def centralCoord : Multiplicative (fixedField J) →* hermitianUnipotentCoord J where
  toFun b := ⟨(0, (b.toAdd : E)), by
    simp only [zero_mul, fixedField_mem, CharTwo.add_self_eq_zero]⟩
  map_one' := rfl
  map_mul' b c := by
    apply Subtype.ext
    apply Prod.ext
    · exact (zero_add 0).symm
    · change (b.toAdd : E) + c.toAdd =
        (b.toAdd : E) + c.toAdd - 0 * J.conj 0
      simp

theorem centralCoord_injective : Function.Injective (centralCoord J) := by
  intro b c he
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg (fun z : hermitianUnipotentCoord J => z.val.2) he

theorem square_eq_one_iff (z : hermitianUnipotentCoord J) :
    z ^ 2 = 1 ↔ z.val.1 = 0 := by
  constructor
  · intro hz
    have hh := congrArg (fun w : hermitianUnipotentCoord J => w.val.2) hz
    rw [EvenInner.square_coordinates] at hh
    exact (mul_eq_zero.mp hh).elim id ((map_eq_zero J.conj).mp)
  · intro hz
    apply Subtype.ext
    rw [EvenInner.square_coordinates, hz]
    exact Prod.ext rfl (zero_mul _)

theorem mem_centralCoord_range (z : hermitianUnipotentCoord J) :
    z ∈ (centralCoord J).range ↔ z.val.1 = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    rfl
  · intro hz
    have hb : J.conj z.val.2 = z.val.2 := by
      have hp := z.property
      rw [hz, zero_mul, add_zero] at hp
      exact (eq_neg_of_add_eq_zero_right hp).trans (CharTwo.neg_eq _)
    exact ⟨Multiplicative.ofAdd ⟨z.val.2, hb⟩, Subtype.ext (Prod.ext hz.symm rfl)⟩

variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- The central root homomorphism into the actual projective group. -/
def centralMap : Multiplicative (fixedField J) →*
    ProjectiveSpecialUnitaryMatrixGroup J :=
  (hermitianUnipotentPSU J hJ).comp (centralCoord J)

/-- The literal central coordinate subgroup, not an abstract elementary group. -/
def centralImage : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (centralMap J hJ).range

theorem centralMap_injective : Function.Injective (centralMap J hJ) :=
  (OddPrimeSylow.NormalizedOuter.Coverage.root_injective J hJ).comp (centralCoord_injective J)

theorem centralImage_le_root : centralImage J hJ ≤ BorelTorus.projectiveRoot J hJ := by
  rintro _ ⟨b, rfl⟩
  exact ⟨centralCoord J b, rfl⟩

/-- Squares identify the full omega subgroup, including the projective quotient. -/
theorem omega_root : omegaOneAmbient (BorelTorus.projectiveRoot J hJ) =
    centralImage J hJ := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    rintro _ ⟨z, rfl⟩ hz
    have hz' : z ^ 2 = 1 := OddPrimeSylow.NormalizedOuter.Coverage.root_injective J hJ (by
      simpa only [map_pow, map_one] using hz)
    obtain ⟨b, rfl⟩ := (mem_centralCoord_range J z).mpr
      ((square_eq_one_iff J z).mp hz')
    exact ⟨b, rfl⟩
  · rintro _ ⟨b, rfl⟩
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl _ (centralImage_le_root J hJ ⟨b, rfl⟩)
    change hermitianUnipotentPSU J hJ (centralCoord J b) ^ 2 = 1
    rw [← map_pow, (square_eq_one_iff J _).mpr rfl, map_one]

theorem centralImage_elementary : IsElementaryAbelian 2 (centralImage J hJ) := by
  let : IsElementaryAbelian 2 (Multiplicative (fixedField J)) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
        intro b
        rw [pow_two]
        apply Multiplicative.toAdd.injective
        change b.toAdd + b.toAdd = 0
        exact CharTwo.add_self_eq_zero _) }
  exact IsElementaryAbelian.of_surjective (centralMap J hJ).rangeRestrict
    (centralMap J hJ).rangeRestrict_surjective

theorem centralImage_card [Finite E] {q : ℕ}
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Nat.card (centralImage J hJ) = q := by
  change Nat.card (centralMap J hJ).range = q
  rw [← Nat.card_congr (MonoidHom.ofInjective (centralMap_injective J hJ)).toEquiv]
  rw [Nat.card_congr Multiplicative.toAdd]
  exact hfixed

/-- Root elements centralize every member of the omega layer. -/
theorem root_centralizes : BorelTorus.projectiveRoot J hJ ≤
    centralizer (centralImage J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  rintro _ ⟨z, rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨b, rfl⟩
  change hermitianUnipotentPSU J hJ (centralCoord J b) * hermitianUnipotentPSU J hJ z =
    hermitianUnipotentPSU J hJ z * hermitianUnipotentPSU J hJ (centralCoord J b)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · change 0 + z.val.1 = z.val.1 + 0
    simp
  · change (b.toAdd : E) + z.val.2 - 0 * J.conj z.val.1 =
      z.val.2 + (b.toAdd : E) - z.val.1 * J.conj 0
    simp [add_comm]

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.Unitary
