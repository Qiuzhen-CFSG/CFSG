module

public import Stellmacher.Recognition.PSU3ThreeModel
public import Theory.SpecificGroups.PSL3Two.UnitaryGenerators
public import Theory.SpecificGroups.PSL3Two.ElementOrders
public import Mathlib.Algebra.CharP.Reduced

/-!
# Coordinates and a properness obstruction for PSU₃(3)

The computable field `FiniteField.Nine` identifies with `GaloisField 3 2`.
Under this identification, quadratic conjugation becomes cube Frobenius,
so determinant-one unitary matrices map into ABG's unchanged PSU₃(3).
The projective map is injective on SL₃: in characteristic three a scalar
with cube one is one.

An explicit unitary matrix of order twelve then rules out any surjection
from SL₃(2), whose element orders divide three, four, or seven.
Source: the scalar description of the center of SL and the finite matrix
calculations in the imported modules.
-/

namespace Stellmacher.Recognition.PSU3Three

open Matrix BenderSuzuki.MatrixGroups
open FiniteField

local notation "E" => GaloisField 3 2
local notation "SL9" => SpecialLinearGroup (Fin 3) Nine

/-- Entrywise coefficient transport followed by passage to projective matrices. -/
public noncomputable def projectiveMap : SL9 →* ProjGenLinGroup (Fin 3) E :=
  SpecialLinearGroup.toPGL.comp
    (SpecialLinearGroup.map Nine.equivGaloisField.toRingHom)

public theorem projectiveMap_apply (a : SL9) :
    projectiveMap a = ProjGenLinGroup.mk (SpecialLinearGroup.toGL
      (SpecialLinearGroup.map Nine.equivGaloisField.toRingHom a)) := by rfl

public theorem projectiveMap_injective : Function.Injective projectiveMap := by
  have hc : Subgroup.center (SpecialLinearGroup (Fin 3) E) = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    change a = 1
    obtain ⟨r, hr, hscalar⟩ := SpecialLinearGroup.mem_center_iff.mp ha
    have hr1 : r = 1 := frobenius_inj E 3 (by simpa [frobenius_def] using hr)
    apply Subtype.ext
    simpa [hr1] using hscalar.symm
  have hp : Function.Injective
      (SpecialLinearGroup.toPGL : SpecialLinearGroup (Fin 3) E →* _) := by
    rw [← MonoidHom.ker_eq_bot_iff, SpecialLinearGroup.toPGL_ker, hc]
  apply hp.comp
  intro a b hab
  apply SpecialLinearGroup.ext
  intro i j
  apply Nine.equivGaloisField.injective
  exact congrArg (fun m : SpecialLinearGroup (Fin 3) E => m i j) hab

/-- The concrete unitary equation implies membership in ABG's projective group. -/
public theorem projectiveMap_mem (a : SL9)
    (ha : (a.val.map star).transpose * a.val = 1) :
    projectiveMap a ∈ ABG.PSU3 3 1 (by decide) := by
  refine ⟨SpecialLinearGroup.toGL
    (SpecialLinearGroup.map Nine.equivGaloisField.toRingHom a), ?_, rfl⟩
  apply (HermitianForm.mem_specialSubgroup_iff _ _).mpr
  constructor
  · change (ABG.unitaryForm 3 3 1 (by decide)).conjTranspose
      (a.val.map Nine.equivGaloisField) * 1 *
        a.val.map Nine.equivGaloisField = 1
    simp only [mul_one]
    have hstar : (ABG.unitaryForm 3 3 1 (by decide)).conjTranspose
        (a.val.map Nine.equivGaloisField) =
        ((a.val.map star).transpose).map Nine.equivGaloisField := by
      ext i j
      change iterateFrobeniusEquiv E 3 1 (Nine.equivGaloisField (a j i)) =
        Nine.equivGaloisField (star (a j i))
      rw [Nine.equivGaloisField_star]
      simp [frobenius_def]
    rw [hstar, ← Matrix.map_mul, ha]
    exact Nine.equivGaloisField.toRingHom.mapMatrix.map_one
  · simp

/-- A unitary representation over the computable field gives a homomorphism
to the actual projective group used in recognition. -/
public noncomputable def lift {G : Type*} [Group G] (f : G →* SL9)
    (hf : ∀ g, ((f g).val.map star).transpose * (f g).val = 1) :
    G →* ABG.PSU3 3 1 (by decide) :=
  (projectiveMap.comp f).codRestrict _ (fun g => projectiveMap_mem (f g) (hf g))

@[simp] public theorem lift_coe {G : Type*} [Group G] (f : G →* SL9)
    (hf : ∀ g, ((f g).val.map star).transpose * (f g).val = 1) (g : G) :
    (lift f hf g : ProjGenLinGroup (Fin 3) E) = projectiveMap (f g) := by rfl

public theorem lift_injective {G : Type*} [Group G] (f : G →* SL9)
    (hf : ∀ g, ((f g).val.map star).transpose * (f g).val = 1)
    (hi : Function.Injective f) : Function.Injective (lift f hf) := by
  intro a b hab
  exact hi (projectiveMap_injective (congrArg Subtype.val hab))

/-- Every homomorphism from SL₃(2) has proper image in the concrete PSU₃(3). -/
public theorem not_surjective (f : SpecialLinearGroup (Fin 3) (ZMod 2) →*
    ABG.PSU3 3 1 (by decide)) : ¬ Function.Surjective f := by
  intro hf
  let w : ABG.PSU3 3 1 (by decide) :=
    ⟨projectiveMap PSL3Two.unitaryTwelve,
      projectiveMap_mem _ PSL3Two.unitaryTwelve_unitary⟩
  obtain ⟨a, ha⟩ := hf w
  have hp (n : ℕ) (hn : a ^ n = 1) : PSL3Two.unitaryTwelve ^ n = 1 := by
    apply projectiveMap_injective
    have hw : w ^ n = 1 := by rw [← ha, ← map_pow, hn, map_one]
    simpa only [w, Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using
      congrArg Subtype.val hw
  rcases PSL3Two.pow_three_or_four_or_seven a with h | h | h
  · exact PSL3Two.unitaryTwelve_powers_ne_one.1 (hp 3 h)
  · exact PSL3Two.unitaryTwelve_powers_ne_one.2.1 (hp 4 h)
  · exact PSL3Two.unitaryTwelve_powers_ne_one.2.2 (hp 7 h)

end Stellmacher.Recognition.PSU3Three
