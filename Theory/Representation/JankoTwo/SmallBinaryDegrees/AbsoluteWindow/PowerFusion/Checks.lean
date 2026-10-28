module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Tables

/-!
# Checked power fusion for the twenty-one Hall--Janko representatives

The kernel checks the base table and its five successive squaring identities,
then checks `c * r⁸ = r³² * c` at all one hundred points. Both `c` and `r` are
certified normal forms in the literal carrier, so
injectivity of its inclusion gives conjugacy inside that carrier. Conjugacy
invariance then supplies power fusion for every element in any of these classes.
Exhaustive coverage of the classes is not asserted here.

Source: the ATLAS `J2G1-p100B0` tables and the candidate words retained in the
adjacent `source/` directory; see `Data` for attribution and conventions.
-/

namespace Sporadic.LeechRelated.J2.PowerFusionCertificate

open GeneratorPair.SecondOrbitCertificate

set_option maxRecDepth 10000 in
private theorem base_check : ∀ i : Fin 21, ∀ x : Fin 100,
    normalForm (representativeIndex i) x = PowerTables.action i 0 x := by
  apply allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem square_check : ∀ i : Fin 21, ∀ k : Fin 5, ∀ x : Fin 100,
    PowerTables.action i k.castSucc (PowerTables.action i k.castSucc x) =
      PowerTables.action i k.succ x := by
  apply allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fusion_check : ∀ i : Fin 21, ∀ x : Fin 100,
    normalForm (conjugatorIndex i) (PowerTables.action i 3 x) =
    PowerTables.action i 5 (normalForm (conjugatorIndex i) x) := by
  apply allFin
  decide +kernel

private theorem power_action (i : Fin 21) (k : ℕ) : ∀ (hk : k < 6) (x : Fin 100),
    (normalForm (representativeIndex i) ^ (2 ^ k)) x = PowerTables.action i ⟨k, hk⟩ x := by
  induction k with
  | zero =>
    intro hk x
    simpa only [pow_zero, pow_one, Fin.mk_zero] using base_check i x
  | succ k ih =>
    intro hk x
    rw [pow_succ, pow_mul, pow_two, Equiv.Perm.mul_apply,
      ih (by omega), ih (by omega)]
    exact square_check i ⟨k, by omega⟩ x

/-- The explicit carrier conjugator satisfies the required intertwining identity. -/
public theorem conjugator_mul_eighth (i : Fin 21) :
    conjugator i * representative i ^ 8 = representative i ^ 32 * conjugator i := by
  apply inclusion_injective
  simp only [map_mul, map_pow, conjugator, representative, inclusion_element]
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply]
  have h8 := power_action i 3 (by decide)
  have h32 := power_action i 5 (by decide)
  simp only [show (2 : ℕ) ^ 3 = 8 by decide,
    show (⟨3, by decide⟩ : Fin 6) = 3 from rfl] at h8
  simp only [show (2 : ℕ) ^ 5 = 32 by decide,
    show (⟨5, by decide⟩ : Fin 6) = 5 from rfl] at h32
  rw [h8, h32]
  exact fusion_check i x

/-- Power fusion holds for every one of the twenty-one concrete representatives. -/
public theorem representative_powerFusion (i : Fin 21) :
    IsConj (representative i ^ 8) (representative i ^ 32) := by
  apply isConj_iff.mpr
  exact ⟨conjugator i, mul_inv_eq_iff_eq_mul.mpr (conjugator_mul_eighth i)⟩

/-- The checked fusion identity transports along actual conjugacy in the carrier. -/
public theorem powerFusion_of_isConj_representative {g : Carrier} (i : Fin 21)
    (h : IsConj (representative i) g) : IsConj (g ^ 8) (g ^ 32) :=
  ((h.pow 8).symm.trans (representative_powerFusion i)).trans (h.pow 32)

end Sporadic.LeechRelated.J2.PowerFusionCertificate
