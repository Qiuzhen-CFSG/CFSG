module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.Normalizer.Words

/-!
# Finite descent of the literal marked-torus normalizers

Conjugate the three proved twisted-fixed Weyl words by the exact Lang
solution already used by `ExceptionalTorus.modelMap`. The established
rational-descent equivalence puts them in the actual Ree carrier. A single
homomorphism transports the cycle, transposition and inversion identities,
so every action retains the original marked torus and its scalar center.

Sources: GLS3 Example 2.6.3 and Table 4.7.3A; Steinberg rational descent.
-/

@[expose] public section
open Theory.AlgebraicGroup
namespace ReeF4.CentralCovers.OddPrimary.Three.Descent.Normalizer
open ExceptionalTorus ReeF4.CentralCovers.OddPrimary.Cyclotomic
noncomputable section

/-- The fixed subgroup for the exact twisted Lang representative used by the marked torus. -/
def twistedFixed (m : ℕ) : Subgroup (AlgebraicPoints (Closure m)) :=
  algebraicFixed (((MulAut.conj (normalizer m)).toMonoidHom).comp
    (algebraicReeTwist m).onPoints)

theorem conjugated_mem (m : ℕ) (hm : 1 ≤ m) (x : twistedFixed m) :
    (MulAut.conj (conjugator (F := Closure m) m hm)⁻¹) x.val ∈
      algebraicFixed (algebraicReeTwist m).onPoints := by
  have hx : normalizer (F := Closure m) m * (algebraicReeTwist m).onPoints x.val *
      (normalizer m)⁻¹ = x.val := x.property
  simpa only [MulAut.conj_apply, inv_inv] using
    conjugated_fixed (algebraicReeTwist m).onPoints (normalizer m)
      (conjugator m hm) x.val (conjugator_equation m hm) hx

/-- Conjugation by the existing Lang solution followed by literal rational descent. -/
def descentHom (m : ℕ) (hm : 1 ≤ m) : twistedFixed m →* Model m :=
  (fixedModelEquiv (coefficientEmbedding m)).toMonoidHom.comp
    ((((MulAut.conj (conjugator (F := Closure m) m hm)⁻¹).toMonoidHom).comp
      (twistedFixed m).subtype).codRestrict
      (algebraicFixed (algebraicReeTwist m).onPoints) (conjugated_mem m hm))

 def fixedCycle (m : ℕ) : twistedFixed m := ⟨cycleElement, cycle_twisted_fixed m⟩
 def fixedSwap (m : ℕ) : twistedFixed m := ⟨swapElement, swap_twisted_fixed m⟩
 def fixedInverter (m : ℕ) : twistedFixed m := ⟨inverterElement, inverter_twisted_fixed m⟩

 def twistedTorus (m : ℕ) : Parameters m →* twistedFixed m :=
  (algebraicMap m (quadraticEmbedding m)).codRestrict _
    (algebraicMap_twisted_fixed m (quadraticEmbedding m))

 theorem descent_torus (m : ℕ) (hm : 1 ≤ m) (a : Parameters m) :
    descentHom m hm (twistedTorus m a) = modelMap m hm a := rfl

 def modelCycle (m : ℕ) (hm : 1 ≤ m) : Model m := descentHom m hm (fixedCycle m)
 def modelSwap (m : ℕ) (hm : 1 ≤ m) : Model m := descentHom m hm (fixedSwap m)
 def modelInverter (m : ℕ) (hm : 1 ≤ m) : Model m := descentHom m hm (fixedInverter m)

 theorem modelCycle_cube (m : ℕ) (hm : 1 ≤ m) : (modelCycle m hm)^3 = 1 := by
  have h : (fixedCycle m)^3 = 1 := by
    apply Subtype.ext
    exact cycle_cube (F := Closure m)
  simpa only [modelCycle, map_pow, map_one] using congrArg (descentHom m hm) h

 theorem modelCycle_torus (m : ℕ) (hm : 1 ≤ m) (a : Parameters m) :
    modelCycle m hm * modelMap m hm a * (modelCycle m hm)⁻¹ =
      modelMap m hm ((a.1*a.2)⁻¹,a.1) := by
  have h : fixedCycle m * twistedTorus m a * (fixedCycle m)⁻¹ =
      twistedTorus m ((a.1*a.2)⁻¹,a.1) := Subtype.ext (cycle_algebraicMap m _ a)
  simpa only [modelCycle, map_mul, map_inv, descent_torus] using congrArg (descentHom m hm) h

 theorem modelSwap_torus (m : ℕ) (hm : 1 ≤ m) (a : Parameters m) :
    modelSwap m hm * modelMap m hm a * (modelSwap m hm)⁻¹ = modelMap m hm (a.2,a.1) := by
  have h : fixedSwap m * twistedTorus m a * (fixedSwap m)⁻¹ =
      twistedTorus m (a.2,a.1) := Subtype.ext (swap_algebraicMap m _ a)
  simpa only [modelSwap, map_mul, map_inv, descent_torus] using congrArg (descentHom m hm) h

 theorem modelInverter_torus (m : ℕ) (hm : 1 ≤ m) (a : Parameters m) :
    modelInverter m hm * modelMap m hm a * (modelInverter m hm)⁻¹ = (modelMap m hm a)⁻¹ := by
  have h : fixedInverter m * twistedTorus m a * (fixedInverter m)⁻¹ =
      (twistedTorus m a)⁻¹ := Subtype.ext (inverter_algebraicMap m _ a)
  simpa only [modelInverter, map_mul, map_inv, descent_torus] using congrArg (descentHom m hm) h

 theorem modelInverter_cycle (m : ℕ) (hm : 1 ≤ m) :
    Commute (modelInverter m hm) (modelCycle m hm) := by
  have h : Commute (fixedInverter m) (fixedCycle m) := by
    apply Subtype.ext
    exact (inverter_commutes (F := Closure m) cycleWord).eq
  exact h.map (descentHom m hm)

end
end ReeF4.CentralCovers.OddPrimary.Three.Descent.Normalizer
