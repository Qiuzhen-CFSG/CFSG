module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.E6Twisting
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The graph-fixed signed chart in the actual twisted E6 cover

The positive root pair at nodes 0 and 5 with parameters t and t^q is fixed
by graph–field twisting. Its additive law makes it a p-element, hence an
element of the literal O^{p′} fixed-point subgroup. It commutes with the
fixed-coefficient roots at 2+ and 3−. Their product is an actual homomorphism
from an elementary group of order q⁴, with its ambient matrix word recorded.

The four folded signed Weyl-word squares also lie in the same residual;
these will supply the involution and the three central-kernel detectors.
No simplicity, group-order, multiplier or F4-identification result is used.
Source: GLS3 §§2.2–2.4 and Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction
open TwistedE6 TwistedE6.FoldedSubsystem
namespace TwistedE6.RankFour
attribute [local instance] Classical.decEq
variable (p : ℕ) [Fact p.Prime] (m : ℕ)

theorem simpleRoot_twist_all (s : Bool) (i : Fin 6) (t : CoefficientField p m) :
    graphFieldTwist p m (simpleRoot (CoefficientField p m) s i t) =
      simpleRoot (CoefficientField p m) s (typeE6DiagramPermutation i) (fieldTwist p m t) := by
  let := Pairing.indexNeg
  cases s
  · change graphFieldTwist p m (rootElement _ (-(simpleIndex i) : typeE6Roots) t) =
      rootElement _ (-(simpleIndex (typeE6DiagramPermutation i)) : typeE6Roots) _
    rw [graphFieldTwist_negative, fieldTwist_apply]
    congr 2
    exact congrArg Subtype.val (typeE6DiagramBasePermutation_numbered i)
  · change graphFieldTwist p m (rootElement _ (simpleIndex i) t) =
      rootElement _ (simpleIndex (typeE6DiagramPermutation i)) _
    rw [graphFieldTwist_positive, fieldTwist_apply]
    congr 1
    exact congrArg Subtype.val (typeE6DiagramBasePermutation_numbered i)

def pairedSplit (t : CoefficientField p m) : rootGeneratedSubgroup p m :=
  simpleRoot (CoefficientField p m) true 0 t * simpleRoot (CoefficientField p m) true 5 (fieldTwist p m t)

theorem pairedSplit_add (t u : CoefficientField p m) :
    pairedSplit p m (t + u) = pairedSplit p m t * pairedSplit p m u := by
  simp only [pairedSplit, map_add, simpleRoot_add]
  exact (simpleRoot_commute (CoefficientField p m) true 0 5 (by decide) (by decide)
    u (fieldTwist p m t)).mul_mul_mul_comm _ _

@[simp] theorem pairedSplit_zero : pairedSplit p m 0 = 1 := by
  simp only [pairedSplit, map_zero, simpleRoot_zero, mul_one]

theorem pairedSplit_fixed (t : CoefficientField p m) :
    graphFieldTwist p m (pairedSplit p m t) = pairedSplit p m t := by
  simp only [pairedSplit, map_mul, simpleRoot_twist_all, fieldTwist_twice]
  exact (simpleRoot_commute (CoefficientField p m) true 5 0 (by decide) (by decide)
    (fieldTwist p m t) t).eq

def pairedFixed (t : CoefficientField p m) : rationalFixedSubgroup p m :=
  ⟨(pairedSplit p m t).val,
    (mem_rationalFixedSubgroup_iff p m _).mpr (pairedSplit_fixed p m t)⟩

theorem pairedFixed_add (t u : CoefficientField p m) :
    pairedFixed p m (t + u) = pairedFixed p m t * pairedFixed p m u :=
  Subtype.ext (congrArg (fun g : rootGeneratedSubgroup p m => g.val) (pairedSplit_add p m t u))

@[simp] theorem pairedFixed_zero : pairedFixed p m 0 = 1 :=
  Subtype.ext (congrArg (fun g : rootGeneratedSubgroup p m => g.val) (pairedSplit_zero p m))

theorem pairedFixed_nsmul (t : CoefficientField p m) (n : ℕ) :
    pairedFixed p m (n • t) = pairedFixed p m t ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, pairedFixed_add, ih, pow_succ]

theorem pairedFixed_pow (t : CoefficientField p m) : pairedFixed p m t ^ p = 1 := by
  rw [← pairedFixed_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, pairedFixed_zero]

def pairedRoot (t : CoefficientField p m) : definingCharacteristicSubgroup p m :=
  ⟨pairedFixed p m t,
    Subgroup.mem_primePowerGenerated_of_pow (n := 1) (by
      simpa only [pow_one] using pairedFixed_pow p m t)⟩

@[simp] theorem pairedRoot_ambient (t : CoefficientField p m) :
    ambientInclusion p m (pairedRoot p m t) = (pairedSplit p m t).val := rfl

def pairedRootHom : Multiplicative (CoefficientField p m) →*
    definingCharacteristicSubgroup p m where
  toFun t := pairedRoot p m t.toAdd
  map_one' := Subtype.ext (pairedFixed_zero p m)
  map_mul' t u := Subtype.ext (pairedFixed_add p m t.toAdd u.toAdd)

theorem commute_of_ambient {a b : definingCharacteristicSubgroup p m}
    (h : Commute (ambientInclusion p m a) (ambientInclusion p m b)) : Commute a b := by
  apply ambientInclusion_injective p m
  simpa only [map_mul] using h.eq

theorem pairedRoot_commute_two (t : CoefficientField p m) (a : FixedField p m) :
    Commute (pairedRoot p m t) (foldedRoot p m true 2 a) := by
  apply commute_of_ambient p m
  simp only [pairedRoot_ambient,foldedRoot_ambient]
  change Commute ((simpleRoot (CoefficientField p m) true 0 t * simpleRoot (CoefficientField p m) true 5 (fieldTwist p m t)).val)
    (simpleRoot (CoefficientField p m) true 2 a).val
  exact ((simpleRoot_commute (CoefficientField p m) true 0 2 (by decide) (by decide) t a).mul_left
    (simpleRoot_commute (CoefficientField p m) true 5 2 (by decide) (by decide) _ a)).map
      (splitCarrier (CoefficientField p m)).subtype

theorem pairedRoot_commute_negative_three (t : CoefficientField p m) (a : FixedField p m) :
    Commute (pairedRoot p m t) (foldedRoot p m false 3 a) := by
  apply commute_of_ambient p m
  simp only [pairedRoot_ambient,foldedRoot_ambient]
  change Commute ((simpleRoot (CoefficientField p m) true 0 t * simpleRoot (CoefficientField p m) true 5 (fieldTwist p m t)).val)
    (simpleRoot (CoefficientField p m) false 3 a).val
  exact ((simpleRoot_opposite_commute (CoefficientField p m) 0 3 (by decide) t a).mul_left
    (simpleRoot_opposite_commute (CoefficientField p m) 5 3 (by decide) _ a)).map
      (splitCarrier (CoefficientField p m)).subtype

theorem two_commute_negative_three (a b : FixedField p m) :
    Commute (foldedRoot p m true 2 a) (foldedRoot p m false 3 b) := by
  apply commute_of_ambient p m
  simp only [foldedRoot_ambient]
  exact (simpleRoot_opposite_commute (CoefficientField p m) 2 3 (by decide) a b).map
    (splitCarrier (CoefficientField p m)).subtype

abbrev Parameters := Multiplicative (CoefficientField p m) ×
  Multiplicative (FixedField p m) × Multiplicative (FixedField p m)

def chartCover : Parameters p m →* definingCharacteristicSubgroup p m :=
  (pairedRootHom p m).noncommCoprod
    ((foldedRootHom p m true 2).noncommCoprod (foldedRootHom p m false 3)
      (fun a b => two_commute_negative_three p m a.toAdd b.toAdd))
    (fun t a => (pairedRoot_commute_two p m t.toAdd a.1.toAdd).mul_right
      (pairedRoot_commute_negative_three p m t.toAdd a.2.toAdd))

@[simp] theorem chartCover_ambient (a : Parameters p m) :
    ambientInclusion p m (chartCover p m a) =
      (simpleRoot (CoefficientField p m) true 0 a.1.toAdd * simpleRoot (CoefficientField p m) true 5 (fieldTwist p m a.1.toAdd) *
        simpleRoot (CoefficientField p m) true 2 a.2.1.toAdd * simpleRoot (CoefficientField p m) false 3 a.2.2.toAdd).val := by
  simp only [chartCover,MonoidHom.noncommCoprod_apply,map_mul,pairedRootHom,foldedRootHom]
  change (simpleRoot (CoefficientField p m) true 0 _ * simpleRoot (CoefficientField p m) true 5 _).val *
    ((simpleRoot (CoefficientField p m) true 2 _).val * (simpleRoot (CoefficientField p m) false 3 _).val) = _
  simp only [Subgroup.coe_mul,mul_assoc]

instance parameters_elementary : IsElementaryAbelian p (Parameters p m) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply Prod.ext
    · change p • a.1.toAdd = 0
      simp [nsmul_eq_mul]
    · apply Prod.ext <;> change p • _ = (0 : FixedField p m) <;> simp [nsmul_eq_mul]

theorem parameters_card : Nat.card (Parameters p m) = parameter p m ^ 4 := by
  change Nat.card (CoefficientField p m × FixedField p m × FixedField p m) = _
  rw [Nat.card_prod,Nat.card_prod,field_card,fixedField_card]
  ring

theorem parameters_card_ge : p^4 ≤ Nat.card (Parameters p m) := by
  rw [parameters_card,parameter]
  exact Nat.pow_le_pow_left (Nat.le_pow (by omega)) 4

def foldedSignActor (i : Fin 4) : definingCharacteristicSubgroup p m :=
  (foldedRoot p m true i 1 * foldedRoot p m false i (-1) * foldedRoot p m true i 1)^2

@[simp] theorem foldedSignActor_ambient (i : Fin 4) :
    ambientInclusion p m (foldedSignActor p m i) =
      ((foldedSimple (CoefficientField p m) true i 1 * foldedSimple (CoefficientField p m) false i (-1) *
        foldedSimple (CoefficientField p m) true i 1)^2).val := by
  simp only [foldedSignActor,map_pow,map_mul,foldedRoot_ambient]
  rfl

end TwistedE6.RankFour
