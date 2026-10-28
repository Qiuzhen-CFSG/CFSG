module
public import Theory.Representation.Triality.RestrictedWeights.ConcreteRootRecovery.Common
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RootPairsSource
/-!
# The three-arm regular SL2 map for triality

The positive and negative roots on distinct arms commute. Transvection
induction extends this to the complete rank-one groups. Multiplying the three
regular maps, with Frobenius exponents zero, n and 2n, therefore defines an
algebraic-group morphism. Its upper, lower and diagonal formulas keep the
literal root order and the left-coroot convention of finite weight recovery.
Source: GLS3 2.8.2; Steinberg 13.3(a).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open scoped MatrixGroups
namespace Triality.RestrictedWeights.Concrete.RootCharts
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

def signedRoot (i : Fin 4) (negative : Bool) : RootIndex :=
  if negative then negativeRoot (simpleRoot i) else simpleRoot i

def armIndex (i : Fin 3) : Fin 4 := ![0,2,3] i

private theorem arm_pairing_zero (i j : Fin 3) (hij : i ≠ j) (a b : Bool) :
    (typeDRootPairing 2).pairing (signedRoot (armIndex i) a)
      (signedRoot (armIndex j) b) = 0 := by
  rw [typeDRootPairing_pairing]
  change (∑ p : Fin 4, typeDRootVector 4 (signedRoot (armIndex j) b) p *
    typeDRootVector 4 (signedRoot (armIndex i) a) p) = 0
  simp only [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals cases a <;> cases b <;>
    norm_num [signedRoot,armIndex,simpleRoot,typeDSimpleRootIndex,
      negativeRoot,typeDRootVector,basisVector,Pi.single_apply,Fin.ext_iff]


private theorem arm_nonopposite (i j : Fin 3) (hij : i ≠ j) (a b : Bool) :
    signedRoot (armIndex j) b ≠ negativeRoot (signedRoot (armIndex i) a) := by
  intro h
  have hz := arm_pairing_zero i j hij a b
  have he := congrArg ((typeDRootPairing 2).root) h
  rw [Pinning.root_negativeRoot] at he
  have hh := congrArg (fun v => (typeDRootPairing 2).toLinearMap v
    ((typeDRootPairing 2).coroot (signedRoot (armIndex i) a))) he
  simp only [map_neg,LinearMap.neg_apply,RootPairing.root_coroot_eq_pairing,
    (typeDRootPairing 2).pairing_same,arm_pairing_zero j i hij.symm b a] at hh
  norm_num at hh

private theorem arm_no_sum (i j : Fin 3) (hij : i ≠ j) (a b : Bool) :
    ¬ ∃ t : RootIndex, (typeDRootPairing 2).root t =
      (typeDRootPairing 2).root (signedRoot (armIndex i) a) +
      (typeDRootPairing 2).root (signedRoot (armIndex j) b) := by
  rintro ⟨c,hs⟩
  let r := signedRoot (armIndex i) a
  let s := signedRoot (armIndex j) b
  have symm (x y : RootIndex) : (typeDRootPairing 2).pairing x y =
      (typeDRootPairing 2).pairing y x := by
    rw [typeDRootPairing_pairing,typeDRootPairing_pairing,dot_comm]
  have h₁ := RootPairing.pairing_eq_add_of_root_eq_add (l := r) hs
  have h₂ := RootPairing.pairing_eq_add_of_root_eq_add (l := s) hs
  have h₃ := RootPairing.pairing_eq_add_of_root_eq_add (l := c) hs
  rw [(typeDRootPairing 2).pairing_same] at h₁ h₂ h₃
  rw [symm s r] at h₁
  rw [symm r c,symm s c] at h₃
  have hz := arm_pairing_zero i j hij a b
  change (typeDRootPairing 2).pairing r s = 0 at hz
  linarith

theorem armRoot_commute (i j : Fin 3) (hij : i ≠ j) (a b : Bool) (s t : k) :
    Commute (rootPoint k (signedRoot (armIndex i) a) s)
      (rootPoint k (signedRoot (armIndex j) b) t) :=
  RootPairs.rootPoint_commute k _ _ (arm_nonopposite i j hij a b)
    (arm_no_sum i j hij a b) s t

omit [CharP k 2] in
theorem point_induction (P : Variety.Point (slVariety k 2) → Prop)
    (hp : ∀ t, P (standardSL2UpperMorphism.onPoints (kPlusPoint t)))
    (hm : ∀ t, P (standardSL2LowerMorphism.onPoints (kPlusPoint t)))
    (hprod : ∀ x y, P x → P y → P (x*y)) (x : Variety.Point (slVariety k 2)) : P x := by
  obtain ⟨A,rfl⟩ := (slPointEquiv 2).symm.surjective x
  apply Matrix.SL2.transvection_induction (fun A => P ((slPointEquiv 2).symm A)) ?_ ?_ A
  · intro i j hij c
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hp c
    · exact hm c
    · exact (hij rfl).elim
  · intro A B hA hB
    exact hprod _ _ hA hB
def twistedSimpleMap (i : Fin 4) (n : ℕ) : Morphism (slVariety k 2) (groupVariety k) :=
  (regularFrobeniusLift k n).comp (simpleMap k i)

theorem twistedSimpleMap_upper (i : Fin 4) (n : ℕ) (t : k) :
    (twistedSimpleMap k i n).onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) =
      rootPoint k (simpleRoot i) (t^(2^n)) := by
  change (regularFrobeniusLift k n).onPoints ((simpleMap k i).onPoints _) = _
  rw [simpleMap_upper,regularFrobeniusLift_onPoints,GraphField.frobenius_rootPoint]

theorem twistedSimpleMap_lower (i : Fin 4) (n : ℕ) (t : k) :
    (twistedSimpleMap k i n).onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)) =
      rootPoint k (negativeRoot (simpleRoot i)) (t^(2^n)) := by
  change (regularFrobeniusLift k n).onPoints ((simpleMap k i).onPoints _) = _
  rw [simpleMap_lower,regularFrobeniusLift_onPoints,GraphField.frobenius_rootPoint]

theorem twistedArms_commute (i j : Fin 3) (hij : i ≠ j) (m n : ℕ)
    (x y : Variety.Point (slVariety k 2)) :
    Commute ((twistedSimpleMap k (armIndex i) m).onPoints x)
      ((twistedSimpleMap k (armIndex j) n).onPoints y) := by
  let f := (twistedSimpleMap k (armIndex i) m).onPoints
  let g := (twistedSimpleMap k (armIndex j) n).onPoints
  change Commute (f x) (g y)
  refine point_induction k (fun x => Commute (f x) (g y)) ?_ ?_ ?_ x
  · intro s
    refine point_induction k (fun y => Commute (f _) (g y)) ?_ ?_ ?_ y
    · intro t
      change Commute ((twistedSimpleMap k (armIndex i) m).onPoints _)
        ((twistedSimpleMap k (armIndex j) n).onPoints _)
      rw [twistedSimpleMap_upper,twistedSimpleMap_upper]
      exact armRoot_commute k i j hij false false _ _
    · intro t
      change Commute ((twistedSimpleMap k (armIndex i) m).onPoints _)
        ((twistedSimpleMap k (armIndex j) n).onPoints _)
      rw [twistedSimpleMap_upper,twistedSimpleMap_lower]
      exact armRoot_commute k i j hij false true _ _
    · intro a b ha hb
      simpa only [map_mul] using ha.mul_right hb
  · intro s
    refine point_induction k (fun y => Commute (f _) (g y)) ?_ ?_ ?_ y
    · intro t
      change Commute ((twistedSimpleMap k (armIndex i) m).onPoints _)
        ((twistedSimpleMap k (armIndex j) n).onPoints _)
      rw [twistedSimpleMap_lower,twistedSimpleMap_upper]
      exact armRoot_commute k i j hij true false _ _
    · intro t
      change Commute ((twistedSimpleMap k (armIndex i) m).onPoints _)
        ((twistedSimpleMap k (armIndex j) n).onPoints _)
      rw [twistedSimpleMap_lower,twistedSimpleMap_lower]
      exact armRoot_commute k i j hij true true _ _
    · intro a b ha hb
      simpa only [map_mul] using ha.mul_right hb
  · intro a b ha hb
    simpa only [map_mul] using ha.mul_left hb

def commutingProduct {A B : Variety k} [AlgebraicGroup A] [AlgebraicGroup B]
    (f g : Morphism A B) (h : ∀ x y, Commute (f.onPoints x) (g.onPoints y)) : Morphism A B where
  toVariety := (mulMorphism B).comp (f.toVariety.pair g.toVariety)
  map_one := by
    change f.onPoints 1 * g.onPoints 1 = 1
    rw [map_one,map_one,one_mul]
  map_mul := by
    intro x y
    change f.onPoints (x*y) * g.onPoints (x*y) =
      (f.onPoints x * g.onPoints x) * (f.onPoints y * g.onPoints y)
    rw [map_mul,map_mul]
    exact (h y x).mul_mul_mul_comm _ _

omit [IsAlgClosed k] [CharP k 2] in
@[simp] theorem commutingProduct_apply {A B : Variety k} [AlgebraicGroup A] [AlgebraicGroup B]
    (f g : Morphism A B) (h : ∀ x y, Commute (f.onPoints x) (g.onPoints y))
    (x : Variety.Point A) : (commutingProduct k f g h).onPoints x = f.onPoints x*g.onPoints x := rfl

def armsMap (n : ℕ) : Morphism (slVariety k 2) (groupVariety k) :=
  commutingProduct k
    (commutingProduct k (twistedSimpleMap k 0 0) (twistedSimpleMap k 2 n)
      (twistedArms_commute k 0 1 (by decide) 0 n))
    (twistedSimpleMap k 3 (2*n)) (by
      intro x y
      exact (twistedArms_commute k 0 2 (by decide) 0 (2*n) x y).mul_left
        (twistedArms_commute k 1 2 (by decide) n (2*n) x y))

theorem armsMap_upper (n : ℕ) (t : k) :
    (armsMap k n).onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) =
      rootPoint k (simpleRoot 0) t * rootPoint k (simpleRoot 2) (t^(2^n)) *
      rootPoint k (simpleRoot 3) (t^((2^n)^2)) := by
  change (twistedSimpleMap k 0 0).onPoints _ * (twistedSimpleMap k 2 n).onPoints _ *
    (twistedSimpleMap k 3 (2*n)).onPoints _ = _
  rw [twistedSimpleMap_upper,twistedSimpleMap_upper,twistedSimpleMap_upper]
  simp only [pow_zero,pow_one]
  rw [Nat.mul_comm 2 n,pow_mul]


theorem armsMap_lower (n : ℕ) (t : k) :
    (armsMap k n).onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)) =
      rootPoint k (negativeRoot (simpleRoot 0)) t *
      rootPoint k (negativeRoot (simpleRoot 2)) (t^(2^n)) *
      rootPoint k (negativeRoot (simpleRoot 3)) (t^((2^n)^2)) := by
  change (twistedSimpleMap k 0 0).onPoints _ * (twistedSimpleMap k 2 n).onPoints _ *
    (twistedSimpleMap k 3 (2*n)).onPoints _ = _
  rw [twistedSimpleMap_lower,twistedSimpleMap_lower,twistedSimpleMap_lower]
  simp only [pow_zero,pow_one]
  rw [Nat.mul_comm 2 n,pow_mul]

attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup
open Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
local instance armsGeometryTorus (hu : IsUniversalVersion (groupVariety k)) :
    AlgebraicGroup (finiteGeometry k hu).torus.carrierVariety :=
  ClosedSubgroup.carrierAlgebraicGroup _

theorem twistedSimpleMap_diagonal (hu : IsUniversalVersion (groupVariety k))
    (i : Fin 4) (n : ℕ) (t : Variety.Point (KMult k)) :
    (twistedSimpleMap k i n).onPoints (standardSL2DiagonalMorphism.onPoints t) =
      (finiteGeometry k hu).torus.includePoint
        (((finiteGeometry k hu).leftSimpleCoroot i).onPoints (t^(2^n))) := by
  change (regularFrobeniusLift k n).onPoints ((simpleMap k i).onPoints _) = _
  rw [simpleMap_diagonal k hu,Geometry.leftSimpleCoroot_apply,Geometry.leftSimpleCoroot_apply]
  change (regularFrobeniusLift k n).onPoints
      ((CorootTorus.closedSubgroup k).includePoint
        (((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i))).onPoints t⁻¹)) = _
  rw [GraphField.frobenius_rootCocharacter,inv_pow]
  rfl

theorem armsMap_diagonal (hu : IsUniversalVersion (groupVariety k))
    (n : ℕ) (t : Variety.Point (KMult k)) :
    (armsMap k n).onPoints (standardSL2DiagonalMorphism.onPoints t) =
      (finiteGeometry k hu).torus.includePoint
        (RootRecovery.RootOrbit.arms.torusPoint (finiteGeometry k hu) n t) := by
  change (twistedSimpleMap k 0 0).onPoints _ * (twistedSimpleMap k 2 n).onPoints _ *
    (twistedSimpleMap k 3 (2*n)).onPoints _ = _
  rw [twistedSimpleMap_diagonal k hu,twistedSimpleMap_diagonal k hu,twistedSimpleMap_diagonal k hu]
  simp only [RootRecovery.RootOrbit.torusPoint,pow_zero,pow_one]
  change _ = (finiteGeometry k hu).torus.inclusion.onPoints (_*_*_)
  rw [map_mul,map_mul]
  rw [Nat.mul_comm 2 n,pow_mul]
  rfl
end Triality.RestrictedWeights.Concrete.RootCharts
