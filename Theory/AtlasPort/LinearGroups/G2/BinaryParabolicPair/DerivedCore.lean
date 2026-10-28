module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair
public import Theory.GroupTheory.SpecificGroups.QuaternionCyclicModel

/-!
# The parity-zero core as Q₈ ◦ C₄

The right quaternion factor and the central left generator give an explicit
isomorphism onto the coordinate subgroup c=d. It intertwines the displayed
cubic and the central quotient. Identification with the derived parabolic
two-core is proved in the restriction module.
Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988.
-/

@[expose] public section

namespace Atlas.G2.BinaryParabolicPair
open Atlas.G2.Explicit BinaryCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The parity-zero part of the five-root coordinates. The sign-character
identification is supplied separately. -/
def derivedCoordinates : Subgroup Coordinates where
  carrier := {x | x.c = x.d}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    change x.c+y.c=x.d+y.d
    rw [show x.c=x.d from hx, show y.c=y.d from hy]
  inv_mem' := by
    intro x hx
    change -x.c = -x.d
    rw [show x.c=x.d from hx]

instance : DecidablePred (· ∈ derivedCoordinates) := fun x =>
  inferInstanceAs (Decidable (x.c = x.d))

/-- Exchange the right quaternion generators so that the cubic has the
canonical orientation used in `QuaternionCyclic.Model`. -/
def derivedQuaternionEmbedding : QuaternionGroup 2 →* Coordinates where
  toFun := quaternionMap rightJ rightI
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

/-- The central C₄ generator is `leftI`; the quaternion factor is the right one. -/
def quaternionCyclicEmbedding : QuaternionCyclic.Model →* Coordinates where
  toFun x := derivedQuaternionEmbedding x.quaternion * (if x.odd then leftI else 1)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem quaternionCyclicEmbedding_injective : Function.Injective quaternionCyclicEmbedding := by
  decide +kernel

theorem quaternionCyclicEmbedding_range : quaternionCyclicEmbedding.range = derivedCoordinates := by
  ext x
  change (∃ q, quaternionCyclicEmbedding q = x) ↔ x.c=x.d
  revert x
  decide +kernel

theorem quaternionCyclicEmbedding_cubic (x : QuaternionCyclic.Model) :
    cubicConjugate (quaternionCyclicEmbedding x) = quaternionCyclicEmbedding (QuaternionCyclic.cubic x) := by
  revert x
  decide +kernel

/-- The actual embedded order-sixteen subgroup. -/
def derivedCore : Subgroup (Model (ZMod 2)) := derivedCoordinates.map embedding

noncomputable def derivedCoreEquiv : QuaternionCyclic.Model ≃* derivedCore :=
  (MonoidHom.ofInjective quaternionCyclicEmbedding_injective).trans
    ((MulEquiv.subgroupCongr quaternionCyclicEmbedding_range).trans
      (derivedCoordinates.equivMapOfInjective embedding embedding_injective))

theorem derivedCoreEquiv_apply (x : QuaternionCyclic.Model) :
    (derivedCoreEquiv x : Model (ZMod 2)) = embedding (quaternionCyclicEmbedding x) := rfl

theorem card_derivedCore : Nat.card derivedCore = 16 :=
  (Nat.card_congr derivedCoreEquiv.toEquiv).symm.trans QuaternionCyclic.card_model

theorem derivedCore_le_core : derivedCore ≤ core := Subgroup.map_le_range _ _

theorem cubic_derivedCore (x : QuaternionCyclic.Model) :
    cubicActor * (derivedCoreEquiv x : Model (ZMod 2)) * cubicActor⁻¹ =
      (derivedCoreEquiv (QuaternionCyclic.cubic x) : Model (ZMod 2)) := by
  simp only [derivedCoreEquiv_apply, cubic_conjugate, quaternionCyclicEmbedding_cubic]

/-- The specified central quotient map, transported by the explicit isomorphism. -/
noncomputable def derivedCentralQuotient : derivedCore →* QuaternionCyclic.CentralQuotient :=
  QuaternionCyclic.centralQuotient.comp derivedCoreEquiv.symm.toMonoidHom

theorem derivedCentralQuotient_apply (x : QuaternionCyclic.Model) :
    derivedCentralQuotient (derivedCoreEquiv x) = QuaternionCyclic.centralQuotient x := by
  simp [derivedCentralQuotient]

theorem derivedCentralQuotient_surjective : Function.Surjective derivedCentralQuotient :=
  QuaternionCyclic.centralQuotient_surjective.comp derivedCoreEquiv.symm.surjective

theorem derivedCentralQuotient_ker :
    derivedCentralQuotient.ker = Subgroup.center derivedCore := by
  ext g
  change derivedCoreEquiv.symm g ∈ QuaternionCyclic.centralQuotient.ker ↔
    g ∈ Subgroup.center derivedCore
  rw [QuaternionCyclic.centralQuotient_ker, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro hg h
    apply derivedCoreEquiv.symm.injective
    simpa only [map_mul] using hg (derivedCoreEquiv.symm h)
  · intro hg q
    apply derivedCoreEquiv.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hg (derivedCoreEquiv q)

theorem derivedCentralQuotient_cubic (x : QuaternionCyclic.Model) :
    derivedCentralQuotient (derivedCoreEquiv (QuaternionCyclic.cubic x)) =
      QuaternionCyclic.cubicQuotient (derivedCentralQuotient (derivedCoreEquiv x)) := by
  simp only [derivedCentralQuotient_apply, QuaternionCyclic.cubic_centralQuotient]

end Atlas.G2.BinaryParabolicPair
