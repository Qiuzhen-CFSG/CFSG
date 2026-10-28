module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.LinearDenominator
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.InvariantRoots
/-!
# Squares in the linear radical's abelianization

The literal denominator X₁ has elementary image in U_s₁/[U_s₁,U_s₁].
Indeed, all three interior linear roots are derived, and the squares of
both interior Suzuki roots lie in the proved derived seed. Endpoint Omega
subgroups consist of involutions. This proves the square-kernel inclusion
for every parameter without assuming any natural-module coordinates.

The intrinsic square kernel is characteristic and is exactly the inverse
image of Omega₁ of the actual abelianization. LinearAbelianization uses
the binary derived upper bound to identify it with X₁ at q=2.
Source: Fong--Seitz II (1974), printed p.222, before (10.6).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
theorem positiveSuzuki_square_eq_one_iff_omega (j : Fin 4)
    (x : positiveRoot Q split (.inr j)) :
    x^2 = 1 ↔ (x : X ⧸ Q.D) ∈ omegaOneAmbient (positiveRoot Q split (.inr j)) := by
  have h := suzuki_rootAt_square_eq_iff_omega Q split 1 m c.suzuki c.suzukiBorel
    (positiveWord (Q.simple 0) (Q.simple 1) (.inr j))
    1 x (one_mem _) x.property
  have hx : x^2 = 1 ↔ (x : X ⧸ Q.D)^2 = 1 := Subtype.ext_iff
  exact hx.trans (by simpa only [one_pow,inv_one,one_mul,eq_comm,positiveRoot,positiveKind] using h)

include c in
theorem positiveSuzuki_square_mem_omega (j : Fin 4)
    (x : positiveRoot Q split (.inr j)) :
    (x : X ⧸ Q.D)^2 ∈ omegaOneAmbient (positiveRoot Q split (.inr j)) := by
  let : Fact (IsPGroup 2 (positiveRoot Q split (.inr j))) :=
    ⟨split.isTwo.to_le (positiveRoot_le_unipotent Q split c.rotation_eight _)⟩
  rw [←positiveSuzuki_phi_eq_omega Q split c j]
  exact mem_map_of_mem _ (pth_power_mem_frattini_of_isPGroup (p := 2) x)

/-- The intrinsic inverse image of the involutions in the actual abelianization. -/
def linearSquareKernel : Subgroup (simpleRemainder Q split 0) :=
  ((powMonoidHom 2).comp (Abelianization.of : simpleRemainder Q split 0 →*
    Abelianization (simpleRemainder Q split 0))).ker

theorem mem_linearSquareKernel (v : simpleRemainder Q split 0) :
    v ∈ linearSquareKernel Q split ↔ (v : X ⧸ Q.D)^2 ∈ linearDerived Q split := by
  change (Abelianization.of v)^2 = 1 ↔ _
  rw [←map_pow]
  exact linearDerived_abelianization_iff Q split (v^2)

theorem linearSquareKernel_eq_omega_preimage : linearSquareKernel Q split =
    (omega₁ (Abelianization (simpleRemainder Q split 0)) (p := 2)).comap Abelianization.of := by
  ext v
  change (Abelianization.of v)^2 = 1 ↔ Abelianization.of v ∈ omega₁ _
  constructor
  · intro h
    apply Subgroup.subset_closure
    change (Abelianization.of v)^(2^1) = 1
    simpa only [pow_one] using h
  · intro h
    let : IsElementaryAbelian 2 (omega₁ (Abelianization (simpleRemainder Q split 0)) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative _
    exact elemPow_eq_one_of_isElementaryAbelian _ h

theorem linearSquareKernel_characteristic : (linearSquareKernel Q split).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro f v hv
  rw [mem_comap,mem_linearSquareKernel,←coe_pow]
  have hh : v^2 ∈ commutator (simpleRemainder Q split 0) := by
    rw [←Abelianization.ker_of]
    exact hv
  have hf := characteristic_iff_le_comap.mp
    (inferInstance : (commutator (simpleRemainder Q split 0)).Characteristic) f hh
  rw [←map_pow]
  apply (linearDerived_abelianization_iff Q split _).mp
  change f (v^2) ∈ (Abelianization.of :
    simpleRemainder Q split 0 →* Abelianization (simpleRemainder Q split 0)).ker
  rwa [Abelianization.ker_of]

include c in
/-- Each interior Suzuki square is in the proved derived seed. Therefore
all of X₁ has involutory image in the actual abelianization, for every q. -/
theorem X1_le_linearSquareKernel : X1 Q split ≤
    (linearSquareKernel Q split).map (simpleRemainder Q split 0).subtype := by
  let K := (linearSquareKernel Q split).map (simpleRemainder Q split 0).subtype
  have hD : linearDerived Q split ≤ K := by
    intro x hx
    have hR : x ∈ simpleRemainder Q split 0 := X1_le_linearRemainder Q split c (linearDerived_le_X1 Q split c hx)
    exact ⟨⟨x,hR⟩,(mem_linearSquareKernel Q split _).mpr ((linearDerived Q split).pow_mem hx 2),rfl⟩
  have hs (j : Fin 4) (hj : omegaOneAmbient (positiveRoot Q split (.inr j)) ≤ linearDerived Q split) :
      positiveRoot Q split (.inr j) ≤ K := by
    intro x hx
    exact ⟨⟨x,positiveRoot_le_remainder Q split c (.inr j) 0 (by simp) hx⟩,
      (mem_linearSquareKernel Q split _).mpr (hj (positiveSuzuki_square_mem_omega Q split c j ⟨x,hx⟩)),rfl⟩
  have hT : T1 Q split ≤ K :=
    sup_le (sup_le (sup_le (sup_le ((nextLinear_le_linearDerived Q split c).trans hD)
      (hs 1 (perpendicularOmega_le_linearDerived Q split c)))
        ((perpendicularLinear_le_linearDerived Q split c).trans hD))
          (hs 3 (shiftedOmega_le_linearDerived Q split c)))
            ((reflectedLinear_le_linearDerived Q split c).trans hD)
  have hΩ (j : Fin 4) : omegaOneAmbient (positiveRoot Q split (.inr j)) ≤ K := by
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hx2
    exact ⟨⟨x,positiveRoot_le_remainder Q split c (.inr j) 0 (by simp) hx⟩,
      (mem_linearSquareKernel Q split _).mpr (hx2 ▸ one_mem _),rfl⟩
  exact sup_le (sup_le (hΩ 2) hT) (hΩ 0)

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
