module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearGraph
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearTorus
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.InvariantRoots

/-!
# The positive-parameter derived bound and binary diagonal generator

For q>2, choose a nonidentity matrix torus element and the graph point
whose second natural coordinate is one. The torus fixes its perpendicular
partner and displaces its shifted factor. The displacement belongs to the
literal derived radical and has nonzero barred-root coordinate. The proved
Cartan-invariant root-intersection theorem then puts the entire shifted
Suzuki root in that radical. Reflection gives the perpendicular root, so
all five factors generating T₁ lie there.

At q=2 the torus argument is unavailable. In the source noncontainment
branch, the graph partner at parameter one cannot be zero, hence is one.
This proves the actual diagonal generator in the corrected native chart;
changing its second parameters by Omega does not change the derived bound.
The derived upper bound and the characteristic inverse-image argument are
still required to construct V₁. OriginalLinearDerived supplies the literal
original-endpoint applications of the proved bounds.
Source: Fong--Seitz II (1974), printed p.222, the argument before (10.6).
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups ReeF4
open scoped Pointwise IsMulCommutative commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
/-- For q>2 a nontrivial actual Cartan displacement removes the perpendicular
partner in the p.222 graph. The binary case is deliberately not asserted. -/
theorem shiftedSuzuki_le_linearDerived_of_pos (hm : 0 < m) :
    positiveRoot Q split (.inr 3) ≤ linearDerived Q split := by
  let c' := pinnedInput Q split c
  let : Nontrivial (CoefficientField m)ˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units,GaloisField.card 2 (2*m+1) (by omega)]
    have hq : 2^2 ≤ 2^(2*m+1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega)
  obtain ⟨a,ha⟩ := exists_ne (1 : (CoefficientField m)ˣ)
  have ha1 : (a : CoefficientField m)^(2^m) ≠ 1 := by
    intro he
    apply ha
    apply Units.ext
    apply iterateFrobenius_inj (CoefficientField m) 2 m
    simpa only [iterateFrobenius_def,Units.val_one,one_pow] using he
  let α := (V2MiddleFieldLabel Q split c).symm 1
  obtain ⟨β,hβ⟩ := exists_linearDerived_graph Q split c α
  let u := positiveChart Q split c' (RingEquiv.refl _) (.inr 3) (α,0)
  let v := positiveChart Q split c' (RingEquiv.refl _) (.inr 1) (β,0)
  let h := pinnedSuzukiTorus Q split c (matrixTorusParameter a)
  have hH : (h : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N := pinnedSuzukiTorus_mem_cartan Q split c _
  have hN := rootAt_torus_normalizes Q split 1 (Q.simple 0*Q.simple 1) hH
  let u' : positiveRoot Q split (.inr 3) :=
    ⟨(h : X ⧸ Q.D)*u*(h : X ⧸ Q.D)⁻¹,(mem_normalizer_iff.mp hN u).mp u.property⟩
  let z : positiveRoot Q split (.inr 3) := u'*u⁻¹
  have hvfix : (h : X ⧸ Q.D)*v*(h : X ⧸ Q.D)⁻¹ = v := by
    have hh := mem_centralizer_iff.mp (pinnedSuzukiTorus_centralizes_perpendicular Q split c
      (matrixTorusParameter a)) v v.property
    rw [←hh,mul_inv_cancel_right]
  have hzD : (z : X ⧸ Q.D) ∈ linearDerived Q split := by
    have hh := (linearDerived Q split).mul_mem
      ((mem_normalizer_iff.mp (linearDerived_cartan_normalizes Q split c hH)
        ((u : X ⧸ Q.D)*v)).mp hβ) ((linearDerived Q split).inv_mem hβ)
    have he : (h : X ⧸ Q.D)*((u : X ⧸ Q.D)*v)*(h : X ⧸ Q.D)⁻¹ *
        ((u : X ⧸ Q.D)*v)⁻¹ = (z : X ⧸ Q.D) := by
      calc
        _ = ((h : X ⧸ Q.D)*u*(h : X ⧸ Q.D)⁻¹)*
          ((h : X ⧸ Q.D)*v*(h : X ⧸ Q.D)⁻¹)*((v : X ⧸ Q.D)⁻¹*(u : X ⧸ Q.D)⁻¹) := by group
        _ = (z : X ⧸ Q.D) := by rw [hvfix]; dsimp [z,u']; group
    exact he ▸ hh
  let uV : (V2Section Q split c').numerator := inclusion (positiveRoot_le_remainder Q split c' (.inr 3) 1 (by decide)) u
  have hu : V2Coordinates Q split c' (Additive.ofMul (V2ShiftedSuzuki Q split c' u)) 1 = 1 := by
    have hc := congrFun (pinnedV2_shifted_parameter Q split c α 0) 1
    change _ = V2MiddleFieldLabel Q split c ((V2MiddleFieldLabel Q split c).symm 1) at hc
    exact hc.trans ((V2MiddleFieldLabel Q split c).apply_symm_apply 1)
  have hu' : V2Coordinates Q split c' (Additive.ofMul (V2ShiftedSuzuki Q split c' u')) 1 =
      (a : CoefficientField m)^(2^m) := by
    have he : (V2Section Q split c').numeratorAction h uV =
        inclusion (positiveRoot_le_remainder Q split c' (.inr 3) 1 (by decide)) u' := rfl
    have hh := pinnedSuzukiTorus_V2_second Q split c a uV
    rw [he] at hh
    change V2Coordinates Q split c' (Additive.ofMul (V2ShiftedSuzuki Q split c' u')) 1 =
      (a : CoefficientField m)^(2^m) *
        V2Coordinates Q split c' (Additive.ofMul (V2ShiftedSuzuki Q split c' u)) 1 at hh
    exact hh.trans (by rw [hu,mul_one])
  have hz : V2Coordinates Q split c' (Additive.ofMul (V2ShiftedSuzuki Q split c' z)) 1 =
      (a : CoefficientField m)^(2^m)-1 := by
    change V2Coordinates Q split c' (Additive.ofMul (V2ShiftedSuzuki Q split c' (u'*u⁻¹))) 1 = _
    rw [map_mul,map_inv]
    change (V2Coordinates Q split c').toLinearEquiv
      (Additive.ofMul (V2ShiftedSuzuki Q split c' u') + -
        Additive.ofMul (V2ShiftedSuzuki Q split c' u)) 1 = _
    rw [map_add,map_neg]
    change V2Coordinates Q split c' (Additive.ofMul (V2ShiftedSuzuki Q split c' u')) 1 +
      -(V2Coordinates Q split c' (Additive.ofMul (V2ShiftedSuzuki Q split c' u)) 1) = _
    rw [hu',hu,←sub_eq_add_neg]
  by_contra hn
  have hΩ := suzuki_rootAt_intersection_le_omega_of_not_le Q split 1 m c'.suzuki c'.suzukiBorel
    (Q.simple 0*Q.simple 1) (linearDerived Q split) (linearDerived_cartan_normalizes Q split c) hn
  have hz0 : V2ShiftedSuzuki Q split c' z = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left)
      (shiftedOmega_le_phi Q split c' (hΩ ⟨hzD,z.property⟩))
  rw [hz0] at hz
  have hzero : V2Coordinates Q split c' (Additive.ofMul (1 : (V2Section Q split c').Carrier)) = 0 :=
    map_zero (V2Coordinates Q split c').toLinearEquiv
  rw [hzero] at hz
  exact ha1 (sub_eq_zero.mp hz.symm)

include c in
/-- All five source factors of T₁ lie in the derived radical for q>2. -/
theorem T1_le_linearDerived_of_pos (hm : 0 < m) : T1 Q split ≤ linearDerived Q split := by
  have hs := shiftedSuzuki_le_linearDerived_of_pos Q split c hm
  exact sup_le (sup_le (sup_le (sup_le (nextLinear_le_linearDerived Q split c)
    (perpendicular_le_linearDerived_of_shifted Q split c hs))
      (perpendicularLinear_le_linearDerived Q split c)) hs)
        (reflectedLinear_le_linearDerived Q split c)


/-- In the binary noncontainment branch, the partner at parameter one is
one. Thus the printed diagonal generator really belongs to the derived
radical; characteristic-section identification still needs the upper bound. -/
theorem binary_linearDerived_diagonal (c₀ : ReeSixHData Q split n 0)
    (hn : ¬ positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    positivePoint Q split (pinnedInput Q split c₀) (RingEquiv.refl _) (.inr 3) (1,0)*
      positivePoint Q split (pinnedInput Q split c₀) (RingEquiv.refl _) (.inr 1) (1,0) ∈
        linearDerived Q split := by
  let c' := pinnedInput Q split c₀
  obtain ⟨β,hβ⟩ := exists_linearDerived_graph Q split c₀ 1
  have hb : β ≠ 0 := by
    intro hb
    rw [hb,positivePoint_quartet_zero,mul_one] at hβ
    have hΩ := suzuki_rootAt_intersection_le_omega_of_not_le Q split 1 0 c'.suzuki c'.suzukiBorel
      (Q.simple 0*Q.simple 1) (linearDerived Q split) (linearDerived_cartan_normalizes Q split c₀) hn
    let u := positiveChart Q split c' (RingEquiv.refl _) (.inr 3) (1,0)
    have hu : V2ShiftedSuzuki Q split c' u = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact (show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left)
        (shiftedOmega_le_phi Q split c' (hΩ ⟨hβ,u.property⟩))
    have hc := congrFun (pinnedV2_shifted_parameter Q split c₀ 1 0) 1
    change V2Coordinates Q split c' (Additive.ofMul (V2ShiftedSuzuki Q split c' u)) 1 =
      V2MiddleFieldLabel Q split c₀ 1 at hc
    rw [hu] at hc
    have hz : V2Coordinates Q split c' (Additive.ofMul (1 : (V2Section Q split c').Carrier)) = 0 :=
      map_zero (V2Coordinates Q split c').toLinearEquiv
    rw [hz] at hc
    exact one_ne_zero ((V2MiddleFieldLabel Q split c₀).injective
      (hc.symm.trans (map_zero (V2MiddleFieldLabel Q split c₀)).symm))
  have hcard : Fintype.card (CoefficientField 0) = 2 := by
    rw [←Nat.card_eq_fintype_card]
    exact GaloisField.card 2 1 (by decide)
  have hb1 : β = 1 := by
    have hp := FiniteField.pow_card_sub_one_eq_one β hb
    simpa only [hcard,show 2-1 = (1:ℕ) from rfl,pow_one] using hp
  exact hb1 ▸ hβ


/-- The diagonal in the literal order printed in the binary p.222 case.
The subgroup abelianization justifies reversing the general graph order. -/
theorem binary_linearDerived_source_diagonal (c₀ : ReeSixHData Q split n 0)
    (hn : ¬ positiveRoot Q split (.inr 3) ≤ linearDerived Q split) :
    positivePoint Q split (pinnedInput Q split c₀) (RingEquiv.refl _) (.inr 1) (1,0)*
      positivePoint Q split (pinnedInput Q split c₀) (RingEquiv.refl _) (.inr 3) (1,0) ∈
        linearDerived Q split := by
  let c' := pinnedInput Q split c₀
  let u := inclusion (positiveRoot_le_remainder Q split c' (.inr 1) 0 (by decide))
    (positiveChart Q split c' (RingEquiv.refl _) (.inr 1) (1,0))
  let v := inclusion (positiveRoot_le_remainder Q split c' (.inr 3) 0 (by decide))
    (positiveChart Q split c' (RingEquiv.refl _) (.inr 3) (1,0))
  have hh := (linearDerived_abelianization_iff Q split (v*u)).mpr
    (binary_linearDerived_diagonal Q split c₀ hn)
  apply (linearDerived_abelianization_iff Q split (u*v)).mp
  rw [map_mul,mul_comm,←map_mul]
  exact hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
