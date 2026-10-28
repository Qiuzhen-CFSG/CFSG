module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.LinearDerived
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.V2Commutators

/-!
# Lifting (10.5) to the derived linear radical

Carter's five-root support and the literal V₂ coordinates identify the
shifted-root parameter of a cross commutator. The first derived-subgroup
bound removes the three linear factors. Their own subgroup abelianization
then removes the two Omega parameters and reverses the remaining pair.
Thus each barred shifted-root parameter has a perpendicular partner whose
product actually lies in [U_s₁,U_s₁], including q=2.

LinearLarge applies this graph to the actual Cartan displacement; the
binary diagonal case is kept separate. No additive label is asserted to
be a field automorphism, and no linear quotient is assumed.
Source: Fong--Seitz II (1974), (10.5) and the following discussion, p.222.
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

private def graphCoordinateHom : (V2Section Q split c).numerator →*
    Multiplicative (Representation.SuzukiNatural.W m) :=
  ((V2Coordinates Q split c).toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom).comp
    (QuotientGroup.mk' (V2Section Q split c).denominator)

private theorem graphCoordinate_T2 (v : (V2Section Q split c).numerator)
    (hv : (v : X ⧸ Q.D) ∈ T2 Q split) :
    V2Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v)) = 0 := by
  have hv' : (QuotientGroup.mk v : (V2Section Q split c).Carrier) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hv
  rw [hv']
  exact map_zero (V2Coordinates Q split c).toLinearEquiv

/-- Reading the second axis of an actual interior product ignores precisely
its other four factors. This is used to lift (10.5) before forming V₁. -/
theorem V2_interior_coordinates
    (a : positiveRoot Q split (.inl 2)) (b : positiveRoot Q split (.inr 1))
    (d : positiveRoot Q split (.inl 3)) (y z : CoefficientField m)
    (f : positiveRoot Q split (.inl 1))
    (v : (V2Section Q split (pinnedInput Q split c)).numerator)
    (hv : (v : X ⧸ Q.D) = (a : X ⧸ Q.D)*b*d*
      positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (y,z)*f) :
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk v)) =
      ![reflectedLinearCoordinate Q split (pinnedInput Q split c) f,
        V2MiddleFieldLabel Q split c y,0,0] := by
  let c' := pinnedInput Q split c
  let a' : (V2Section Q split c').numerator := inclusion (positiveRoot_le_remainder Q split c' (.inl 2) 1 (by decide)) a
  let b' : (V2Section Q split c').numerator := inclusion (positiveRoot_le_remainder Q split c' (.inr 1) 1 (by decide)) b
  let d' : (V2Section Q split c').numerator := inclusion (positiveRoot_le_remainder Q split c' (.inl 3) 1 (by decide)) d
  let e' : (V2Section Q split c').numerator := inclusion (positiveRoot_le_remainder Q split c' (.inr 3) 1 (by decide))
    (positiveChart Q split c' (RingEquiv.refl _) (.inr 3) (y,z))
  let f' : (V2Section Q split c').numerator := inclusion (positiveRoot_le_remainder Q split c' (.inl 1) 1 (by decide)) f
  have he : v = a'*b'*d'*e'*f' := Subtype.ext hv
  have ha := graphCoordinate_T2 Q split c' a' ((show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left) (nextLinear_le_phi Q split c' a.property))
  have hb := graphCoordinate_T2 Q split c' b' (show (b' : X ⧸ Q.D) ∈ T2 Q split from (show perpendicularSuzuki Q split ≤ T2 Q split from le_sup_right) b.property)
  have hd := graphCoordinate_T2 Q split c' d' ((show phi (simpleRemainder Q split 1) ≤ T2 Q split from le_sup_left) (perpendicularLinear_le_phi Q split c' d.property))
  have hh := congrArg Multiplicative.toAdd (congrArg (graphCoordinateHom Q split c') he)
  simp only [map_mul] at hh
  change V2Coordinates Q split c' (Additive.ofMul (QuotientGroup.mk v)) =
    V2Coordinates Q split c' (Additive.ofMul (QuotientGroup.mk a')) +
    V2Coordinates Q split c' (Additive.ofMul (QuotientGroup.mk b')) +
    V2Coordinates Q split c' (Additive.ofMul (QuotientGroup.mk d')) +
    V2Coordinates Q split c' (Additive.ofMul (V2ShiftedSuzuki Q split c'
      (positiveChart Q split c' (RingEquiv.refl _) (.inr 3) (y,z)))) +
    V2Coordinates Q split c' (Additive.ofMul (V2ReflectedLinear Q split c' f)) at hh
  rw [ha,hb,hd,pinnedV2_shifted_parameter,V2Coordinates_reflectedLinear] at hh
  exact hh.trans (by ext i; fin_cases i <;> simp <;> rfl)

private theorem zero_first_mem_omega (i : Fin 4) (b : CoefficientField m) :
    positivePoint Q split c (RingEquiv.refl _) (.inr i) (0,b) ∈
      omegaOneAmbient (positiveRoot Q split (.inr i)) := by
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl _
    (positiveChart Q split c (RingEquiv.refl _) (.inr i) (0,b)).property
  change positivePoint Q split c (RingEquiv.refl _) (.inr i) (0,b) ^ 2 = 1
  rw [pow_two,positivePoint_quartet_mul]
  simpa only [zero_add,map_zero,zero_mul,add_zero,CharTwo.add_self_eq_zero] using
    positivePoint_quartet_zero Q split c (RingEquiv.refl _) i

private def rootAbelianization (i : Fin 4) : positiveRoot Q split (.inr i) →*
    Abelianization (simpleRemainder Q split 0) :=
  (Abelianization.of).comp (inclusion (positiveRoot_le_remainder Q split c (.inr i) 0 (by simp)))

private theorem rootAbelianization_parameter (i : Fin 4)
    (hi : omegaOneAmbient (positiveRoot Q split (.inr i)) ≤ linearDerived Q split)
    (a b : CoefficientField m) :
    rootAbelianization Q split c i (positiveChart Q split c (RingEquiv.refl _) (.inr i) (a,b)) =
    rootAbelianization Q split c i (positiveChart Q split c (RingEquiv.refl _) (.inr i) (a,0)) := by
  have h0 : rootAbelianization Q split c i
      (positiveChart Q split c (RingEquiv.refl _) (.inr i) (0,b)) = 1 :=
    (linearDerived_abelianization_iff Q split _).mpr (hi (zero_first_mem_omega Q split c i b))
  have he : positiveChart Q split c (RingEquiv.refl _) (.inr i) (a,b) =
      positiveChart Q split c (RingEquiv.refl _) (.inr i) (a,0)*
      positiveChart Q split c (RingEquiv.refl _) (.inr i) (0,b) := by
    apply Subtype.ext
    change positivePoint Q split c (RingEquiv.refl _) (.inr i) (a,b) =
      positivePoint Q split c (RingEquiv.refl _) (.inr i) (a,0) *
      positivePoint Q split c (RingEquiv.refl _) (.inr i) (0,b)
    exact (by simpa only [add_zero,zero_add,mul_zero] using
      (positivePoint_quartet_mul Q split c (RingEquiv.refl _) i a 0 0 b).symm)
  rw [he,map_mul,h0,mul_one]

/-- The remaining two barred-root factors in the first p.222 argument have
an actual lift in the derived radical, for every field parameter and q=2. -/
theorem exists_linearDerived_graph (α : CoefficientField m) :
    ∃ β : CoefficientField m,
      positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 3) (α,0)*
      positivePoint Q split (pinnedInput Q split c) (RingEquiv.refl _) (.inr 1) (β,0) ∈
        linearDerived Q split := by
  let c' := pinnedInput Q split c
  obtain ⟨a,b,y,hcover⟩ := V2_cross_commutator_covers Q split c (RingEquiv.refl _) α 0
  let u := suzukiChart Q split c' (a,b)
  let v := inclusion (positiveRoot_le_remainder Q split c' (.inr 2) 1 (by decide))
    (positiveChart Q split c' (RingEquiv.refl _) (.inr 2) (y,0))
  let k := V2RightCommutator Q split c' u v
  have hk : (k : X ⧸ Q.D) ∈ ⁅simpleRoot Q split 1,positiveRoot Q split (.inr 2)⁆ := by
    rw [commutator_comm]
    have hh := commutator_mem_commutator
      ((positiveRoot Q split (.inr 2)).inv_mem
        (positiveChart Q split c' (RingEquiv.refl _) (.inr 2) (y,0)).property)
      ((simpleRoot Q split 1).inv_mem u.property)
    change ⁅(v : X ⧸ Q.D)⁻¹,(u : X ⧸ Q.D)⁻¹⁆ ∈ _ at hh
    rw [show (k : X ⧸ Q.D) = _ from V2RightCommutator_val Q split c' u v]
    simpa only [commutatorElement_def,inv_inv] using hh
  have hkD : (k : X ⧸ Q.D) ∈ linearDerived Q split := by
    apply commutator_mono _ _ hk
    · simpa only [positiveRoot,positiveKind,positiveWord,Matrix.cons_val,
        Fin.isValue,Matrix.head_cons,rootAt_one] using
        positiveRoot_le_remainder Q split c' (.inr 0) 0 (by decide)
    · exact positiveRoot_le_remainder Q split c' (.inr 2) 0 (by decide)
  obtain ⟨⟨r,s,t,w,z,pu⟩,hprod⟩ := V2_cross_commutator_support Q split c' k hk
  have hp : (k : X ⧸ Q.D) = (r : X ⧸ Q.D)*s*t*w*z := by
    simpa only [V2InteriorFactors,rootProduct,mul_one,mul_assoc] using hprod.symm
  obtain ⟨⟨δ,ε⟩,hw⟩ := (positiveChart Q split c' (RingEquiv.refl _) (.inr 3)).surjective w
  obtain ⟨⟨β,γ⟩,hs⟩ := (positiveChart Q split c' (RingEquiv.refl _) (.inr 1)).surjective s
  have hcoords := V2_interior_coordinates Q split c r s t δ ε z k
    (by rw [hp,←hw]; rfl)
  have hz : positiveChart Q split c' (RingEquiv.refl _) (.inl 1) 0 = 1 :=
    Subtype.ext (positivePoint_pair_zero Q split c' (RingEquiv.refl _) 1)
  change QuotientGroup.mk k = V2ShiftedSuzuki Q split c'
    (positiveChart Q split c' (RingEquiv.refl _) (.inr 3) (α,0))*
    V2ReflectedLinear Q split c' (positiveChart Q split c' (RingEquiv.refl _) (.inl 1) 0) at hcover
  rw [hz,map_one,mul_one] at hcover
  have hc := congrArg (fun z : (V2Section Q split c').Carrier =>
    V2Coordinates Q split c' (Additive.ofMul z)) hcover
  rw [hcoords,pinnedV2_shifted_parameter] at hc
  have hδα : δ = α := (V2MiddleFieldLabel Q split c).injective (congrFun hc 1)
  subst δ
  have hsD : (s : X ⧸ Q.D)*w ∈ linearDerived Q split :=
    linearDerived_interior_strip Q split c' r s t w z (hp ▸ hkD)
  let s' := inclusion (positiveRoot_le_remainder Q split c' (.inr 1) 0 (by decide)) s
  let w' := inclusion (positiveRoot_le_remainder Q split c' (.inr 3) 0 (by decide)) w
  have hab := (linearDerived_abelianization_iff Q split (s'*w')).mpr hsD
  change rootAbelianization Q split c' 1 s * rootAbelianization Q split c' 3 w = 1 at hab
  rw [←hs,←hw,rootAbelianization_parameter Q split c' 1
    (perpendicularOmega_le_linearDerived Q split c'),rootAbelianization_parameter Q split c' 3
    (shiftedOmega_le_linearDerived Q split c')] at hab
  refine ⟨β,?_⟩
  apply (linearDerived_abelianization_iff Q split
    (inclusion (positiveRoot_le_remainder Q split c' (.inr 3) 0 (by decide))
        (positiveChart Q split c' (RingEquiv.refl _) (.inr 3) (α,0)) *
      inclusion (positiveRoot_le_remainder Q split c' (.inr 1) 0 (by decide))
        (positiveChart Q split c' (RingEquiv.refl _) (.inr 1) (β,0)))).mp
  rw [map_mul,mul_comm]
  exact hab

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
