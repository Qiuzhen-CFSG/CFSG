module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLastLinear

/-!
# The simple Suzuki--linear commutator in source coordinates

The right commutator lies in both simple remainders. Carter's ordered
coordinates remove its two endpoint roots, and the synchronized natural
Suzuki quotient fixes the three exterior coefficients of the resulting
six-factor word. All equalities are in the actual source quotient and retain
the triangular native Suzuki chart, including its binary correction.

Source: Fong--Seitz II (1974), printed pp.228--229, (10.27)--(10.30).
The interior coefficients require the subsequent rank-one identities.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition WeylPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)

private theorem simple_suzuki (a b : CoefficientField m) :
    S 0 a b = (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) := by
  rw [synchronizedPositivePoint_quartet_word]
  simp only [positiveWord,Matrix.cons_val_zero,map_one,inv_one,one_mul,mul_one]

private theorem simple_linear (a : CoefficientField m) :
    L 0 a = (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D) := by
  rw [synchronizedPositivePoint_pair_word]
  simp only [positiveWord,Matrix.cons_val_zero,map_one,inv_one,one_mul,mul_one]

/-- The literal right commutator of the simple linear and Suzuki roots. -/
def synchronizedSuzukiLinear (a b y : CoefficientField m) :
    (V2Section Q split (pinnedInput Q split c)).numerator :=
  V2RightCommutator Q split (pinnedInput Q split c)
    (suzukiChart Q split (pinnedInput Q split c) (a,b))
    (inclusion (simpleLinear_le_suzukiRemainder Q split (pinnedInput Q split c))
      (synchronizedLinearChart Q split c (.ofAdd y)))

theorem synchronizedSuzukiLinear_val (a b y : CoefficientField m) :
    (synchronizedSuzukiLinear Q split c a b y : X ⧸ Q.D) =
      (L 0 y)⁻¹ * (S 0 a b)⁻¹ * L 0 y * S 0 a b := by
  rw [simple_linear,simple_suzuki]
  exact V2RightCommutator_val Q split (pinnedInput Q split c) _ _

private theorem raw_support (a b y : CoefficientField m) :
    ∃ d r s e t v h w f : CoefficientField m,
      (synchronizedSuzukiLinear Q split c a b y : X ⧸ Q.D) =
        S 2 d r * L 2 s * S 1 e t * L 3 v * S 3 h w * L 1 f := by
  let k := synchronizedSuzukiLinear Q split c a b y
  have hN : simpleRoot Q split 0 ≤ normalizer (simpleRemainder Q split 0 : Set (X ⧸ Q.D)) :=
    (simpleRoot_le Q split 0).trans (split.U_le.trans
      ((Q.tits.B_le_standardParabolic _).trans
        (remainder_parabolic_normalizes Q split 0
          (remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow
            c.linearBorel (CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource.linear_normalizer_index c.linearSylow)))))
  have hk0 : (k : X ⧸ Q.D) ∈ simpleRemainder Q split 0 := by
    apply le_normalizer_iff_commutator_le_left.mp hN
    have hu : S 0 a b ∈ simpleRemainder Q split 0 :=
      positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)
        (synchronizedPositiveChart Q split c (.inr 0) (a,b)).property
    have hv : L 0 y ∈ simpleRoot Q split 0 := by
      rw [simple_linear]
      exact (synchronizedLinearChart Q split c (.ofAdd y)).property
    rw [commutator_comm]
    have h := commutator_mem_commutator
      ((simpleRoot Q split 0).inv_mem hv) ((simpleRemainder Q split 0).inv_mem hu)
    simpa only [k,synchronizedSuzukiLinear_val,commutatorElement_def,inv_inv] using h
  have hp : (k : X ⧸ Q.D) ∈ Set.range (rootProduct (linearFactors Q split)) := by
    rw [linearProduct_range Q split c]
    exact hk0
  obtain ⟨⟨d,s,e,v,h,f,z,u⟩,hp⟩ := hp
  let tail : X ⧸ Q.D := (d : X ⧸ Q.D)*s*e*v*h*f
  have ht : tail ∈ simpleRemainder Q split 1 := by
    apply (simpleRemainder Q split 1).mul_mem
    · apply (simpleRemainder Q split 1).mul_mem
      · apply (simpleRemainder Q split 1).mul_mem
        · apply (simpleRemainder Q split 1).mul_mem
          · apply (simpleRemainder Q split 1).mul_mem
            · exact positiveRoot_le_remainder Q split c (.inr 2) 1 (by decide) d.property
            · exact positiveRoot_le_remainder Q split c (.inl 2) 1 (by decide) s.property
          · exact positiveRoot_le_remainder Q split c (.inr 1) 1 (by decide) e.property
        · exact positiveRoot_le_remainder Q split c (.inl 3) 1 (by decide) v.property
      · exact positiveRoot_le_remainder Q split c (.inr 3) 1 (by decide) h.property
    · exact positiveRoot_le_remainder Q split c (.inl 1) 1 (by decide) f.property
  have hp' : tail * (z : X ⧸ Q.D) = k := by
    simpa only [tail,linearFactors,rootProduct,mul_one,mul_assoc] using hp
  have hz : (z : X ⧸ Q.D) = 1 := by
    apply disjoint_def.mp (simpleRoot_disjoint_remainder Q split 1)
      (by simpa [positiveRoot,positiveKind,positiveWord] using z.property)
    have hh := (simpleRemainder Q split 1).mul_mem
      ((simpleRemainder Q split 1).inv_mem ht) k.property
    rwa [←hp',inv_mul_cancel_left] at hh
  rw [hz,mul_one] at hp'
  obtain ⟨⟨d,r⟩,rfl⟩ := (synchronizedPositiveChart Q split c (.inr 2)).surjective d
  obtain ⟨s,rfl⟩ := (synchronizedPositiveChart Q split c (.inl 2)).surjective s
  obtain ⟨⟨e,t⟩,rfl⟩ := (synchronizedPositiveChart Q split c (.inr 1)).surjective e
  obtain ⟨v,rfl⟩ := (synchronizedPositiveChart Q split c (.inl 3)).surjective v
  obtain ⟨⟨h,w⟩,rfl⟩ := (synchronizedPositiveChart Q split c (.inr 3)).surjective h
  obtain ⟨f,rfl⟩ := (synchronizedPositiveChart Q split c (.inl 1)).surjective f
  exact ⟨d,r,s,e,t,v,h,w,f,hp'.symm⟩

private def coordinateHom : (V2Section Q split (pinnedInput Q split c)).numerator →*
    Multiplicative (Representation.SuzukiNatural.W m) :=
  ((V2Coordinates Q split (pinnedInput Q split c)).toLinearEquiv.toAddEquiv.toMultiplicative.toMonoidHom).comp
    (QuotientGroup.mk' (V2Section Q split (pinnedInput Q split c)).denominator)

private def rootPoint (i : PositiveTables.Root) (hi : i ≠ .inr 0)
    (a : PositiveTables.Parameter m i) :
    (V2Section Q split (pinnedInput Q split c)).numerator :=
  inclusion (positiveRoot_le_remainder Q split (pinnedInput Q split c) i 1 hi)
    (synchronizedPositiveChart Q split c i a)

theorem synchronizedSuzukiLinear_coordinates (a b y : CoefficientField m) :
    V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk (synchronizedSuzukiLinear Q split c a b y))) =
      ![((a^2*titsEnd m a+a*b+titsEnd m b)*y)*pinnedLinearV2Label Q split c 1,
        ((b+a*titsEnd m a)*y)*pinnedLinearV2Label Q split c 1,
        (a*y)*pinnedLinearV2Label Q split c 1,0] := by
  have h := V2RightCommutator_coordinates Q split (pinnedInput Q split c) a b
    (inclusion (simpleLinear_le_suzukiRemainder Q split (pinnedInput Q split c))
      (synchronizedLinearChart Q split c (.ofAdd y)))
  dsimp only at h
  rw [show V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk
        (inclusion (simpleLinear_le_suzukiRemainder Q split (pinnedInput Q split c))
          (synchronizedLinearChart Q split c (.ofAdd y))))) =
      ![0,0,0,y*pinnedLinearV2Label Q split c 1] from synchronizedLinearChart_V2 Q split c y] at h
  change V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk (V2RightCommutator Q split (pinnedInput Q split c)
        (suzukiChart Q split (pinnedInput Q split c) (a,b))
        (inclusion (simpleLinear_le_suzukiRemainder Q split (pinnedInput Q split c))
          (synchronizedLinearChart Q split c (.ofAdd y)))))) = _
  rw [h]
  ext i
  fin_cases i <;> simp <;> ring

/-- The first natural quotient determines all three exterior coefficients
of the six-factor mixed commutator in the synchronized source chart. -/
theorem synchronizedSuzukiLinear_outer_coefficients (a b y : CoefficientField m) :
    ∃ r s e t v w : CoefficientField m,
      (L 0 y)⁻¹ * (S 0 a b)⁻¹ * L 0 y * S 0 a b =
        S 2 (a*y) r * L 2 s * S 1 e t * L 3 v *
          S 3 ((b+a*titsEnd m a)*y) w *
            L 1 ((a^2*titsEnd m a+a*b+titsEnd m b)*y) := by
  obtain ⟨d,r,s,e,t,v,h,w,f,hprod⟩ := raw_support Q split c a b y
  let k := synchronizedSuzukiLinear Q split c a b y
  let d' := rootPoint Q split c (.inr 2) (by decide) (d,r)
  let tail := rootPoint Q split c (.inl 2) (by decide) s *
    rootPoint Q split c (.inr 1) (by decide) (e,t) *
    rootPoint Q split c (.inl 3) (by decide) v *
    rootPoint Q split c (.inr 3) (by decide) (h,w) *
    rootPoint Q split c (.inl 1) (by decide) f
  have he : k = d' * tail := by
    apply Subtype.ext
    change (k : X ⧸ Q.D) = S 2 d r * (L 2 s * S 1 e t * L 3 v * S 3 h w * L 1 f)
    simpa only [k,mul_assoc] using hprod
  have ht := V2_interior_coordinates Q split c
    (synchronizedPositiveChart Q split c (.inl 2) s)
    (synchronizedPositiveChart Q split c (.inr 1) (e,t))
    (synchronizedPositiveChart Q split c (.inl 3) v) h w
    (synchronizedPositiveChart Q split c (.inl 1) f) tail (by rfl)
  rw [synchronized_reflected_coordinate,V2MiddleFieldLabel_scalar] at ht
  have hc := congrArg Multiplicative.toAdd (congrArg (coordinateHom Q split c) he)
  simp only [map_mul] at hc
  change V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk k)) =
    V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk d')) +
      V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk tail)) at hc
  rw [ht] at hc
  have hd := synchronized_opposite_coordinates Q split c d r
  change V2Coordinates Q split (pinnedInput Q split c) (Additive.ofMul (QuotientGroup.mk d')) = _ at hd
  rw [hd,synchronizedSuzukiLinear_coordinates] at hc
  have hd' : d = a*y := by
    apply mul_right_cancel₀ (pinnedLinearV2Label_one_ne_zero Q split c)
    simpa only [Pi.add_apply,Matrix.cons_val,Fin.isValue,Matrix.head_cons,add_zero,zero_add]
      using (congrFun hc 2).symm
  have hh' : h = (b+a*titsEnd m a)*y := by
    apply mul_right_cancel₀ (pinnedLinearV2Label_one_ne_zero Q split c)
    simpa only [Pi.add_apply,Matrix.cons_val,Fin.isValue,Matrix.head_cons,add_zero,zero_add]
      using (congrFun hc 1).symm
  have hf' : f = (a^2*titsEnd m a+a*b+titsEnd m b)*y := by
    apply mul_right_cancel₀ (pinnedLinearV2Label_one_ne_zero Q split c)
    simpa only [Pi.add_apply,Matrix.cons_val,Fin.isValue,Matrix.head_cons,add_zero,zero_add]
      using (congrFun hc 0).symm
  subst d; subst h; subst f
  exact ⟨r,s,e,t,v,w,(synchronizedSuzukiLinear_val Q split c a b y).symm.trans hprod⟩

private theorem seed_pair_inv (i : Fin 4) (a : CoefficientField m) :
    (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_pair_mul]
  simp only [CharTwo.add_self_eq_zero, synchronizedPositivePoint_pair_zero]

private theorem seed_quartet_inv (i : Fin 4) (a b : CoefficientField m) :
    (S i a b)⁻¹ = S i a (b + titsEnd m a * a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_quartet_mul]
  have h : b + (b + titsEnd m a * a) + titsEnd m a * a = 0 := by
    rw [← add_assoc b b, CharTwo.add_self_eq_zero, zero_add,
      CharTwo.add_self_eq_zero]
  simp only [h, CharTwo.add_self_eq_zero, synchronizedPositivePoint_quartet_zero]

/-- Inverse orientation for arbitrary parameters, retaining the native
Suzuki inverse corrections in every quartet factor. -/
theorem synchronizedSuzukiLinear_inverse_support (a b y : CoefficientField m) :
    ∃ r s e t v w : CoefficientField m,
      (S 0 a b)⁻¹ * (L 0 y)⁻¹ * S 0 a b * L 0 y =
        L 1 ((a^2*titsEnd m a+a*b+titsEnd m b)*y) *
          S 3 ((b+a*titsEnd m a)*y) (w + titsEnd m ((b+a*titsEnd m a)*y) * ((b+a*titsEnd m a)*y)) *
          L 3 v * S 1 e (t + titsEnd m e * e) * L 2 s *
          S 2 (a*y) (r + titsEnd m (a*y) * (a*y)) := by
  obtain ⟨r,s,e,t,v,w,h⟩ := synchronizedSuzukiLinear_outer_coefficients Q split c a b y
  have hi : (S 0 a b)⁻¹ * (L 0 y)⁻¹ * S 0 a b * L 0 y =
      (S 2 (a*y) r * L 2 s * S 1 e t * L 3 v *
        S 3 ((b+a*titsEnd m a)*y) w *
          L 1 ((a^2*titsEnd m a+a*b+titsEnd m b)*y))⁻¹ := by
    calc
      _ = ((L 0 y)⁻¹ * (S 0 a b)⁻¹ * L 0 y * S 0 a b)⁻¹ := by group
      _ = _ := congrArg Inv.inv h
  refine ⟨r,s,e,t,v,w,?_⟩
  rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev] at hi
  simpa only [seed_pair_inv, seed_quartet_inv, map_zero, map_add, map_mul,
    zero_add, add_zero, mul_zero, mul_one, one_mul, mul_assoc] using hi

/-- The literal parameter-one residual in the actual synchronized chart. -/
theorem synchronizedSuzukiLinear_seed_support :
    ∃ r s e t v w : CoefficientField m,
      (L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 =
        S 2 1 r * L 2 s * S 1 e t * L 3 v * S 3 1 w * L 1 1 := by
  simpa only [one_mul,mul_one,map_one,map_zero,pow_one,one_pow,zero_add,add_zero,mul_zero]
    using synchronizedSuzukiLinear_outer_coefficients Q split c 1 0 1

/-- Inverting the V2-oriented seed gives the printed source right-commutator
orientation. The native Suzuki inverse correction is retained explicitly. -/
theorem synchronizedSuzukiLinear_seed_inverse_support :
    ∃ r s e t v w : CoefficientField m,
      (S 0 1 0)⁻¹ * (L 0 1)⁻¹ * S 0 1 0 * L 0 1 =
        L 1 1 * S 3 1 (w + 1) * L 3 v *
          S 1 e (t + titsEnd m e * e) * L 2 s * S 2 1 (r + 1) := by
  obtain ⟨r,s,e,t,v,w,h⟩ := synchronizedSuzukiLinear_seed_support Q split c
  have hi : (S 0 1 0)⁻¹ * (L 0 1)⁻¹ * S 0 1 0 * L 0 1 =
      (S 2 1 r * L 2 s * S 1 e t * L 3 v * S 3 1 w * L 1 1)⁻¹ := by
    calc
      _ = ((L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0)⁻¹ := by group
      _ = _ := congrArg Inv.inv h
  refine ⟨r,s,e,t,v,w,?_⟩
  rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev] at hi
  simpa only [seed_pair_inv, seed_quartet_inv, map_one, map_zero,
    one_mul, mul_one, pow_one, one_pow, zero_add, add_zero, mul_zero,
    mul_assoc] using hi


end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
