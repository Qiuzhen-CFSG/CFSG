module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PhiOppositeCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SuzukiOppositeCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularSuzukiNear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularSuzukiCommute
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLinearCommute

/-!
# The middle coordinate of the opposite whole-Suzuki commutator

The previously determined exterior coordinates leave a three-factor main
commutator. Squaring the opposite root parameter converts it to the proved
opposite-Omega action. The resulting square-commutator identity isolates the
middle linear coefficient, without torus separation or a nonbinary assumption.
Only the two central Suzuki labels remain explicit in the public result.

Source: Fong--Seitz II (1974), (10.23)--(10.25), pp.227--228. The native
triangular chart makes the middle coefficient a theta(a) y theta(y), whereas
the printed chart's corresponding middle term is zero.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4 BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4.RootPresentationRecognition WeylPresentation SignedGeometry
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

private theorem quartet_inv (i : Fin 4) (a b : CoefficientField m) :
    (S i a b)⁻¹ = S i a (b+titsEnd m a*a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_quartet_mul]
  have he : b+(b+titsEnd m a*a)+titsEnd m a*a = 0 := by
    rw [←add_assoc b b,CharTwo.add_self_eq_zero,zero_add,CharTwo.add_self_eq_zero]
  simp only [he,CharTwo.add_self_eq_zero,synchronizedPositivePoint_quartet_zero]

private theorem quartet_square (i : Fin 4) (a b : CoefficientField m) :
    S i a b * S i a b = S i 0 (titsEnd m a*a) := by
  rw [synchronizedPositivePoint_quartet_mul]
  simp only [CharTwo.add_self_eq_zero,zero_add]

private theorem pair_square (i : Fin 4) (a : CoefficientField m) : L i a * L i a = 1 := by
  rw [synchronizedPositivePoint_pair_mul,CharTwo.add_self_eq_zero,
    synchronizedPositivePoint_pair_zero]

/-- Opposite omega right commutator in the actual quotient. -/
theorem synchronized_oppositeOmega_right (a b y : CoefficientField m) :
    (S 2 0 y)⁻¹ * (S 0 a b)⁻¹ * S 2 0 y * S 0 a b =
      S 1 0 (b*titsEnd m y) *
        (S 3 0 ((a^2*titsEnd m a+a*b+titsEnd m b)*y) *
          L 3 ((b+a*titsEnd m a)*y) * L 2 (a*y)) := by
  have h := congrArg (fun v : (phiCenterSection Q split (pinnedInput Q split c)).numerator =>
    (v : X ⧸ Q.D)) (synchronized_oppositeOmega_commutator Q split c a b y)
  rw [phiRightCommutator_val,phiOppositeOmega_point,←simple_suzuki] at h
  exact h

private theorem square_word {G : Type*} [Group G] (A B C D : G)
    (hBA : Commute B A) (hBC : Commute B C) (hDA : Commute D A)
    (hDB : Commute D B) (hCA : C*A = D*A*C) :
    (A*B*C)*(A*B*C) = (A*A)*D*(B*B)*(C*C) := by
  calc
    _ = A*B*(C*A)*B*C := by group
    _ = A*B*(D*A*C)*B*C := by rw [hCA]
    _ = A*(B*D)*A*(C*B)*C := by group
    _ = A*(D*B)*A*(B*C)*C := by rw [hDB.symm.eq,hBC.symm.eq]
    _ = A*D*(B*A)*B*C*C := by group
    _ = A*D*(A*B)*B*C*C := by rw [hBA.eq]
    _ = A*(D*A)*(B*B)*(C*C) := by group
    _ = _ := by rw [hDA.eq]; group

private theorem middle_square (v l w t r : CoefficientField m) :
    (S 1 v l * L 3 w * S 3 t r) * (S 1 v l * L 3 w * S 3 t r) =
      S 1 0 (titsEnd m v*v) * L 3 (t*v) * S 3 0 (titsEnd m t*t) := by
  have hCA : S 3 t r * S 1 v l = L 3 (t*v) * S 1 v l * S 3 t r := by
    have h := congrArg (fun x => x*S 3 t r)
      (synchronized_nearSuzuki_middle_conjugate Q split c t r v l)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using h
  have h := square_word (S 1 v l) (L 3 w) (S 3 t r) (L 3 (t*v))
    (synchronized_adjacent_commute_family Q split c w v l).2.2.2.1
    (synchronized_adjacent_commute_family Q split c w t r).2.2.1
    (synchronized_adjacent_commute_family Q split c (t*v) v l).2.2.2.1
    (by rw [Commute,SemiconjBy,synchronizedPositivePoint_pair_mul,
      synchronizedPositivePoint_pair_mul,add_comm]) hCA
  simpa only [quartet_square,pair_square,mul_one] using h

private theorem opposite_conj_S1 (y v l : CoefficientField m) :
    (S 2 y 0)⁻¹ * S 1 v l * S 2 y 0 = L 2 (v*y) * S 1 v l := by
  have h := synchronized_nearSuzuki_terminal_conjugate Q split c v l y 0
  have hh := congrArg (fun x => (S 2 y 0)⁻¹*x*S 1 v l) h
  have hc := (synchronized_adjacent_commute_family Q split c (v*y) y 0).2.2.2.2.2.1
  calc
    _ = (S 2 y 0)⁻¹ * (L 2 (v*y) * S 2 y 0) * S 1 v l := by
      rw [←h]; group
    _ = L 2 (v*y)*S 1 v l := by rw [hc.eq]; group

private theorem opposite_conj_L3 (y w : CoefficientField m) :
    (S 2 y 0)⁻¹ * L 3 w * S 2 y 0 = S 1 0 (y*w) * L 3 w := by
  have h := synchronized_short_reflected_conjugate Q split c y 0 w
  have hc : Commute (S 1 0 (y*w)) (S 2 y 0) := by
    change _ * _ = _ * _
    have hh := congrArg (fun x => x*S 1 0 (y*w))
      (synchronized_nearSuzuki_terminal_conjugate Q split c 0 (y*w) y 0)
    simpa only [zero_mul,synchronizedPositivePoint_pair_zero,one_mul,mul_assoc,
      inv_mul_cancel,mul_one] using hh
  calc
    _ = (S 2 y 0)⁻¹ * (S 1 0 (y*w) * S 2 y 0) * L 3 w := by
      rw [←h]; group
    _ = S 1 0 (y*w)*L 3 w := by rw [hc.eq]; group

private theorem opposite_conj_S3 (y t r : CoefficientField m) :
    (S 2 y 0)⁻¹ * S 3 t r * S 2 y 0 = S 3 t r := by
  have hc := (synchronized_suzuki_commute_family Q split c t r y 0).2
  rw [mul_assoc, hc.eq]
  group


private theorem omega_main_commute (i : Fin 4) (e v l : CoefficientField m) :
    Commute (S i 0 e) (S i v l) := by
  change _ * _ = _ * _
  rw [synchronizedPositivePoint_quartet_mul,synchronizedPositivePoint_quartet_mul]
  simp only [zero_add,add_zero,map_zero,zero_mul,mul_zero]
  rw [add_comm e l]

private theorem opposite_conj_middle (y v l w t r : CoefficientField m) :
    (S 2 y 0)⁻¹ * (S 1 v l * L 3 w * S 3 t r) * S 2 y 0 =
      (L 2 (v*y) * S 1 0 (y*w)) * (S 1 v l * L 3 w * S 3 t r) := by
  calc
    _ = ((S 2 y 0)⁻¹*S 1 v l*S 2 y 0) *
        ((S 2 y 0)⁻¹*L 3 w*S 2 y 0) * ((S 2 y 0)⁻¹*S 3 t r*S 2 y 0) := by group
    _ = (L 2 (v*y)*S 1 v l)*(S 1 0 (y*w)*L 3 w)*S 3 t r := by
      rw [opposite_conj_S1,opposite_conj_L3,opposite_conj_S3]
    _ = L 2 (v*y)*(S 1 v l*S 1 0 (y*w))*L 3 w*S 3 t r := by group
    _ = _ := by rw [(omega_main_commute Q split c 1 (y*w) v l).symm.eq]; group

private theorem omega_add (i : Fin 4) (a b : CoefficientField m) :
    S i 0 a*S i 0 b = S i 0 (a+b) := by
  simpa only [zero_add,map_zero,zero_mul,add_zero] using
    synchronizedPositivePoint_quartet_mul Q split c i 0 a 0 b

private theorem phi_product_reorder (p w r : CoefficientField m) :
    S 3 0 r*L 3 w*L 2 p = L 2 p*L 3 w*S 3 0 r := by
  let : IsElementaryAbelian 2 (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
    phiRemainder_elementary Q split (pinnedInput Q split c)
  have he : phiShiftedPoint Q split c r * phiPerpendicularPoint Q split c w * phiNextPoint Q split c p =
      phiNextPoint Q split c p * phiPerpendicularPoint Q split c w * phiShiftedPoint Q split c r := by ac_rfl
  exact congrArg (fun z : (phiCenterSection Q split (pinnedInput Q split c)).numerator =>
    (z : X ⧸ Q.D)) he

private theorem middle_coefficient (a y l w r : CoefficientField m) (hy : y ≠ 0)
    (hk : (S 2 y 0)⁻¹*(S 0 a 0)⁻¹*S 2 y 0*S 0 a 0 =
      S 1 (titsEnd m y*a) l*L 3 w*S 3 (titsEnd m a*y) r) :
    w = (a*titsEnd m a)*(y*titsEnd m y) := by
  let v := titsEnd m y*a
  let t := titsEnd m a*y
  let k := S 1 v l*L 3 w*S 3 t r
  have he : (S 2 0 (titsEnd m y*y))⁻¹*(S 0 a 0)⁻¹*S 2 0 (titsEnd m y*y)*S 0 a 0 =
      L 2 (v*y)*S 1 0 (y*w+titsEnd m v*v)*L 3 (t*v)*S 3 0 (titsEnd m t*t) := by
    calc
      _ = (S 2 y 0)⁻¹*((S 2 y 0)⁻¹*(S 0 a 0)⁻¹*S 2 y 0*S 0 a 0)*S 2 y 0 *
          ((S 2 y 0)⁻¹*(S 0 a 0)⁻¹*S 2 y 0*S 0 a 0) := by
        rw [←quartet_square Q split c 2 y 0]; group
      _ = ((S 2 y 0)⁻¹*k*S 2 y 0)*k := by rw [hk]
      _ = (L 2 (v*y)*S 1 0 (y*w))*(k*k) := by
        rw [show (S 2 y 0)⁻¹*k*S 2 y 0 = (L 2 (v*y)*S 1 0 (y*w))*k from
          opposite_conj_middle Q split c y v l w t r]
        group
      _ = (L 2 (v*y)*S 1 0 (y*w))*(S 1 0 (titsEnd m v*v)*L 3 (t*v)*S 3 0 (titsEnd m t*t)) := by
        rw [show k*k = _ from middle_square Q split c v l w t r]
      _ = L 2 (v*y)*(S 1 0 (y*w)*S 1 0 (titsEnd m v*v))*L 3 (t*v)*S 3 0 (titsEnd m t*t) := by group
      _ = _ := by rw [omega_add]
  have hphi := synchronized_oppositeOmega_right Q split c a 0 (titsEnd m y*y)
  simp only [zero_mul,mul_zero,map_zero,add_zero,zero_add,
    synchronizedPositivePoint_quartet_zero,one_mul] at hphi
  have hP : a*(titsEnd m y*y) = v*y := by dsimp [v]; ring
  have hW : a*titsEnd m a*(titsEnd m y*y) = t*v := by dsimp [t,v]; ring
  have hR : a^2*titsEnd m a*(titsEnd m y*y) = titsEnd m t*t := by
    dsimp [t]
    rw [map_mul,titsEnd_twice]
    ring
  rw [hP,hW,hR,phi_product_reorder] at hphi
  have hz : S 1 0 (y*w+titsEnd m v*v) = 1 := by
    have hh := he.symm.trans hphi
    have hh' : L 2 (v*y)*(S 1 0 (y*w+titsEnd m v*v)*L 3 (t*v)*S 3 0 (titsEnd m t*t)) =
        L 2 (v*y)*(1*L 3 (t*v)*S 3 0 (titsEnd m t*t)) := by simpa only [one_mul,mul_assoc] using hh
    exact mul_right_cancel (mul_right_cancel (mul_left_cancel hh'))
  have hzero : y*w+titsEnd m v*v = 0 := by
    have hh : S 1 0 (y*w+titsEnd m v*v) = S 1 0 0 := by
      rw [hz,synchronizedPositivePoint_quartet_zero]
    exact congrArg Prod.snd ((synchronizedPositiveChart Q split c (.inr 1)).injective (Subtype.ext hh))
  have hcoef : y*w = titsEnd m v*v := by
    simpa only [CharTwo.neg_eq] using (eq_neg_iff_add_eq_zero.mpr hzero)
  apply mul_left_cancel₀ hy
  rw [hcoef]
  dsimp [v]
  rw [map_mul,titsEnd_twice]
  ring

/-- The opposite main-curve commutator has its exact middle linear coordinate,
uniformly over all fields; only its two central Suzuki coordinates remain. -/
theorem synchronizedSuzukiMixed_main_middle (a y : CoefficientField m) :
    ∃ l r : CoefficientField m,
      (synchronizedSuzukiMixed Q split c a 0 y 0 : X ⧸ Q.D) =
        S 1 (titsEnd m y*a) l * L 3 ((a*titsEnd m a)*(y*titsEnd m y)) *
          S 3 (titsEnd m a*y) r := by
  by_cases hy : y = 0
  · subst y
    refine ⟨0,0,?_⟩
    rw [synchronizedSuzukiMixed_val]
    simp only [synchronizedPositivePoint_quartet_zero,inv_one,one_mul,map_zero,
      zero_mul,mul_zero,synchronizedPositivePoint_pair_zero,mul_one,inv_mul_cancel]
  obtain ⟨l,w,r,h⟩ := synchronizedSuzukiMixed_four_coefficients Q split c a 0 y 0
  simp only [zero_mul,synchronizedPositivePoint_pair_zero,one_mul,mul_one] at h
  have he := h
  rw [synchronizedSuzukiMixed_val,←simple_suzuki] at he
  exact ⟨l,r,by rw [middle_coefficient Q split c a y l w r hy he] at h; exact h⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
