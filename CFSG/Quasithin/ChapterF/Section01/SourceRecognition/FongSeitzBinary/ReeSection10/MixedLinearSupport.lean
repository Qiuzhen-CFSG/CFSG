module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LinearMixedCoefficient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLinearCommute
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularNextTransforms
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAdjacent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularShortCompletion

/-!
# Three-factor support for the mixed linear source commutator

The literal Phi product gives five factors for the commutator of the two
linear roots. Since the Phi layer is elementary abelian, the two endpoint
Omega factors can be removed by conjugating with the actual endpoint roots.
This leaves the two linear factors and the middle Omega factor. The source
coefficient elimination from Fong--Seitz (10.19)--(10.22) remains separate.
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
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10.MixedLinearSupport
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)


local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)
private theorem omega_point_mem (i : Fin 4) (b : CoefficientField m) :
    synchronizedPositivePoint Q split c (.inr i) (0,b) ∈
      omegaOneAmbient (positiveRoot Q split (.inr i)) := by
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl _
    (synchronizedPositiveChart Q split c (.inr i) (0,b)).property
  change synchronizedPositivePoint Q split c (.inr i) (0,b) ^ 2 = 1
  rw [pow_two,synchronizedPositivePoint_quartet_mul]
  simpa only [zero_add,map_zero,zero_mul,add_zero,CharTwo.add_self_eq_zero] using
    synchronizedPositivePoint_quartet_zero Q split c i

private def omegaChartHom (i : Fin 4) : Multiplicative (CoefficientField m) →*
    omegaOneAmbient (positiveRoot Q split (.inr i)) where
  toFun a := ⟨synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd),omega_point_mem Q split c i _⟩
  map_one' := Subtype.ext (synchronizedPositivePoint_quartet_zero Q split c i)
  map_mul' a b := by
    apply Subtype.ext
    change synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd+b.toAdd) =
      synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd) *
      synchronizedPositivePoint Q split c (.inr i) (0,b.toAdd)
    symm
    simpa only [zero_add,map_zero,zero_mul,add_zero] using
      synchronizedPositivePoint_quartet_mul Q split c i 0 a.toAdd 0 b.toAdd

private theorem omegaChartHom_bijective (i : Fin 4) : Function.Bijective (omegaChartHom Q split c i) := by
  apply Function.Injective.bijective_of_nat_card_le
  · intro a b h
    have hv : synchronizedPositivePoint Q split c (.inr i) (0,a.toAdd) =
        synchronizedPositivePoint Q split c (.inr i) (0,b.toAdd) :=
      congrArg (fun z : omegaOneAmbient (positiveRoot Q split (.inr i)) => (z : X ⧸ Q.D)) h
    have h' := (synchronizedPositiveChart Q split c (.inr i)).injective (Subtype.ext hv)
    exact Multiplicative.toAdd.injective (congrArg Prod.snd h')
  · rw [omega_positiveRoot_card Q split c i,
      Nat.card_congr Multiplicative.toAdd,GaloisField.card 2 (2*m+1) (by omega)]


private theorem omega_surjective (i : Fin 4)
    (x : omegaOneAmbient (positiveRoot Q split (.inr i))) :
    ∃ b : CoefficientField m, S i 0 b = (x : X ⧸ Q.D) := by
  obtain ⟨b,hb⟩ := (omegaChartHom_bijective Q split c i).surjective x
  exact ⟨b.toAdd, congrArg Subtype.val hb⟩

/-- Five field coordinates of the actual mixed linear commutator. -/
theorem mixed_field_support (a b : CoefficientField m) :
    ∃ p q r s t : CoefficientField m,
      S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t =
        (L 1 a)⁻¹ * (L 0 b)⁻¹ * L 1 a * L 0 b := by
  obtain ⟨p,q,r,s,t,h⟩ := synchronized_mixedPhi_decomposition Q split c b a
  obtain ⟨p',hp⟩ := omega_surjective Q split c 3 p
  obtain ⟨q',rfl⟩ := (synchronizedPositiveChart Q split c (.inl 3)).surjective q
  obtain ⟨r',hr⟩ := omega_surjective Q split c 1 r
  obtain ⟨s',rfl⟩ := (synchronizedPositiveChart Q split c (.inl 2)).surjective s
  obtain ⟨t',ht⟩ := omega_surjective Q split c 2 t
  refine ⟨p',q',r',s',t',?_⟩
  dsimp only [synchronizedPositivePoint] at hp hr ht ⊢
  rw [hp,hr,ht]
  exact h

private theorem mixed_mem_phi (a b : CoefficientField m) :
    (L 1 a)⁻¹ * (L 0 b)⁻¹ * L 1 a * L 0 b ∈
      phi (simpleRemainder Q split 1) := by
  have hphi : ⁅simpleRemainder Q split 1, simpleRemainder Q split 1⁆ =
      phi (simpleRemainder Q split 1) := by
    simpa only [nConj, OneMemClass.coe_one, rightConjugate_one] using
      (c.relations.ten_three_frattini 1)
  have hu := (positiveRoot_le_remainder Q split (pinnedInput Q split c) (.inl 0) 1
    (by decide)) (synchronizedPositiveChart Q split c (.inl 0) b).property
  have hv := (reflectedLinear_le_suzukiRemainder Q split c)
    (synchronizedPositiveChart Q split c (.inl 1) a).property
  have hh := hphi ▸ commutator_mem_commutator (inv_mem hv) (inv_mem hu)
  simpa only [commutatorElement_def, inv_inv,synchronizedPositivePoint] using hh

private theorem pair_inv (i : Fin 4) (a : CoefficientField m) : (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_pair_mul]
  simp only [CharTwo.add_self_eq_zero,synchronizedPositivePoint_pair_zero]

/-- Elementary Frattini support forces the mixed linear commutator to be an involution. -/
theorem mixed_inv (a b : CoefficientField m) :
    ((L 1 a)⁻¹ * (L 0 b)⁻¹ * L 1 a * L 0 b)⁻¹ =
      (L 1 a)⁻¹ * (L 0 b)⁻¹ * L 1 a * L 0 b := by
  let k : (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
    ⟨_, mixed_mem_phi Q split c a b⟩
  let : IsElementaryAbelian 2 (phiCenterSection Q split (pinnedInput Q split c)).numerator :=
    phiRemainder_elementary Q split (pinnedInput Q split c)
  have hs : k*k = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2
        (phiCenterSection Q split (pinnedInput Q split c)).numerator) k
  exact congrArg Subtype.val (inv_eq_of_mul_eq_one_right hs)

private theorem commute_involutions_commutator {H : Type*} [Group H]
    (x y : H) (hx : x⁻¹ = x) (hy : y⁻¹ = y)
    (hk : (x⁻¹*y⁻¹*x*y)⁻¹ = x⁻¹*y⁻¹*x*y) :
    Commute x (x⁻¹*y⁻¹*x*y) ∧ Commute y (x⁻¹*y⁻¹*x*y) := by
  have hx2 : x*x = 1 := by calc x*x = x⁻¹*x := by rw [hx]
                           _ = 1 := inv_mul_cancel _
  constructor
  · change x * _ = _ * x
    calc
      x * (x⁻¹*y⁻¹*x*y) = (x⁻¹*y⁻¹*x*y)⁻¹ * x := by
        calc
          _ = y⁻¹*x*y := by group
          _ = y⁻¹*x⁻¹*y*(x*x) := by rw [hx,hx2,mul_one]
          _ = _ := by group
      _ = _ := by rw [hk]
  · change y * _ = _ * y
    calc
      y * (x⁻¹*y⁻¹*x*y) = (x⁻¹*y⁻¹*x*y)⁻¹ * y := by
        calc
          _ = y⁻¹*x⁻¹*y*x*y := by rw [hy]; group
          _ = _ := by group
      _ = _ := by rw [hk]

/-- Both actual endpoint elements centralize their mixed commutator. -/
theorem mixed_endpoint_commute (a b : CoefficientField m) :
    Commute (L 1 a) ((L 1 a)⁻¹*(L 0 b)⁻¹*L 1 a*L 0 b) ∧
    Commute (L 0 b) ((L 1 a)⁻¹*(L 0 b)⁻¹*L 1 a*L 0 b) :=
  commute_involutions_commutator _ _ (pair_inv Q split c 1 a)
    (pair_inv Q split c 0 b) (mixed_inv Q split c a b)

private theorem omega_inv (i : Fin 4) (a : CoefficientField m) : (S i 0 a)⁻¹ = S i 0 a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_quartet_mul]
  simp only [CharTwo.add_self_eq_zero,map_zero,zero_mul,synchronizedPositivePoint_quartet_zero]

private theorem reverse_conjugate {H : Type*} [Group H] {x y z : H}
    (h : x*y*x⁻¹ = z*y) : y*x*y⁻¹ = z⁻¹*x := by
  calc
    _ = z⁻¹*(z*y)*x*y⁻¹ := by group
    _ = z⁻¹*(x*y*x⁻¹)*x*y⁻¹ := by rw [h]
    _ = _ := by group

private theorem conjugate_of_commute {H : Type*} [Group H] {x y : H}
    (h : Commute x y) : MulAut.conj x y = y := by
  change x*y*x⁻¹ = y
  rw [h.eq,mul_inv_cancel_right]

private theorem omega0_conjugate (p b : CoefficientField m) :
    MulAut.conj (L 0 b) (S 3 0 p) = S 1 0 (p*b) * S 3 0 p := by
  have h := synchronized_next_shifted_conjugate Q split c 0 p b
  simp only [map_zero,zero_mul,add_zero,synchronizedPositivePoint_pair_zero,
    synchronizedPositivePoint_quartet_zero,mul_one] at h
  simpa only [omega_inv,MulAut.conj_apply] using reverse_conjugate h

private theorem central0_conjugate (r b : CoefficientField m) :
    MulAut.conj (L 0 b) (S 1 0 r) = S 1 0 r := by
  have h := synchronized_short_terminal_conjugate Q split c 0 r b
  simp only [zero_mul,synchronizedPositivePoint_quartet_zero,one_mul] at h
  exact conjugate_of_commute (Commute.symm (by
    change S 1 0 r * L 0 b = L 0 b * S 1 0 r
    have hh := congrArg (fun z => z * S 1 0 r) h
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh))

private theorem central1_conjugate (r a : CoefficientField m) :
    MulAut.conj (L 1 a) (S 1 0 r) = S 1 0 r := by
  simpa only [MulAut.conj_apply,zero_mul,synchronizedPositivePoint_quartet_zero,one_mul] using
    synchronized_short_perpendicular_conjugate Q split c 0 r a

private theorem omega1_conjugate (t a : CoefficientField m) :
    MulAut.conj (L 1 a) (S 2 0 t) = S 1 0 (t*a) * S 2 0 t := by
  simpa only [MulAut.conj_apply,map_zero,zero_mul,add_zero,synchronizedPositivePoint_pair_zero,
    synchronizedPositivePoint_quartet_zero,one_mul] using
    synchronized_next_reflected_conjugate Q split c 0 t a

private theorem central_commute_prefix (p q r s z : CoefficientField m) :
    Commute (S 3 0 p * L 3 q * S 1 0 r * L 2 s) (S 1 0 z) := by
  let d := pinnedInput Q split c
  let : IsElementaryAbelian 2 (phiCenterSection Q split d).numerator := phiRemainder_elementary Q split d
  have h := (show Commute
    (phiShiftedPoint Q split c p * phiPerpendicularPoint Q split c q *
      phiCentralPoint Q split c r * phiNextPoint Q split c s)
    (phiCentralPoint Q split c z) from Commute.all _ _).map
      (phiCenterSection Q split d).numerator.subtype
  exact h

private theorem omega_parameter_eq_zero (z : CoefficientField m)
    (h : S 1 0 z = 1) : z = 0 := by
  have hh : synchronizedPositiveChart Q split c (.inr 1) (0,z) =
      synchronizedPositiveChart Q split c (.inr 1) (0,0) := by
    apply Subtype.ext
    change S 1 0 z = S 1 0 0
    rw [synchronizedPositivePoint_quartet_zero,h]
  exact congrArg Prod.snd ((synchronizedPositiveChart Q split c (.inr 1)).injective hh)

private theorem conjugate_field0 (p q r s t b : CoefficientField m) :
    MulAut.conj (L 0 b) (S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t) =
      S 1 0 (p*b) * (S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t) := by
  have h3 := (synchronized_linear_commute_family Q split c q b).2.2.2.1.symm
  have h2 := (synchronized_linear_commute_family Q split c s b).2.2.2.2.symm
  rw [map_mul,map_mul,map_mul,map_mul,omega0_conjugate,
    conjugate_of_commute h3,central0_conjugate,conjugate_of_commute h2,
    conjugate_of_commute (synchronized_A0_B2_commute Q split c b 0 t)]
  simp only [mul_assoc]

private theorem conjugate_field1 (p q r s t a : CoefficientField m) :
    MulAut.conj (L 1 a) (S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t) =
      S 1 0 (t*a) * (S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t) := by
  have h3 := (synchronized_linear_commute_family Q split c a q).1
  have h2 := (synchronized_linear_commute_family Q split c a s).2.1
  have hs := (synchronized_adjacent_commute_family Q split c a 0 p).2.1
  rw [map_mul,map_mul,map_mul,map_mul,conjugate_of_commute hs,
    conjugate_of_commute h3,central1_conjugate,conjugate_of_commute h2,omega1_conjugate]
  rw [←mul_assoc,(central_commute_prefix Q split c p q r s (t*a)).eq,mul_assoc]

/-- Endpoint involutions remove both outer Omega coordinates from the mixed row. -/
theorem mixed_outer_zero (a b p q r s t : CoefficientField m)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : S 3 0 p * L 3 q * S 1 0 r * L 2 s * S 2 0 t =
      (L 1 a)⁻¹ * (L 0 b)⁻¹ * L 1 a * L 0 b) : p = 0 ∧ t = 0 := by
  have h0 := conjugate_of_commute (mixed_endpoint_commute Q split c a b).2
  have h1 := conjugate_of_commute (mixed_endpoint_commute Q split c a b).1
  rw [←h,conjugate_field0] at h0
  rw [←h,conjugate_field1] at h1
  have hp : S 1 0 (p*b) = 1 := mul_right_cancel (h0.trans (one_mul _).symm)
  have ht : S 1 0 (t*a) = 1 := mul_right_cancel (h1.trans (one_mul _).symm)
  exact ⟨(mul_eq_zero.mp (omega_parameter_eq_zero Q split c _ hp)).resolve_right hb,
    (mul_eq_zero.mp (omega_parameter_eq_zero Q split c _ ht)).resolve_right ha⟩

/-- Only two linear coefficients and the middle Omega coefficient remain in
source (10.19); the exterior Omega coordinates have been discharged. -/
theorem mixed_three_factor_support (a b : CoefficientField m) :
    ∃ q r s : CoefficientField m,
      L 3 q * S 1 0 r * L 2 s = (L 1 a)⁻¹*(L 0 b)⁻¹*L 1 a*L 0 b := by
  by_cases ha : a = 0
  · subst a
    refine ⟨0,0,0,?_⟩
    simp only [synchronizedPositivePoint_pair_zero,synchronizedPositivePoint_quartet_zero,
      inv_one,one_mul,mul_one,inv_mul_cancel]
  by_cases hb : b = 0
  · subst b
    refine ⟨0,0,0,?_⟩
    simp only [synchronizedPositivePoint_pair_zero,synchronizedPositivePoint_quartet_zero,
      inv_one,mul_one,inv_mul_cancel]
  obtain ⟨p,q,r,s,t,h⟩ := mixed_field_support Q split c a b
  obtain ⟨rfl,rfl⟩ := mixed_outer_zero Q split c a b p q r s t ha hb h
  exact ⟨q,r,s,by simpa only [synchronizedPositivePoint_quartet_zero,one_mul,mul_one] using h⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10.MixedLinearSupport

