module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.BinaryInterior
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLastSuzukiLinear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.SuzukiOppositeEndpoints


/-!
# The binary source endpoint equations

The rank-one Suzuki relation gives a fourth-power constraint on conjugation by
an inverse main-root element followed by reflection. The seven source root
generators satisfy the certified interior rewrite table, and Carter coordinates
separate its outputs. The finite rigidity theorem therefore fixes both endpoint
commutators at once. Binary coefficient exhaustion extends the resulting unit
identities to the two complete main-curve families.

Source: Fong--Seitz II (1974), Section 10, (10.23)--(10.41), in the literal
native triangular Suzuki charts. No endpoint angular equation is assumed.
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
open ReeF4.RootPresentationRecognition WeylPresentation SignedGeometry
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local notation "L" i:max a:max => synchronizedPositivePoint Q split c (Sum.inl i) a
local notation "S" i:max a:max b:max => synchronizedPositivePoint Q split c (Sum.inr i) (a,b)
local notation "W" s:max => (sourceSimpleReflection Q split c s : X ⧸ Q.D)

private theorem batch_pair_reflection (s : Bool) (i : Fin 4)
    (h : (step false s (true,i)).1 = true) (a : CoefficientField m) :
    MulAut.conj (W s) (L i a) = L (next false s i) a := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) false s (true,i)
    (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D)
    (synchronizedLinear_perpendicularReflection Q split c a)
  rw [show step false s (true,i) = (true,next false s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_pair_word,MulAut.conj_apply] using hh

private theorem batch_quartet_reflection (s : Bool) (i : Fin 4)
    (h : (step true s (true,i)).1 = true) (a b : CoefficientField m) :
    MulAut.conj (W s) (S i a b) = S (next true s i) a b := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) true s (true,i)
    (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)
    (synchronizedSuzuki_perpendicularReflection Q split c a b)
  rw [show step true s (true,i) = (true,next true s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord,↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_quartet_word,MulAut.conj_apply] using hh


namespace BinarySourceAction
open BenderSuzuki.MatrixGroups

def rootAction : MulAut (X ⧸ Q.D) := MulAut.conj ((S 0 1 0)⁻¹)
def reflection : MulAut (X ⧸ Q.D) := MulAut.conj (W true)
def action : MulAut (X ⧸ Q.D) := rootAction Q split c * reflection Q split c

private theorem simple_suzuki (a b : CoefficientField m) :
    S 0 a b = (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) := by
  rw [synchronizedPositivePoint_quartet_word]
  simp only [positiveWord,Matrix.cons_val_zero,map_one,inv_one,one_mul,mul_one]

private theorem source_power : (W true * S 0 1 0)^4 = 1 := by
  let e := suzukiActorEquiv Q split 1 m (pinnedInput Q split c).suzuki
    (pinnedInput Q split c).suzukiBorel
  let u : rankOne Q split 1 := inclusion le_sup_left
    (suzukiChart Q split (pinnedInput Q split c) (1,0))
  let w : rankOne Q split 1 := ⟨(c.reflections 1).val,(c.reflections 1).mem_rankOne⟩
  have hm : (e (w*u))^4 = 1 := by
    rw [map_mul]
    dsimp only [e,w,u]
    rw [pinnedInput_reflection,suzukiActorEquiv_simpleRoot]
    change (suzukiWeyl m * (((suzukiRootEquiv Q split 1 m
      (pinnedInput Q split c).suzuki (pinnedInput Q split c).suzukiBorel)
      ((suzukiRootEquiv Q split 1 m (pinnedInput Q split c).suzuki
      (pinnedInput Q split c).suzukiBorel).symm
        (matrixRootPoint m 1 (0+1*titsEnd m 1)))) : SuzukiMatrixGroup m))^4 = 1
    rw [MulEquiv.apply_symm_apply]
    simp only [map_one,mul_one,zero_add]
    apply Subtype.ext
    apply Units.ext
    change (SuzukiWeylMatrix m * SuzukiRootMatrix m 1 1)^4 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SuzukiWeylMatrix,SuzukiRootMatrix,pow_succ,Matrix.mul_apply,Fin.sum_univ_four,
        CharTwo.add_self_eq_zero]
  have he : (w*u)^4 = 1 := e.injective (by simpa only [map_pow,map_one] using hm)
  have hv := congrArg (fun g : rankOne Q split 1 => (g : X ⧸ Q.D)) he
  rw [simple_suzuki]
  exact hv

/-- The actual rank-one fourth power, in the certificate's action order. -/
theorem action_fourth : action Q split c ^ 4 = 1 := by
  have hw : (W true)⁻¹ = W true := by
    apply inv_eq_of_mul_eq_one_right
    have h := congrArg (fun w : Q.tits.N => (w : X ⧸ Q.D))
      (sourceSimpleReflection_sq Q split c true)
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,pow_two,Subgroup.coe_mul] using h
  have hi := congrArg Inv.inv (source_power Q split c)
  have hp : ((S 0 1 0)⁻¹ * W true)^4 = 1 := by
    simpa only [←inv_pow,mul_inv_rev,hw,inv_one] using hi
  change (MulAut.conj ((S 0 1 0)⁻¹) * MulAut.conj (W true))^4 = 1
  rw [←map_mul,←map_pow,hp,map_one]

/-- The Suzuki reflection reverses the seven source generators literally. -/
theorem reflection_generator (i : Fin 7) :
    reflection Q split c (BinaryInterior.generators Q split c i) =
      BinaryInterior.generators Q split c i.rev := by
  fin_cases i <;>
    simp only [reflection,BinaryInterior.generators,Matrix.cons_val,Fin.reduceFinMk,
      Fin.rev,Fin.isValue]
  · exact batch_pair_reflection Q split c true 0 (by decide) 1
  · exact batch_quartet_reflection Q split c true 2 (by decide) 1 0
  · exact batch_pair_reflection Q split c true 2 (by decide) 1
  · exact batch_quartet_reflection Q split c true 1 (by decide) 1 0
  · exact batch_pair_reflection Q split c true 3 (by decide) 1
  · exact batch_quartet_reflection Q split c true 3 (by decide) 1 0
  · exact batch_pair_reflection Q split c true 1 (by decide) 1

/-- The fixed five generator actions require no remaining endpoint equation. -/
theorem rootAction_known :
    rootAction Q split c (L 2 1) = L 3 1 * (S 1 1 0 * S 1 1 0) * L 2 1 ∧
    rootAction Q split c (S 1 1 0) = S 1 1 0 ∧
    rootAction Q split c (L 3 1) = (S 3 1 0 * S 3 1 0) * L 3 1 ∧
    rootAction Q split c (S 3 1 0) = S 3 1 0 * L 1 1 ∧
    rootAction Q split c (L 1 1) = L 1 1 := by
  have hsi : (S 0 1 0)⁻¹ = S 0 1 1 := by
    apply inv_eq_of_mul_eq_one_right
    rw [synchronizedPositivePoint_quartet_mul]
    simp only [CharTwo.add_self_eq_zero,zero_add,map_one,mul_one,
      synchronizedPositivePoint_quartet_zero]
  have hss (i : Fin 4) : S i 1 0 * S i 1 0 = S i 0 1 := by
    rw [synchronizedPositivePoint_quartet_mul]
    simp only [CharTwo.add_self_eq_zero,zero_add,map_one,mul_one]
  have hco := synchronized_suzuki_commute_family Q split c 1 1 1 0
  have had := synchronized_adjacent_commute_family Q split c 1 1 1
  simp only [rootAction,MulAut.conj_apply,hsi]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hss]
    have h := synchronized_next_conjugate Q split c 1 1 1
    simpa only [map_one,mul_one,CharTwo.add_self_eq_zero,
      synchronizedPositivePoint_quartet_zero,one_mul,mul_assoc] using h
  · rw [hco.1.eq]; group
  · rw [hss]
    simpa only [one_mul] using synchronized_short_conjugate Q split c 1 1 1
  · have h := synchronized_nearSuzuki_conjugate Q split c 1 1 1 0
    simpa only [one_mul,(synchronized_adjacent_commute_family Q split c 1 1 0).2.1.eq]
      using h
  · rw [had.1.symm.eq]; group


private def bit (b : Bool) : CoefficientField m := if b then 1 else 0

private theorem first_image_value (r s e t v w ε : Bool) :
    evalWord (BinaryInterior.generators Q split c)
      (BinaryEndSupportRigidity.actor r s e t v w ε 0) =
    L 0 1 * (S 2 1 (bit r) * L 2 (bit s) * S 1 (bit e) (bit t) *
      L 3 (bit v) * S 3 1 (bit w) * L 1 1) := by
  -- Each independent bit is converted using just its own root multiplication.
  have h1 (b : Bool) : evalWord (BinaryInterior.generators Q split c)
      (if b then [1,1,1] else [1]) = S 2 1 (bit b) := by
    cases b <;> simp [evalWord,BinaryInterior.generators,bit,
      synchronizedPositivePoint_quartet_mul,CharTwo.add_self_eq_zero]
  have h5 (b : Bool) : evalWord (BinaryInterior.generators Q split c)
      (if b then [5,5,5] else [5]) = S 3 1 (bit b) := by
    cases b <;> simp [evalWord,BinaryInterior.generators,bit,
      synchronizedPositivePoint_quartet_mul,CharTwo.add_self_eq_zero]
  have h2 (b : Bool) : evalWord (BinaryInterior.generators Q split c)
      (if b then [2] else []) = L 2 (bit b) := by
    cases b <;> simp [evalWord,BinaryInterior.generators,bit]
  have h4 (b : Bool) : evalWord (BinaryInterior.generators Q split c)
      (if b then [4] else []) = L 3 (bit b) := by
    cases b <;> simp [evalWord,BinaryInterior.generators,bit]
  have h3 (b d : Bool) : evalWord (BinaryInterior.generators Q split c)
      (if b then [3] else []) * evalWord (BinaryInterior.generators Q split c)
      (if d then [3,3] else []) = S 1 (bit b) (bit d) := by
    cases b <;> cases d <;> simp [evalWord,BinaryInterior.generators,bit,
      synchronizedPositivePoint_quartet_mul,CharTwo.add_self_eq_zero]
  simp only [BinaryEndSupportRigidity.actor,Matrix.cons_val,evalWord_append]
  rw [h1,h2,h4,h5]
  simp only [evalWord,BinaryInterior.generators,Matrix.cons_val,mul_one]
  dsimp only [BinaryInterior.generators] at h3
  simp only [←mul_assoc] at h3 ⊢
  rw [mul_assoc (L 0 1 * S 2 1 (bit r) * L 2 (bit s)),h3]

private theorem second_image_value (r s e t v w ε : Bool) :
    evalWord (BinaryInterior.generators Q split c)
      (BinaryEndSupportRigidity.actor r s e t v w ε 1) =
    S 2 1 0 * (S 1 1 (1+bit ε) * L 3 1 * S 3 1 (bit ε)) := by
  cases ε <;> simp [BinaryEndSupportRigidity.actor,evalWord,
    BinaryInterior.generators,bit,synchronizedPositivePoint_quartet_mul,
    CharTwo.add_self_eq_zero,←mul_assoc]
  rw [mul_assoc,synchronizedPositivePoint_quartet_mul]
  simp only [add_zero,zero_add,mul_zero]

private theorem image_support (r s e t v w ε : Bool)
    (h0 : (L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 =
      S 2 1 (bit r) * L 2 (bit s) * S 1 (bit e) (bit t) *
        L 3 (bit v) * S 3 1 (bit w) * L 1 1)
    (h1 : (S 2 1 0)⁻¹ * (S 0 1 0)⁻¹ * S 2 1 0 * S 0 1 0 =
      S 1 1 (1+bit ε) * L 3 1 * S 3 1 (bit ε)) :
    ∀ i, evalWord (BinaryInterior.generators Q split c)
        (BinaryEndSupportRigidity.actor r s e t v w ε i) =
      rootAction Q split c (BinaryInterior.generators Q split c i) := by
  intro i
  have hk := rootAction_known Q split c
  fin_cases i <;> simp only [Fin.reduceFinMk]
  · rw [first_image_value]
    simp only [BinaryInterior.generators,Matrix.cons_val]
    rw [←h0]
    simp only [rootAction,MulAut.conj_apply,inv_inv]
    group
  · rw [second_image_value]
    simp only [BinaryInterior.generators,Matrix.cons_val]
    rw [←h1]
    simp only [rootAction,MulAut.conj_apply,inv_inv]
    group
  · simpa only [BinaryEndSupportRigidity.actor,BinaryInterior.generators,Matrix.cons_val,
      Fin.reduceFinMk,evalWord,mul_one,mul_assoc] using hk.1.symm
  · simpa only [BinaryEndSupportRigidity.actor,BinaryInterior.generators,Matrix.cons_val,
      Fin.reduceFinMk,evalWord,mul_one] using hk.2.1.symm
  · simpa only [BinaryEndSupportRigidity.actor,BinaryInterior.generators,Matrix.cons_val,
      Fin.reduceFinMk,evalWord,mul_one,mul_assoc] using hk.2.2.1.symm
  · simpa only [BinaryEndSupportRigidity.actor,BinaryInterior.generators,Matrix.cons_val,
      Fin.reduceFinMk,evalWord,mul_one] using hk.2.2.2.1.symm
  · simpa only [BinaryEndSupportRigidity.actor,BinaryInterior.generators,Matrix.cons_val,
      Fin.reduceFinMk,evalWord,mul_one] using hk.2.2.2.2.symm

private theorem support_rigid (r s e t v w ε : Bool)
    (h0 : (L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 =
      S 2 1 (bit r) * L 2 (bit s) * S 1 (bit e) (bit t) *
        L 3 (bit v) * S 3 1 (bit w) * L 1 1)
    (h1 : (S 2 1 0)⁻¹ * (S 0 1 0)⁻¹ * S 2 1 0 * S 0 1 0 =
      S 1 1 (1+bit ε) * L 3 1 * S 3 1 (bit ε)) :
    r = true ∧ s = true ∧ e = false ∧ t = true ∧ v = true ∧ w = false ∧ ε = false := by
  let x := BinaryInterior.generators Q split c
  have hu := image_support Q split c r s e t v w ε h0 h1
  have hi (i : Fin 7) : evalWord x (BinaryEndSupportRigidity.images r s e t v w ε i) =
      action Q split c (x i) := by
    change evalWord x (BinaryEndSupportRigidity.actor r s e t v w ε i.rev) = _
    rw [action,MulAut.mul_apply,reflection_generator]
    exact hu i.rev
  have hfour : action Q split c (action Q split c (action Q split c
      (action Q split c (evalWord x [1,5])))) = evalWord x [1,5] := by
    have h := congrArg (fun f : MulAut (X ⧸ Q.D) => f (evalWord x [1,5]))
      (action_fourth Q split c)
    simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply] using h
  have hsq : evalWord x (BinaryEndSupportRigidity.actor r s e t v w ε 0) *
      evalWord x (BinaryEndSupportRigidity.actor r s e t v w ε 0) = 1 := by
    rw [hu 0,←map_mul]
    change rootAction Q split c (L 0 1 * L 0 1) = 1
    rw [synchronizedPositivePoint_pair_mul,CharTwo.add_self_eq_zero,
      synchronizedPositivePoint_pair_zero,map_one]
  exact BinaryEndSupportRigidity.rigidity x (action Q split c).toMonoidHom
    (BinaryInterior.rules_valid Q split c) r s e t v w ε hi
    (BinaryInterior.coordinates_injective Q split c) hfour hsq

private theorem binary_bit (z : CoefficientField 0) : ∃ b : Bool, z = bit (m := 0) b := by
  by_cases hz : z = 0
  · exact ⟨false,hz⟩
  · refine ⟨true,?_⟩
    have h : z*z = z*1 := by simpa only [Nat.mul_zero,zero_add,pow_one,pow_two,mul_one] using field_pow 0 z
    exact mul_left_cancel₀ hz h

/-- Both binary parameter-one end commutators have their literal native coefficients. -/
theorem binary_end_seeds (hfield : m = 0) :
    ((L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 =
      S 2 1 1 * L 2 1 * S 1 0 1 * L 3 1 * S 3 1 0 * L 1 1) ∧
    ((S 2 1 0)⁻¹ * (S 0 1 0)⁻¹ * S 2 1 0 * S 0 1 0 =
      S 1 1 1 * L 3 1 * S 3 1 0) := by
  subst m
  obtain ⟨r,s,e,t,v,w,h0⟩ := synchronizedSuzukiLinear_seed_support Q split c
  obtain ⟨ε,h1⟩ := synchronizedSuzukiMixed_binary_seed Q split c rfl
  rw [synchronizedSuzukiMixed_val,←simple_suzuki] at h1
  obtain ⟨r,rfl⟩ := binary_bit r
  obtain ⟨s,rfl⟩ := binary_bit s
  obtain ⟨e,rfl⟩ := binary_bit e
  obtain ⟨t,rfl⟩ := binary_bit t
  obtain ⟨v,rfl⟩ := binary_bit v
  obtain ⟨w,rfl⟩ := binary_bit w
  obtain ⟨ε,rfl⟩ := binary_bit ε
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := support_rigid Q split c r s e t v w ε h0 h1
  exact ⟨h0,by simpa only [bit,Bool.false_eq_true,↓reduceIte,add_zero] using h1⟩

/-- The opposite main-curve equation for every pair of binary coefficients. -/
theorem binary_opposite_main_commutator (hfield : m = 0)
    (a y : CoefficientField m) :
    (S 2 y 0)⁻¹ * (S 0 a 0)⁻¹ * S 2 y 0 * S 0 a 0 =
      S 1 (a*titsEnd m y) (titsEnd m (a*titsEnd m y)*(a*titsEnd m y)) *
        L 3 ((a*titsEnd m a)*(y*titsEnd m y)) * S 3 (titsEnd m a*y) 0 := by
  subst m
  obtain ⟨a,rfl⟩ := binary_bit a
  obtain ⟨y,rfl⟩ := binary_bit y
  cases a <;> cases y <;> simp [bit]
  exact (binary_end_seeds Q split c rfl).2

/-- The last main-curve equation for every pair of binary coefficients. -/
theorem binary_last_main_commutator (hfield : m = 0)
    (a x : CoefficientField m) :
    (L 0 x)⁻¹ * (S 0 a 0)⁻¹ * L 0 x * S 0 a 0 =
      S 2 (a*x) (titsEnd m (a*x)*(a*x)) *
        L 2 ((a^2*titsEnd m a)*(x*titsEnd m x)) *
        S 1 0 ((a^3*(titsEnd m a)^2)*(x^2*titsEnd m x)) *
        L 3 ((a^2*(titsEnd m a)^2)*(x*titsEnd m x)) *
        S 3 ((a*titsEnd m a)*x) 0 * L 1 ((a^2*titsEnd m a)*x) := by
  subst m
  obtain ⟨a,rfl⟩ := binary_bit a
  obtain ⟨x,rfl⟩ := binary_bit x
  cases a <;> cases x <;> simp [bit]
  exact (binary_end_seeds Q split c rfl).1

end BinarySourceAction
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
