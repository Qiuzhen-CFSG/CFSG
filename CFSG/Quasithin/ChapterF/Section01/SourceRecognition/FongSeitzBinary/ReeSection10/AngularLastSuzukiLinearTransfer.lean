module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularFaithfulSuffix
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularOppositeExtension
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularLastSuzukiLinearBraid

/-!
# Faithful transfer of the last source seed constraints

The linear braid fixes the conjugated parameter-one Suzuki element. Its
reflected factorization and disjointness of the simple root from its remainder
fix the first central coefficient. Faithfulness of the six-root realization
then transfers the reflected word, involution and adjacent commutation to the
native model. These are the exact inputs of the final coefficient calculation.

Source: Carter 2.5.10--17; Fong--Seitz II, Section 10, (10.27)--(10.41).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4
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
local notation "NL" i:max a:max => (PositiveTables.pair m i a : Model m)
local notation "NS" i:max a:max b:max => (PositiveTables.quartet m i a b : Model m)

private def sixL (i : Fin 4) (hi : i ≠ 0) (a : CoefficientField m) : AngularSix.Carrier m :=
  AngularSix.root m (.inl i) (by fin_cases i <;> simp_all [AngularSix.order])
    (PositiveTables.rootChartEquiv m (.inl i) a)
private def sixS (i : Fin 4) (hi : i ≠ 0) (a b : CoefficientField m) : AngularSix.Carrier m :=
  AngularSix.root m (.inr i) (by fin_cases i <;> simp_all [AngularSix.order])
    (PositiveTables.rootChartEquiv m (.inr i) (a,b))
private theorem evalL (i : Fin 4) (hi : i ≠ 0) (a : CoefficientField m) :
    angularSixEval Q split c (sixL i hi a) = L i a := by
  rw [sixL,angularSixEval_root,synchronizedSourceRoot_field]
private theorem evalS (i : Fin 4) (hi : i ≠ 0) (a b : CoefficientField m) :
    angularSixEval Q split c (sixS i hi a b) = S i a b := by
  rw [sixS,angularSixEval_root,synchronizedSourceRoot_field]
private theorem six_eval_injective : Function.Injective (angularSixEval Q split c) := by
  intro a b he
  simp only [angularSixEval,MonoidHom.comp_apply] at he
  have he' : AngularSix.inclusion m a = AngularSix.inclusion m b :=
    (angularSuffixEval_injective Q split c) he
  exact Subgroup.inclusion_injective (AngularSix.le_suffix m) he'
private theorem six_eval_mem (a : AngularSix.Carrier m) :
    angularSixEval Q split c a ∈ simpleRemainder Q split 1 :=
  angularSuffixEval_mem_remainder Q split c (AngularSix.inclusion m a)
private theorem simple_suzuki (a b : CoefficientField m) :
    S 0 a b = (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) := by
  rw [synchronizedPositivePoint_quartet_word]
  simp only [positiveWord,Matrix.cons_val_zero,map_one,inv_one,one_mul,mul_one]
private theorem pair_inv (i : Fin 4) (a : CoefficientField m) : (L i a)⁻¹ = L i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_pair_mul]
  simp only [CharTwo.add_self_eq_zero,synchronizedPositivePoint_pair_zero]
private theorem quartet_inv (i : Fin 4) (a b : CoefficientField m) :
    (S i a b)⁻¹ = S i a (b+titsEnd m a*a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_quartet_mul]
  have he : b+(b+titsEnd m a*a)+titsEnd m a*a = 0 := by
    rw [←add_assoc b b,CharTwo.add_self_eq_zero,zero_add,CharTwo.add_self_eq_zero]
  simp only [he,CharTwo.add_self_eq_zero,synchronizedPositivePoint_quartet_zero]
private theorem pair_reflection (s : Bool) (i : Fin 4)
    (h : (step false s (true,i)).1 = true) (a : CoefficientField m) :
    MulAut.conj (W s) (L i a) = L (next false s i) a := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) false s (true,i)
    (synchronizedLinearChart Q split c (.ofAdd a) : X ⧸ Q.D)
    (synchronizedLinear_perpendicularReflection Q split c a)
  rw [show step false s (true,i) = (true,next false s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord,Bool.false_eq_true,Bool.true_eq_false,
    ↓reduceIte,mul_one,synchronizedWeylPoint_simple,←synchronizedPositivePoint_pair_word,
    MulAut.conj_apply] using hh
private theorem quartet_reflection (s : Bool) (i : Fin 4)
    (h : (step true s (true,i)).1 = true) (a b : CoefficientField m) :
    MulAut.conj (W s) (S i a b) = S (next true s i) a b := by
  have hh := signedWordPoint_reflection (synchronizedWeylPoint Q split c) true s (true,i)
    (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)
    (synchronizedSuzuki_perpendicularReflection Q split c a b)
  rw [show step true s (true,i) = (true,next true s i) from Prod.ext h rfl] at hh
  simpa only [signedWordPoint,signedRootWord,↓reduceIte,mul_one,synchronizedWeylPoint_simple,
    ←synchronizedPositivePoint_quartet_word,MulAut.conj_apply] using hh

private def sixK (r s e t v w : CoefficientField m) : AngularSix.Carrier m :=
  sixS 2 (by decide) 1 r * sixL 2 (by decide) s * sixS 1 (by decide) e t *
    sixL 3 (by decide) v * sixS 3 (by decide) 1 w * sixL 1 (by decide) 1
private def sixV (s e t v w : CoefficientField m) : AngularSix.Carrier m :=
  sixS 2 (by decide) 1 0 * sixL 2 (by decide) 1 * sixS 1 (by decide) 1 (w+1) *
    sixL 3 (by decide) v * sixS 3 (by decide) e (t+titsEnd m e*e) * sixL 1 (by decide) s

private theorem reflected_seed (r s e t v w : CoefficientField m)
    (hk : (L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 =
      S 2 1 r * L 2 s * S 1 e t * L 3 v * S 3 1 w * L 1 1) :
    angularSixEval Q split c (sixV s e t v w) * S 0 1 (r+1) =
      S 0 1 0 * (angularSixEval Q split c (sixK r s e t v w))⁻¹ := by
  have hk' : angularSixEval Q split c (sixK r s e t v w) =
      (L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 := by
    simpa only [sixK,map_mul,evalL,evalS] using hk.symm
  have hC : S 0 1 0 * (angularSixEval Q split c (sixK r s e t v w))⁻¹ =
      L 0 1 * S 0 1 0 * L 0 1 := by
    rw [hk']
    simp only [mul_inv_rev,inv_inv,pair_inv]
    group
  have hf := synchronizedSuzukiLinear_linear_braid_fixed Q split c 1 0
  rw [←hC] at hf
  simp only [sixK,map_mul,evalL,evalS,mul_inv_rev,pair_inv,quartet_inv,
    map_one,mul_one] at hf
  simp only [quartet_reflection Q split c false 0 (by decide),
    quartet_reflection Q split c false 1 (by decide),
    quartet_reflection Q split c false 2 (by decide),
    quartet_reflection Q split c false 3 (by decide),
    pair_reflection Q split c false 1 (by decide),
    pair_reflection Q split c false 2 (by decide),
    pair_reflection Q split c false 3 (by decide),next,Matrix.cons_val,Fin.isValue] at hf
  simpa only [sixV,sixK,map_mul,evalL,evalS,mul_inv_rev,pair_inv,quartet_inv,
    map_one,mul_one,one_mul,mul_assoc] using hf

private theorem seed_first_coefficient (r s e t v w : CoefficientField m)
    (hk : (L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 =
      S 2 1 r * L 2 s * S 1 e t * L 3 v * S 3 1 w * L 1 1) : r = 1 := by
  let u := PositiveTables.rootChartEquiv m (.inr 0) (1,0)
  let A := angularSixEval Q split c (sixV s e t v w)
  let B := angularSixEval Q split c (AngularSix.firstAction m u (sixK r s e t v w)⁻¹)
  have hB : B = S 0 1 0 * (angularSixEval Q split c (sixK r s e t v w))⁻¹ * (S 0 1 0)⁻¹ := by
    dsimp only [B]
    rw [angularSixEval_firstAction Q split c (synchronized_opposite_main_commutator Q split c),
      map_inv,synchronizedSourceRoot_field]
  have he : A * S 0 1 (r+1) = B * S 0 1 0 := by
    rw [hB,mul_assoc _ _ (S 0 1 0),inv_mul_cancel,mul_one]
    exact reflected_seed Q split c r s e t v w hk
  have hz : S 0 1 (r+1) * (S 0 1 0)⁻¹ ∈ simpleRemainder Q split 1 := by
    have hh := (simpleRemainder Q split 1).mul_mem
      ((simpleRemainder Q split 1).inv_mem (six_eval_mem Q split c (sixV s e t v w)))
      (six_eval_mem Q split c (AngularSix.firstAction m u (sixK r s e t v w)⁻¹))
    have he' : A⁻¹ * B = S 0 1 (r+1) * (S 0 1 0)⁻¹ := by
      calc
        _ = A⁻¹ * (B*S 0 1 0) * (S 0 1 0)⁻¹ := by group
        _ = A⁻¹ * (A*S 0 1 (r+1)) * (S 0 1 0)⁻¹ := by rw [←he]
        _ = _ := by group
    rwa [he'] at hh
  have hzero : S 0 1 (r+1) * (S 0 1 0)⁻¹ = 1 := by
    apply disjoint_def.mp (simpleRoot_disjoint_remainder Q split 1) _ hz
    have hmem (b : CoefficientField m) : S 0 1 b ∈ simpleRoot Q split 1 := by
      rw [simple_suzuki]
      exact (suzukiChart Q split (pinnedInput Q split c) (1,b)).property
    exact (simpleRoot Q split 1).mul_mem (hmem _) ((simpleRoot Q split 1).inv_mem (hmem _))
  have hs : S 0 1 (r+1) = S 0 1 0 := mul_inv_eq_one.mp hzero
  have hc := congrArg Prod.snd ((synchronizedPositiveChart Q split c (.inr 0)).injective
    (Subtype.ext hs))
  have hh : r+1 = 0 := hc
  calc r = (r+1)+1 := by rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]
       _ = 1 := by rw [hh,zero_add]

private theorem seed_native_constraints (s e t v w : CoefficientField m)
    (hk : (L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 =
      S 2 1 1 * L 2 s * S 1 e t * L 3 v * S 3 1 w * L 1 1) :
    let K := NS 2 1 1 * NL 2 s * NS 1 e t * NL 3 v * NS 3 1 w * NL 1 1
    let V := NS 2 1 0 * NL 2 1 * NS 1 1 (w+1) * NL 3 v *
      NS 3 e (t+titsEnd m e*e) * NL 1 s
    V = NS 0 1 0 * K⁻¹ * (NS 0 1 0)⁻¹ ∧
      (NL 0 1 * K)^2 = 1 ∧
      Commute (NL 0 1 * K) ((NS 0 1 0)⁻¹ * NS 2 1 0 * NS 0 1 0) := by
  let u := PositiveTables.rootChartEquiv m (.inr 0) (1,0)
  let k := sixK 1 s e t v w
  let v' := sixV s e t v w
  let x := AngularSuffix.root m (.inl 0) ((AngularSuffix.suffix_member _).mpr (by decide))
    (PositiveTables.rootChartEquiv m (.inl 0) 1)
  let A := x * AngularSix.inclusion m k
  let B := AngularSix.inclusion m (AngularSix.firstAction m u⁻¹ (sixS 2 (by decide) 1 0))
  have hk' : angularSixEval Q split c k =
      (L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 := by
    simpa only [k,sixK,map_mul,evalL,evalS] using hk.symm
  have haction (a : AngularPresentation.Parameter m (.inr 0)) (z : AngularSix.Carrier m) :=
    angularSixEval_firstAction Q split c (synchronized_opposite_main_commutator Q split c) a z
  have hu : synchronizedSourceRoot Q split c (.inr 0) u = S 0 1 0 :=
    synchronizedSourceRoot_field Q split c (.inr 0) (1,0)
  have hxval : angularSuffixEval Q split c x = L 0 1 := by
    rw [show x = AngularSuffix.root m (.inl 0)
      ((AngularSuffix.suffix_member _).mpr (by decide))
      (PositiveTables.rootChartEquiv m (.inl 0) 1) from rfl,
      angularSuffixEval_root,synchronizedSourceRoot_field]
  have hV : v' = AngularSix.firstAction m u k⁻¹ := by
    apply six_eval_injective Q split c
    rw [haction,map_inv,hu]
    have he := reflected_seed Q split c 1 s e t v w hk
    simp only [CharTwo.add_self_eq_zero] at he
    calc
      _ = (angularSixEval Q split c v' * S 0 1 0) * (S 0 1 0)⁻¹ := by group
      _ = _ := by rw [he]
  have hA : angularSuffixEval Q split c A = (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 := by
    change angularSuffixEval Q split c (x * AngularSix.inclusion m k) = _
    rw [map_mul]
    change angularSuffixEval Q split c x * angularSixEval Q split c k = _
    rw [hk']
    rw [hxval]
    group
  have hB : angularSuffixEval Q split c B = (S 0 1 0)⁻¹ * S 2 1 0 * S 0 1 0 := by
    change angularSixEval Q split c (AngularSix.firstAction m u⁻¹ (sixS 2 (by decide) 1 0)) = _
    rw [haction,evalS,map_inv,hu,inv_inv]
  have hsq : A^2 = 1 := by
    apply angularSuffixEval_injective Q split c
    rw [map_pow,hA,map_one]
    have hx : (L 0 1)^2 = 1 := by
      rw [pow_two,synchronizedPositivePoint_pair_mul,CharTwo.add_self_eq_zero,
        synchronizedPositivePoint_pair_zero]
    calc
      _ = (S 0 1 0)⁻¹ * ((L 0 1)^2) * S 0 1 0 := by simp only [pow_two]; group
      _ = 1 := by rw [hx]; group
  have hco : Commute A B := by
    apply (angularSuffixEval_injective Q split c)
    rw [map_mul _ A B,map_mul _ B A,hA,hB]
    have hc := (synchronized_adjacent_commute_family Q split c 1 1 0).2.2.2.2.2.2
    calc
      _ = (S 0 1 0)⁻¹ * (L 0 1 * S 2 1 0) * S 0 1 0 := by group
      _ = (S 0 1 0)⁻¹ * (S 2 1 0 * L 0 1) * S 0 1 0 := by rw [hc.eq]
      _ = _ := by group
  refine ⟨?_,?_,?_⟩
  · exact congrArg (fun z : AngularSix.Carrier m => (z : Model m)) hV
  · exact congrArg (fun z : AngularSuffix.Carrier m => (z : Model m)) hsq
  · exact congrArg (fun z : AngularSuffix.Carrier m => (z : Model m)) hco.eq

/-- The actual source seed supplies all native rigidity premises. -/
theorem synchronizedSuzukiLinear_seed_native_data :
    ∃ s e t v w : CoefficientField m,
      ((L 0 1)⁻¹ * (S 0 1 0)⁻¹ * L 0 1 * S 0 1 0 =
        S 2 1 1 * L 2 s * S 1 e t * L 3 v * S 3 1 w * L 1 1) ∧
      (let K := NS 2 1 1 * NL 2 s * NS 1 e t * NL 3 v * NS 3 1 w * NL 1 1
       let V := NS 2 1 0 * NL 2 1 * NS 1 1 (w+1) * NL 3 v *
         NS 3 e (t+titsEnd m e*e) * NL 1 s
       V = NS 0 1 0 * K⁻¹ * (NS 0 1 0)⁻¹ ∧
         (NL 0 1 * K)^2 = 1 ∧
         Commute (NL 0 1 * K) ((NS 0 1 0)⁻¹ * NS 2 1 0 * NS 0 1 0)) := by
  obtain ⟨r,s,e,t,v,w,hk⟩ := synchronizedSuzukiLinear_seed_support Q split c
  have hr := seed_first_coefficient Q split c r s e t v w hk
  subst r
  exact ⟨s,e,t,v,w,hk,seed_native_constraints Q split c s e t v w hk⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
