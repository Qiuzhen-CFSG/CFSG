module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.FinalConstruction
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.BinaryEndSupportRigidity

/-!
# Source interior relations for binary endpoint rigidity

The seven parameter-one roots satisfy the checked finite word collection table.
The proof uses the established adjacent, short, near and linear commutators,
with inverse Suzuki charts in the two noncentral exchanges. Carter's ordered
coordinates separate the five root coordinates used by the fourth-power test.
These statements hold over every Ree coefficient field; the binary endpoint
consumer supplies the seven Boolean action coefficients.

Source: Fong--Seitz II (1974), Section 10, (10.8)--(10.26), and the literal
native triangular charts.
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


namespace BinaryInterior

def generators : Fin 7 → X ⧸ Q.D := ![L 0 1,S 2 1 0,L 2 1,S 1 1 0,L 3 1,S 3 1 0,L 1 1]

private theorem lsq (i : Fin 4) : L i 1 * L i 1 = 1 := by
  rw [synchronizedPositivePoint_pair_mul,CharTwo.add_self_eq_zero,
    synchronizedPositivePoint_pair_zero]
private theorem ssq (i : Fin 4) : S i 1 0 * S i 1 0 = S i 0 1 := by
  rw [synchronizedPositivePoint_quartet_mul]
  simp only [CharTwo.add_self_eq_zero,zero_add,map_one,mul_one]
private theorem osq (i : Fin 4) : S i 0 1 * S i 0 1 = 1 := by
  rw [synchronizedPositivePoint_quartet_mul]
  simp only [CharTwo.add_self_eq_zero,map_zero,zero_mul,
    synchronizedPositivePoint_quartet_zero]
private theorem sfour (i : Fin 4) : S i 1 0 * (S i 1 0 * (S i 1 0 * S i 1 0)) = 1 := by
  rw [ssq,←mul_assoc,ssq,osq]
private theorem sinv (i : Fin 4) : (S i 1 0)⁻¹ = S i 1 1 := by
  apply inv_eq_of_mul_eq_one_right
  rw [synchronizedPositivePoint_quartet_mul]
  simp only [CharTwo.add_self_eq_zero,zero_add,map_one,mul_one,
    synchronizedPositivePoint_quartet_zero]

private theorem swap_of_conj {G : Type*} [Group G] {a b z : G}
    (h : a*b*a⁻¹ = z*b) (ha : Commute z a) (hb : Commute z b) :
    a*b = b*(a*z) := by
  calc
    _ = (a*b*a⁻¹)*a := by group
    _ = (z*b)*a := by rw [h]
    _ = _ := by rw [hb.eq]; simp only [mul_assoc,ha.eq]

private theorem swap_of_inv_conj {G : Type*} [Group G] {a b z : G}
    (h : b⁻¹*a*b = z*a) (ha : Commute z a) : a*b = b*(a*z) := by
  calc
    _ = b*(b⁻¹*a*b) := by group
    _ = b*(z*a) := by rw [h]
    _ = _ := by rw [ha.eq]

private theorem reverse_swap_of_inv_conj {G : Type*} [Group G] {a b z : G}
    (h : a⁻¹*b*a = z*b) (hb : Commute z b) (hz : z*z=1) : a*b = b*(a*z) := by
  have hs := swap_of_inv_conj h hb
  calc
    _ = (a*b)*(z*z) := by rw [hz,mul_one]
    _ = (a*(b*z))*z := by group
    _ = _ := by rw [←hs]; group

/-- The literal source root generators satisfy the finite word-rewrite table. -/
theorem rules_valid (i : Fin 28) :
    Theory.GroupTheory.evalWord (generators Q split c) (BinaryEndRigidity.rules i).lhs =
      Theory.GroupTheory.evalWord (generators Q split c) (BinaryEndRigidity.rules i).rhs := by
  have ha := synchronized_adjacent_commute_family Q split c 1 1 0
  have hao := synchronized_adjacent_commute_family Q split c 1 0 1
  have hl := synchronized_linear_commute_family Q split c 1 1
  have hs := synchronized_suzuki_commute_family Q split c 1 0 1 0
  fin_cases i <;> simp only [BinaryEndRigidity.rules,Matrix.cons_val,Fin.isValue,Fin.reduceFinMk,
    Theory.GroupTheory.evalWord,generators,mul_one]
  · exact lsq Q split c 0
  · exact sfour Q split c 2
  · exact lsq Q split c 2
  · exact sfour Q split c 1
  · exact lsq Q split c 3
  · exact sfour Q split c 3
  · exact lsq Q split c 1
  · exact ha.2.2.2.2.2.2.symm.eq
  · exact hl.2.2.2.2.eq
  · exact ha.2.2.2.2.2.1.eq
  · rw [ssq]
    apply swap_of_conj
    · simpa only [one_mul] using synchronized_short_terminal_conjugate Q split c 1 0 1
    · apply Commute.symm
      apply (commute_iff_eq _ _).mpr
      have h := synchronized_nearSuzuki_terminal_conjugate Q split c 1 0 0 1
      simp only [mul_zero,synchronizedPositivePoint_pair_zero,one_mul] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    · exact hao.2.2.2.2.2.2.symm
  · apply swap_of_conj
    · simpa only [one_mul] using synchronized_nearSuzuki_terminal_conjugate Q split c 1 0 1 0
    · exact ha.2.2.2.2.1
    · exact ha.2.2.2.2.2.1
  · exact ha.2.2.2.2.1.symm.eq
  · exact hl.2.2.2.1.eq
  · rw [ssq]
    apply swap_of_conj
    · simpa only [one_mul] using synchronized_short_reflected_conjugate Q split c 1 0 1
    · exact hao.2.2.2.1.symm
    · have h := synchronized_nearSuzuki_terminal_conjugate Q split c 0 1 1 0
      simp only [zero_mul,synchronizedPositivePoint_pair_zero,one_mul] at h
      exact (commute_iff_eq _ _).mpr (mul_inv_eq_iff_eq_mul.mp h)
  · exact hl.2.2.1.eq
  · exact ha.2.2.2.1.eq
  · rw [ssq]
    apply reverse_swap_of_inv_conj
    · rw [sinv]
      have h := synchronized_next_shifted_conjugate Q split c 1 1 1
      have hinv : (S 3 1 1)⁻¹ = S 3 1 0 := (inv_eq_iff_eq_inv.mpr (sinv Q split c 3).symm)
      rw [hinv] at h
      simpa only [map_one,mul_one,CharTwo.add_self_eq_zero,
        synchronizedPositivePoint_quartet_zero,one_mul,mul_assoc] using h
    · exact hl.2.2.2.2.mul_left hao.2.2.2.2.2.2.symm
    · rw [mul_assoc,hao.2.2.2.2.2.1.symm.left_comm,←mul_assoc,lsq,one_mul,osq]
  · exact hs.2.eq
  · rw [ssq]
    apply swap_of_conj
    · simpa only [one_mul] using synchronized_short_shifted_conjugate Q split c 1 0 1
    · apply Commute.symm
      have h := synchronized_nearSuzuki_middle_conjugate Q split c 1 0 0 1
      simp only [mul_zero,synchronizedPositivePoint_pair_zero,one_mul] at h
      exact (commute_iff_eq _ _).mpr (mul_inv_eq_iff_eq_mul.mp h)
    · exact hao.2.2.2.2.1.symm
  · apply swap_of_conj
    · simpa only [one_mul] using synchronized_nearSuzuki_middle_conjugate Q split c 1 0 1 0
    · exact ha.2.2.1
    · exact ha.2.2.2.1
  · exact ha.2.2.1.symm.eq
  · apply swap_of_conj
    · simpa only [map_one,mul_one,mul_assoc] using synchronized_last_linear_conjugate Q split c 1 1
    · exact hl.1.symm.mul_left hl.2.1.symm
    · exact hl.2.2.2.1.mul_left hl.2.2.2.2
  · rw [ssq]
    have h := synchronized_next_reflected_conjugate Q split c 1 1 1
    have hinv : (S 2 1 1)⁻¹ = S 2 1 0 :=
      inv_eq_iff_eq_inv.mpr (sinv Q split c 2).symm
    have hi := congrArg Inv.inv h
    rw [mul_inv_rev,mul_inv_rev,inv_inv,hinv] at hi
    have linv3 : (L 3 1)⁻¹ = L 3 1 := inv_eq_of_mul_eq_one_right (lsq Q split c 3)
    have oinv : (S 3 0 1)⁻¹ = S 3 0 1 := inv_eq_of_mul_eq_one_right (osq Q split c 3)
    simp only [map_one,mul_one,CharTwo.add_self_eq_zero,
      synchronizedPositivePoint_quartet_zero,mul_one,mul_inv_rev,linv3,oinv,hinv] at hi
    have hh := congrArg (· * L 1 1) hi
    simp only [mul_assoc,inv_mul_cancel,mul_one] at hh
    exact hh.trans (by
      rw [hao.2.1.symm.eq,hl.1.symm.left_comm])
  · exact hl.2.1.eq
  · rw [ssq]
    apply swap_of_conj
    · simpa only [one_mul] using synchronized_short_perpendicular_conjugate Q split c 1 0 1
    · exact hao.2.1.symm
    · have h := synchronized_nearSuzuki_middle_conjugate Q split c 0 1 1 0
      simp only [zero_mul,synchronizedPositivePoint_pair_zero,one_mul] at h
      exact (commute_iff_eq _ _).mpr (mul_inv_eq_iff_eq_mul.mp h)
  · exact hl.1.eq
  · exact ha.2.1.eq


private def bit (b : Bool) : CoefficientField m := if b then 1 else 0
private def label (k : Fin 4) : CoefficientField m × CoefficientField m :=
  ![(0,0),(1,0),(0,1),(1,1)] k

private theorem bit_injective : Function.Injective (bit (m := m)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]
private theorem label_injective : Function.Injective (label (m := m)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp_all [label,Matrix.cons_val,Fin.reduceFinMk]

private theorem power_label (i : Fin 4) (k : Fin 4) :
    (S i 1 0)^k.val = S i (label (m := m) k).1 (label (m := m) k).2 := by
  fin_cases k <;> simp [label,Fin.reduceFinMk,pow_succ,
    synchronizedPositivePoint_quartet_mul,CharTwo.add_self_eq_zero]

private theorem eval_replicate {G : Type*} [Group G] (g : Fin 7 → G)
    (i : Fin 7) (k : ℕ) : evalWord g (List.replicate k i) = (g i)^k := by
  induction k with
  | zero => simp only [List.replicate_zero,evalWord,pow_zero]
  | succ k ih => simp only [List.replicate_succ,evalWord,ih,pow_succ']

private theorem normalWord_value (p : BinaryEndSupportRigidity.Coordinates) :
    evalWord (generators Q split c) (BinaryEndSupportRigidity.normalWord p) =
      S 2 (label (m := m) p.1).1 (label (m := m) p.1).2 *
      L 2 (bit (m := m) p.2.1) *
      S 1 (label (m := m) p.2.2.1).1 (label (m := m) p.2.2.1).2 *
      L 3 (bit (m := m) p.2.2.2.1) *
      S 3 (label (m := m) p.2.2.2.2).1 (label (m := m) p.2.2.2.2).2 := by
  rcases p with ⟨a,b,d,e,f⟩
  simp only [BinaryEndSupportRigidity.normalWord,evalWord_append,eval_replicate]
  simp only [generators,Matrix.cons_val,power_label]
  cases b <;> cases e <;>
    simp [bit,evalWord,Matrix.cons_val,mul_assoc]

private theorem five_unique
    (a b d e f a' b' d' e' f' : CoefficientField m × CoefficientField m)
    (he : S 2 a.1 a.2 * L 2 b.1 * S 1 d.1 d.2 * L 3 e.1 * S 3 f.1 f.2 =
      S 2 a'.1 a'.2 * L 2 b'.1 * S 1 d'.1 d'.2 * L 3 e'.1 * S 3 f'.1 f'.2) :
    a = a' ∧ b.1 = b'.1 ∧ d = d' ∧ e.1 = e'.1 ∧ f = f' := by
  have hh := linearProduct_injective Q split c
    (a₁ := (synchronizedPositiveChart Q split c (.inr 2) a,
      synchronizedPositiveChart Q split c (.inl 2) b.1,
      synchronizedPositiveChart Q split c (.inr 1) d,
      synchronizedPositiveChart Q split c (.inl 3) e.1,
      synchronizedPositiveChart Q split c (.inr 3) f,1,1,PUnit.unit))
    (a₂ := (synchronizedPositiveChart Q split c (.inr 2) a',
      synchronizedPositiveChart Q split c (.inl 2) b'.1,
      synchronizedPositiveChart Q split c (.inr 1) d',
      synchronizedPositiveChart Q split c (.inl 3) e'.1,
      synchronizedPositiveChart Q split c (.inr 3) f',1,1,PUnit.unit)) (by
        change S 2 a.1 a.2 * (L 2 b.1 * (S 1 d.1 d.2 *
          (L 3 e.1 * (S 3 f.1 f.2 * (1*(1*1)))))) =
          S 2 a'.1 a'.2 * (L 2 b'.1 * (S 1 d'.1 d'.2 *
          (L 3 e'.1 * (S 3 f'.1 f'.2 * (1*(1*1))))))
        simpa only [mul_one,mul_assoc] using he)
  exact ⟨(synchronizedPositiveChart Q split c (.inr 2)).injective (congrArg Prod.fst hh),
    (synchronizedPositiveChart Q split c (.inl 2)).injective (congrArg (fun p => p.2.1) hh),
    (synchronizedPositiveChart Q split c (.inr 1)).injective (congrArg (fun p => p.2.2.1) hh),
    (synchronizedPositiveChart Q split c (.inl 3)).injective (congrArg (fun p => p.2.2.2.1) hh),
    (synchronizedPositiveChart Q split c (.inr 3)).injective (congrArg (fun p => p.2.2.2.2.1) hh)⟩

/-- Carter uniqueness separates the five finite coordinates tested by the certificate. -/
theorem coordinates_injective : Function.Injective (fun p : BinaryEndSupportRigidity.Coordinates =>
    evalWord (generators Q split c) (BinaryEndSupportRigidity.normalWord p)) := by
  rintro ⟨a,b,d,e,f⟩ ⟨a',b',d',e',f'⟩ h
  dsimp only at h
  rw [normalWord_value,normalWord_value] at h
  obtain ⟨ha,hb,hd,he,hf⟩ := five_unique Q split c
    (label a) (bit b,0) (label d) (bit e,0) (label f)
    (label a') (bit b',0) (label d') (bit e',0) (label f') h
  have ha := label_injective ha
  have hb := bit_injective hb
  have hd := label_injective hd
  have he := bit_injective he
  have hf := label_injective hf
  subst a'; subst b'; subst d'; subst e'; subst f'
  rfl

end BinaryInterior
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
