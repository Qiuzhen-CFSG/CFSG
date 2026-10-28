module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CommonField

/-!
# The unit coefficient of the source middle pairing

The common-field calculation gives DC = κ σ(dc), where κ is nonzero.
Its unit slice is therefore injective. This removes the possible C coordinate
from [F(1),D(1)] by involutivity. Applying the short rank-one cubic and reducing
modulo the actual long parabolic radical fixes the B coordinate to κ. Long
reflection gives the same A coordinate.

The same cubic now determines F(1)'s action on E(κ). Its square is one, because
E(κ) is an involution. Collecting this square with the actual EB and DC equations
gives A(κ²+κ)=1. Injectivity and κ≠0 force κ=1. Thus the actual DC coefficient
is σ(dc) for one field automorphism, for every finite characteristic-two field,
including q=2 and q=4 and either orientation.

This is a calculation toward compatible whole-pinning labels, not an assertion
that independent local labels already agree. CommonFieldPinning applies σ to
the entire long rank-one pinning. The full-relation and marked-comparison
transport remains necessary before source recognition is complete.

Source: Fong--Seitz II (9.13)--(9.14), printed pp.215--216. The argument
replaces the unit-normalization part of the tensor-module calculation by actual
rank-one words, radical coordinates and the consumer's left commutators.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (hm : rotationOrder Q = 6)

  (hne : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ ≠ ⊥)

local notation "g" => middleCoefficient Q split hK μ n short hm
local notation "κ" => middleCoefficient Q split hK μ n short hm 1 1

private theorem root_mem (i : Fin 6) (a : F) :
    (alignedSourceRoots Q split hK μ n short).x i a ∈ positiveCarrier Q split short i := by
  rw [← alignedSourceRoots_range Q split hK μ n short i]
  exact ⟨.ofAdd a,rfl⟩

private theorem root_inj (i : Fin 6) :
    Function.Injective ((alignedSourceRoots Q split hK μ n short).x i) :=
  (alignedSourceRoots_injective Q split hK μ n short i).comp Multiplicative.ofAdd.injective

include hm hne in
/-- Every unit slice of the actual middle coefficient is injective. -/
theorem middleCoefficient_one_injective : Function.Injective (g 1) := by
  obtain ⟨k,σ,hk,hσ⟩ := exists_middleCoefficient_field_equiv Q split hK μ n short hm hne
  intro c d he
  rw [hσ,hσ,one_mul,one_mul] at he
  exact σ.injective (mul_left_cancel₀ hk he)

include hm hne in
/-- The unit coefficient is nonzero before proving its value is one. -/
theorem middleCoefficient_one_ne_zero : κ ≠ 0 := by
  intro hz
  apply (one_ne_zero : (1 : F) ≠ 0)
  apply middleCoefficient_one_injective Q split hK μ n short hm hne
  simpa only [middleCoefficient_zero_right] using hz

include hm hne in
/-- Long-reflection transport of the unnormalized actual middle coefficient. -/
theorem aligned_fc_action_of_pairing (z c : F) :
    MulAut.conj ((alignedSourceRoots Q split hK μ n short).x 5 z)
      ((alignedSourceRoots Q split hK μ n short).x 2 c) =
        (alignedSourceRoots Q split hK μ n short).x 1 (g z c) *
          (alignedSourceRoots Q split hK μ n short).x 2 c := by
  let L := alignedSourceRoots Q split hK μ n short
  let r : X ⧸ Q.D := (n (1-short)).val
  have R := aligned_commuting_of_middle_pairing_ne_bot Q split hK μ n short hm hne
  have hrD (v : F) : MulAut.conj r (L.x 3 v) = L.x 5 v :=
    sourceBorelWeyl_rD Q split hK μ n short split.abelian v
  have hrC (v : F) : MulAut.conj r (L.x 2 v) = L.x 2 v :=
    sourceBorelWeyl_rC Q split hK μ n short split.abelian hm R v
  have hrA (v : F) : MulAut.conj r (L.x 0 v) = L.x 1 v :=
    sourceBorelWeyl_rA Q split hK μ n short split.abelian v
  have he := congrArg (MulAut.conj r) (middleCoefficient_spec Q split hK μ n short hm z c)
  rw [map_commutatorElement,hrD,hrC,hrA] at he
  have hh := congrArg (fun v : X ⧸ Q.D => v*L.x 2 c) he
  simpa only [MulAut.conj_apply,commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh

include hm hne in
/-- The unit FD commutator lies in AB: its possible C coordinate is killed
by involutivity and the actual FC action. -/
private theorem fd_unit_mem_of_pairing : ∃ a b : F,
    ⁅(alignedSourceRoots Q split hK μ n short).x 5 1,
      (alignedSourceRoots Q split hK μ n short).x 3 1⁆ =
        (alignedSourceRoots Q split hK μ n short).x 0 a *
          (alignedSourceRoots Q split hK μ n short).x 1 b := by
  let L := alignedSourceRoots Q split hK μ n short
  let R : L.CommutingRelations := aligned_commuting_of_middle_pairing_ne_bot Q split hK μ n short hm hne
  have hij : short ≠ 1-short := by fin_cases short <;> decide
  have hF : L.x 5 1 ∈ simpleRemainder Q split (1-short) :=
    simpleRoot_le_other_remainder Q split hm short (1-short) hij
      (root_mem Q split hK μ n short 5 1)
  have hD : L.x 3 1 ∈ simpleRemainder Q split (1-short) :=
    (exchanged_roots_le_remainder Q split hm short (1-short) hij).1
      (root_mem Q split hK μ n short 3 1)
  have hx := radical_commutator_le_middle_of_linear Q split hm short (1-short) hij
    (hK short) (μ short) (commutator_mem_commutator hF hD)
  change ⁅L.x 5 1,L.x 3 1⁆ ∈ (middleRoots Q split short (1-short) : Set (X ⧸ Q.D)) at hx
  rw [middleRoots_product Q split hm short (1-short) hij] at hx
  obtain ⟨bc,⟨b,hb,c,hc,rfl⟩,a,ha,hx⟩ := hx
  change b ∈ positiveCarrier Q split short 1 at hb
  change c ∈ positiveCarrier Q split short 2 at hc
  change a ∈ positiveCarrier Q split short 0 at ha
  rw [← alignedSourceRoots_range Q split hK μ n short 1] at hb
  rw [← alignedSourceRoots_range Q split hK μ n short 2] at hc
  rw [← alignedSourceRoots_range Q split hK μ n short 0] at ha
  obtain ⟨b,rfl⟩ := hb
  obtain ⟨c,rfl⟩ := hc
  obtain ⟨a,rfl⟩ := ha
  have he : ⁅L.x 5 1,L.x 3 1⁆ = L.x 0 a.toAdd * L.x 1 b.toAdd * L.x 2 c.toAdd := by
    change L.x 1 b.toAdd * L.x 2 c.toAdd * L.x 0 a.toAdd = ⁅L.x 5 1,L.x 3 1⁆ at hx
    rw [mul_assoc,R.ca,← mul_assoc,R.ba] at hx
    exact hx.symm
  have hInv : ⁅L.x 5 1,L.x 3 1⁆⁻¹ = ⁅L.x 5 1,L.x 3 1⁆ := by
    rw [he]
    simp only [mul_inv_rev,root_inv]
    rw [← mul_assoc,R.cb,mul_assoc,R.ca,← mul_assoc,R.ba]
  have hfix : MulAut.conj (L.x 5 1) ⁅L.x 5 1,L.x 3 1⁆ = ⁅L.x 5 1,L.x 3 1⁆ := by
    calc
      _ = ⁅L.x 5 1,L.x 3 1⁆⁻¹ := by
        simp only [MulAut.conj_apply,commutatorElement_def,mul_inv_rev,root_inv]
        group
        rw [← L.x_add,CharTwo.add_self_eq_zero,L.x_zero,one_mul]
      _ = _ := hInv
  have hFA (a : F) : MulAut.conj (L.x 5 1) (L.x 0 a) = L.x 0 a := by
    change L.x 5 1 * L.x 0 a * (L.x 5 1)⁻¹ = _
    rw [R.fa,mul_assoc,mul_inv_cancel,mul_one]
  have hFB (b : F) : MulAut.conj (L.x 5 1) (L.x 1 b) = L.x 1 b := by
    change L.x 5 1 * L.x 1 b * (L.x 5 1)⁻¹ = _
    rw [R.fb,mul_assoc,mul_inv_cancel,mul_one]
  have hFC : MulAut.conj (L.x 5 1) (L.x 2 c.toAdd) = L.x 1 (g 1 c.toAdd) * L.x 2 c.toAdd :=
    aligned_fc_action_of_pairing Q split hK μ n short hm hne 1 c.toAdd
  rw [he,map_mul,map_mul,hFA,hFB,hFC] at hfix
  have hc0 : c.toAdd = 0 := by
    apply middleCoefficient_one_injective Q split hK μ n short hm hne
    rw [middleCoefficient_zero_right]
    apply root_inj Q split hK μ n short 1
    rw [L.x_zero]
    have hh := mul_left_cancel hfix
    exact mul_right_cancel (hh.trans (one_mul _).symm)
  exact ⟨a.toAdd,b.toAdd,by simpa only [hc0,L.x_zero,mul_one] using he⟩



include hm hne in
private theorem pairing_cubic_constraint (a b d : F)
    (hab : MulAut.conj ((alignedSourceRoots Q split hK μ n short).x 5 1)
      ((alignedSourceRoots Q split hK μ n short).x 3 d) =
        (alignedSourceRoots Q split hK μ n short).x 0 a *
          (alignedSourceRoots Q split hK μ n short).x 1 b *
            (alignedSourceRoots Q split hK μ n short).x 3 d) :
    (alignedSourceRoots Q split hK μ n short).x 0 a *
      MulAut.conj ((alignedSourceRoots Q split hK μ n short).x 5 1)
        ((alignedSourceRoots Q split hK μ n short).x 4 b) *
      ((alignedSourceRoots Q split hK μ n short).x 1 (g 1 d) *
        (alignedSourceRoots Q split hK μ n short).x 2 d) =
      (alignedSourceRoots Q split hK μ n short).x 4 (g 1 d) *
        (alignedSourceRoots Q split hK μ n short).x 3 d := by
  let L := alignedSourceRoots Q split hK μ n short
  let R : L.CommutingRelations := aligned_commuting_of_middle_pairing_ne_bot Q split hK μ n short hm hne
  let s : X ⧸ Q.D := (n short).val
  let f := MulAut.conj (L.x 5 1)
  let w := MulAut.conj s
  let t := MulAut.conj (L.x 5 1*s)
  have hFD : f (L.x 3 d) = L.x 0 a * L.x 1 b * L.x 3 d := hab
  have hFC : f (L.x 2 d) = L.x 1 (g 1 d) * L.x 2 d :=
    aligned_fc_action_of_pairing Q split hK μ n short hm hne 1 d
  have hsA (c : F) : w (L.x 0 c) = L.x 0 c :=
    sourceBorelWeyl_sA Q split hK μ n short split.abelian hm R c
  have hsB (c : F) : w (L.x 1 c) = L.x 4 c :=
    sourceBorelWeyl_sB Q split hK μ n short split.abelian c
  have hsC (c : F) : w (L.x 2 c) = L.x 3 c :=
    sourceBorelWeyl_sC Q split hK μ n short split.abelian c
  have hsD (c : F) : w (L.x 3 c) = L.x 2 c :=
    sourceBorelWeyl_sD Q split hK μ n short split.abelian c
  have hFA (c : F) : f (L.x 0 c) = L.x 0 c := by
    change L.x 5 1 * L.x 0 c * (L.x 5 1)⁻¹ = _
    rw [R.fa,mul_assoc,mul_inv_cancel,mul_one]
  have ht (x : X ⧸ Q.D) : t x = f (w x) := by
    change MulAut.conj (L.x 5 1*s) x = _
    rw [map_mul,MulAut.mul_apply]
  have hcube : (L.x 5 1*s)^3 = 1 := by
    let φ := alignedPinningHom Q split short (hK short) (μ short) (n short)
    have hh : (Theory.PSL2.SemilinearCoverage.uni (1 : F) *
        Theory.PSL2.SemilinearCoverage.weyl F)^3 = 1 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pow_succ,Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
    have he := congrArg φ hh
    change (φ (Theory.PSL2.SemilinearCoverage.uni 1) * ((n short).val : X ⧸ Q.D))^3 = 1
    simpa only [map_pow,map_mul,map_one,φ,alignedPinningHom_weyl] using he
  have hpow : (L.x 5 1*s)^2 = (L.x 5 1*s)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [pow_succ] using hcube
  have hsInv : s⁻¹ = s := inv_eq_of_mul_eq_one_right
    (sourceReflection_sq Q split short (hK short) (μ short) (n short))
  have he : L.x 0 a * f (L.x 4 b) * (L.x 1 (g 1 d) * L.x 2 d) = L.x 4 (g 1 d) * L.x 3 d := by
    calc
      _ = t (t (L.x 2 d)) := by
        rw [ht (L.x 2 d),hsC,hFD,ht]
        simp only [map_mul,hsA,hsB,hsD,hFA,hFC]
      _ = MulAut.conj ((L.x 5 1*s)^2) (L.x 2 d) := by
        rw [pow_two,map_mul,MulAut.mul_apply]
      _ = MulAut.conj ((L.x 5 1*s)⁻¹) (L.x 2 d) := by rw [hpow]
      _ = _ := by
        rw [mul_inv_rev,hsInv,root_inv,map_mul,MulAut.mul_apply]
        change w (f (L.x 2 d)) = _
        rw [hFC,map_mul,hsB,hsC]
  exact he

include hm hne in
private theorem pairing_fd_unit_b (a b : F)
    (hab : ⁅(alignedSourceRoots Q split hK μ n short).x 5 1,
      (alignedSourceRoots Q split hK μ n short).x 3 1⁆ =
        (alignedSourceRoots Q split hK μ n short).x 0 a *
          (alignedSourceRoots Q split hK μ n short).x 1 b) : b = κ := by
  let L := alignedSourceRoots Q split hK μ n short
  change ⁅L.x 5 1,L.x 3 1⁆ = L.x 0 a * L.x 1 b at hab
  have hFD : MulAut.conj (L.x 5 1) (L.x 3 1) = L.x 0 a * L.x 1 b * L.x 3 1 := by
    have hh := congrArg (fun v : X ⧸ Q.D => v*L.x 3 1) hab
    simpa only [MulAut.conj_apply,commutatorElement_def,mul_assoc,
      inv_mul_cancel,mul_one] using hh
  have he := pairing_cubic_constraint Q split hK μ n short hm hne a b 1 hFD
  change L.x 0 a * MulAut.conj (L.x 5 1) (L.x 4 b) * (L.x 1 κ * L.x 2 1) =
    L.x 4 κ * L.x 3 1 at he
  let V := simpleRemainder Q split (1-short)
  have hij : short ≠ 1-short := by fin_cases short <;> decide
  have hM : middleRoots Q split short (1-short) ≤ V :=
    middleRoots_le_remainder Q split hm short (1-short) hij
  have hA : L.x 0 a ∈ V := hM ((show positiveCarrier Q split short 0 ≤ middleRoots Q split short (1-short) from le_sup_right) (root_mem Q split hK μ n short 0 a))
  have hB : L.x 1 κ ∈ V :=
    hM ((show positiveCarrier Q split short 1 ≤ middleRoots Q split short (1-short) from le_sup_left.trans le_sup_left) (root_mem Q split hK μ n short 1 κ))
  have hC : L.x 2 1 ∈ V :=
    hM ((show positiveCarrier Q split short 2 ≤ middleRoots Q split short (1-short) from le_sup_right.trans le_sup_left) (root_mem Q split hK μ n short 2 1))
  have hD : L.x 3 1 ∈ V :=
    (exchanged_roots_le_remainder Q split hm short (1-short) hij).1
      (root_mem Q split hK μ n short 3 1)
  have hF : L.x 5 1 ∈ V :=
    simpleRoot_le_other_remainder Q split hm short (1-short) hij
      (root_mem Q split hK μ n short 5 1)
  have hEN : L.x 4 κ ∈ normalizer (V : Set (X ⧸ Q.D)) :=
    remainder_parabolic_normalizes Q split (1-short) (hK (1-short))
      ((split.U_le.trans (Q.tits.B_le_standardParabolic _))
        ((simpleRoot_le Q split (1-short)) (root_mem Q split hK μ n short 4 κ)))
  have hsolve : L.x 4 b * (L.x 4 κ)⁻¹ =
      (L.x 5 1)⁻¹ * (L.x 0 a)⁻¹ *
        (L.x 4 κ * (L.x 3 1 * (L.x 1 κ * L.x 2 1)⁻¹ * L.x 5 1) * (L.x 4 κ)⁻¹) := by
    have hh := congrArg (fun v : X ⧸ Q.D =>
      (L.x 5 1)⁻¹ * (L.x 0 a)⁻¹ * v * (L.x 1 κ * L.x 2 1)⁻¹ * L.x 5 1 * (L.x 4 κ)⁻¹) he
    change _ * _ * (L.x 0 a * (L.x 5 1*L.x 4 b*(L.x 5 1)⁻¹) * _) * _ * _ * _ = _ at hh
    simpa only [mul_assoc,mul_inv_rev,inv_mul_cancel_left,mul_inv_cancel_left,
      inv_mul_cancel,mul_inv_cancel,mul_one,one_mul] using hh
  have hV : L.x 4 b * (L.x 4 κ)⁻¹ ∈ V := by
    rw [hsolve]
    exact V.mul_mem (V.mul_mem (V.inv_mem hF) (V.inv_mem hA))
      ((mem_normalizer_iff.mp hEN _).mp
        (V.mul_mem (V.mul_mem hD (V.inv_mem (V.mul_mem hB hC))) hF))
  have hroot : L.x 4 b * (L.x 4 κ)⁻¹ ∈ simpleRoot Q split (1-short) :=
    (simpleRoot Q split (1-short)).mul_mem (root_mem Q split hK μ n short 4 b)
      ((simpleRoot Q split (1-short)).inv_mem (root_mem Q split hK μ n short 4 κ))
  have h1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split (1-short)) hroot hV
  exact root_inj Q split hK μ n short 4 (mul_inv_eq_one.mp h1)



include hm hne in
/-- The short cubic and the long reflection fix both unit FD coefficients. -/
private theorem fd_unit_coefficients_of_pairing :
    ⁅(alignedSourceRoots Q split hK μ n short).x 5 1,
      (alignedSourceRoots Q split hK μ n short).x 3 1⁆ =
        (alignedSourceRoots Q split hK μ n short).x 0 κ *
          (alignedSourceRoots Q split hK μ n short).x 1 κ := by
  let L := alignedSourceRoots Q split hK μ n short
  obtain ⟨a,b,hab⟩ := fd_unit_mem_of_pairing Q split hK μ n short hm hne
  have hb := pairing_fd_unit_b Q split hK μ n short hm hne a b hab
  let r : X ⧸ Q.D := (n (1-short)).val
  have hrA (c : F) : MulAut.conj r (L.x 0 c) = L.x 1 c :=
    sourceBorelWeyl_rA Q split hK μ n short split.abelian c
  have hrB (c : F) : MulAut.conj r (L.x 1 c) = L.x 0 c :=
    sourceBorelWeyl_rB Q split hK μ n short split.abelian c
  have hrD (c : F) : MulAut.conj r (L.x 3 c) = L.x 5 c :=
    sourceBorelWeyl_rD Q split hK μ n short split.abelian c
  have hrF (c : F) : MulAut.conj r (L.x 5 c) = L.x 3 c :=
    sourceBorelWeyl_rF Q split hK μ n short split.abelian c
  change ⁅L.x 5 1,L.x 3 1⁆ = L.x 0 a * L.x 1 b at hab
  have he := congrArg (MulAut.conj r) hab
  simp only [map_commutatorElement,map_mul,hrA,hrB,hrD,hrF] at he
  have he' := congrArg (fun v : X ⧸ Q.D => v⁻¹) he
  simp only [commutatorElement_inv,mul_inv_rev,root_inv] at he'
  have ha := pairing_fd_unit_b Q split hK μ n short hm hne b a he'
  rw [ha,hb] at hab
  exact hab

private theorem append_exchange {Y : Type*} [Group Y] {a b c : Y}
    (h : a*b=c) (z : Y) : a*(b*z)=c*z := by rw [←mul_assoc,h]

private theorem collect_root {K Y : Type*} [Field K] [Group Y]
    (L : PositiveRoots K Y) (i : Fin 6) (a b : K) (z : Y) :
    L.x i a*(L.x i b*z)=L.x i (a+b)*z := by rw [←mul_assoc,←L.x_add]

include hm hne in
/-- The short cubic and involutivity of the long root force the scalar
in the common-field pairing to be one. No exceptional-field exclusion is used. -/
theorem middleCoefficient_one : κ = 1 := by
  let L := alignedSourceRoots Q split hK μ n short
  let R : L.CommutingRelations := aligned_commuting_of_middle_pairing_ne_bot Q split hK μ n short hm hne
  have hfd := fd_unit_coefficients_of_pairing Q split hK μ n short hm hne
  change ⁅L.x 5 1,L.x 3 1⁆ = L.x 0 κ*L.x 1 κ at hfd
  have hFD : MulAut.conj (L.x 5 1) (L.x 3 1) = L.x 0 κ*L.x 1 κ*L.x 3 1 := by
    have hh := congrArg (fun v : X ⧸ Q.D => v*L.x 3 1) hfd
    simpa only [MulAut.conj_apply,commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
  have hcubic := pairing_cubic_constraint Q split hK μ n short hm hne κ κ 1 hFD
  change L.x 0 κ*MulAut.conj (L.x 5 1) (L.x 4 κ)*(L.x 1 κ*L.x 2 1) = L.x 4 κ*L.x 3 1 at hcubic
  have hFE : MulAut.conj (L.x 5 1) (L.x 4 κ) = L.x 0 κ*L.x 4 κ*L.x 3 1*L.x 2 1*L.x 1 κ := by
    have hh : MulAut.conj (L.x 5 1) (L.x 4 κ) =
        (L.x 0 κ)⁻¹*(L.x 4 κ*L.x 3 1)*(L.x 1 κ*L.x 2 1)⁻¹ := by
      calc
        _ = (L.x 0 κ)⁻¹*(L.x 0 κ*MulAut.conj (L.x 5 1) (L.x 4 κ)*
          (L.x 1 κ*L.x 2 1))*(L.x 1 κ*L.x 2 1)⁻¹ := by group
        _ = _ := by rw [hcubic]
    simpa only [mul_assoc,mul_inv_rev,root_inv] using hh
  have hEB := (aligned_long_natural_action_of_pairing Q split hK μ n short hm hne).1 κ κ
  change L.x 4 κ*L.x 1 κ=L.x 0 (κ*κ)*L.x 1 κ*L.x 4 κ at hEB
  have hBE : L.x 1 κ*L.x 4 κ=L.x 0 (κ*κ)*L.x 4 κ*L.x 1 κ := by
    have hh := congrArg (fun v : X ⧸ Q.D => v⁻¹) hEB
    simp only [mul_inv_rev,root_inv] at hh
    rw [R.ba,←mul_assoc,R.ea] at hh
    exact hh
  have hDC : L.x 3 1*L.x 2 1=L.x 0 κ*L.x 2 1*L.x 3 1 := by
    have hh := middleCoefficient_spec Q split hK μ n short hm 1 1
    change ⁅L.x 3 1,L.x 2 1⁆=L.x 0 κ at hh
    rw [←hh]
    simp only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one]
  have hsq : (L.x 0 κ*L.x 4 κ*L.x 3 1*L.x 2 1*L.x 1 κ)^2=L.x 0 (κ*κ+κ) := by
    simp only [pow_two,mul_assoc,
      append_exchange (R.ca _ _),append_exchange (R.da _ _),append_exchange (R.ea _ _),
      append_exchange hBE,append_exchange (R.ec _ _).symm,
      append_exchange (R.ed _ _).symm,append_exchange (R.db _ _).symm,
      append_exchange (R.cb _ _).symm,append_exchange hDC,
      collect_root,CharTwo.add_self_eq_zero,L.x_zero,one_mul]
    rw [←L.x_add,CharTwo.add_self_eq_zero,L.x_zero,mul_one]
  have hsq1 : (L.x 0 κ*L.x 4 κ*L.x 3 1*L.x 2 1*L.x 1 κ)^2=1 := by
    rw [←hFE,←map_pow]
    have he : (L.x 4 κ)^2=1 := by rw [pow_two,←L.x_add,CharTwo.add_self_eq_zero,L.x_zero]
    rw [he,map_one]
  have hzero : κ*κ+κ=0 := root_inj Q split hK μ n short 0
    (hsq.symm.trans (hsq1.trans (L.x_zero 0).symm))
  have hmul : κ*κ=κ := CharTwo.add_eq_zero.mp hzero
  exact mul_left_cancel₀ (middleCoefficient_one_ne_zero Q split hK μ n short hm hne)
    (hmul.trans (mul_one κ).symm)

include hm hne in
/-- A single field automorphism describes the full DC coefficient. The
coefficient has no remaining scalar normalization or small-field premise. -/
theorem exists_middleCoefficient_ringEquiv :
    ∃ σ : F ≃+* F, ∀ d c : F, g d c=σ (d*c) := by
  obtain ⟨k,σ,_,hσ⟩ := exists_middleCoefficient_field_equiv Q split hK μ n short hm hne
  have hk : k=1 := by
    have hh := hσ 1 1
    rw [one_mul,map_one,mul_one,middleCoefficient_one Q split hK μ n short hm hne] at hh
    exact hh.symm
  refine ⟨σ,?_⟩
  intro d c
  simpa only [hk,one_mul] using hσ d c

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
