module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.PairingCartan

/-!
# The short-root radical action from the DC pairing

The normalized DC pairing and the actual rank-one pinnings determine FD
and FE, without a tensor-module classification or further mixed equations.
The commutator of F(1) and D(1) lies in the radical-derived triple BCA.
That triple has exponent two. Conjugation by F(1), using the already
proved FC action, therefore removes its C coordinate.

Apply the short SL₂ cubic to C(1). Reducing the resulting identity modulo
the actual long parabolic radical fixes the B coordinate of [F(1),D(1)]
to one. The long reflection reverses this commutator and exchanges A/B,
so its A coordinate is also one. The actual Cartan weights extend FD to
all parameters. Applying the same cubic to C(e) now determines the whole
FE product at short parameter one, including its highest-root coefficient;
the source torus extends it to every short parameter.

Together with LongRootModule and PairingCartan this supplies every positive
and Borel--Weyl equation from normalized DC alone. No scalar outside {0,1}
is used: q=2 and q=4, and both orientations, are included. In particular no
Thomas recognition or simplicity of the unknown quotient is assumed.
ShortModuleApplication retains the full marked, original and geometric
consumers. Existence of compatible whole-pinning field labels giving DC
from the genuine 6E(a) radicals remains a source obligation; arbitrary
independent local labelings are not asserted to satisfy normalized DC.

Source: Fong--Seitz I (5C), (6E)(a), and II (9.4), (9.13)--(9.21),
printed pp.212,215--217. This direct radical/rank-one-word argument proves
the needed action formulas in the consumer's left-conjugation convention.
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
  (hdc : ∀ d c : F, (alignedSourceRoots Q split hK μ n short).x 3 d *
    (alignedSourceRoots Q split hK μ n short).x 2 c =
      (alignedSourceRoots Q split hK μ n short).x 0 (c*d) *
        (alignedSourceRoots Q split hK μ n short).x 2 c *
          (alignedSourceRoots Q split hK μ n short).x 3 d)

private theorem root_mem (i : Fin 6) (a : F) :
    (alignedSourceRoots Q split hK μ n short).x i a ∈ positiveCarrier Q split short i := by
  rw [← alignedSourceRoots_range Q split hK μ n short i]
  exact ⟨.ofAdd a,rfl⟩

private theorem root_inj (i : Fin 6) :
    Function.Injective ((alignedSourceRoots Q split hK μ n short).x i) :=
  (alignedSourceRoots_injective Q split hK μ n short i).comp Multiplicative.ofAdd.injective

include hm hdc in
/-- The unit FD commutator lies in AB: its possible C coordinate is killed
by involutivity and the actual FC action. -/
theorem aligned_fd_unit_mem_of_dc : ∃ a b : F,
    ⁅(alignedSourceRoots Q split hK μ n short).x 5 1,
      (alignedSourceRoots Q split hK μ n short).x 3 1⁆ =
        (alignedSourceRoots Q split hK μ n short).x 0 a *
          (alignedSourceRoots Q split hK μ n short).x 1 b := by
  let L := alignedSourceRoots Q split hK μ n short
  let R : L.CommutingRelations := aligned_commuting_of_dc Q split hK μ n short hm hdc
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
  have hFC : MulAut.conj (L.x 5 1) (L.x 2 c.toAdd) = L.x 1 c.toAdd * L.x 2 c.toAdd := by
    change L.x 5 1 * L.x 2 c.toAdd * (L.x 5 1)⁻¹ = _
    rw [aligned_fc_of_dc Q split hK μ n short hm
      (aligned_ec_of_dc Q split hK μ n short hm hdc) hdc,mul_one,
      mul_assoc,mul_inv_cancel,mul_one]
  rw [he,map_mul,map_mul,hFA,hFB,hFC] at hfix
  have hc0 : c.toAdd = 0 := by
    apply root_inj Q split hK μ n short 1
    rw [L.x_zero]
    have hh := mul_left_cancel hfix
    exact mul_right_cancel (hh.trans (one_mul _).symm)
  exact ⟨a.toAdd,b.toAdd,by simpa only [hc0,L.x_zero,mul_one] using he⟩



include hm hdc in
private theorem short_cubic_constraint (a b d : F)
    (hab : MulAut.conj ((alignedSourceRoots Q split hK μ n short).x 5 1)
      ((alignedSourceRoots Q split hK μ n short).x 3 d) =
        (alignedSourceRoots Q split hK μ n short).x 0 a *
          (alignedSourceRoots Q split hK μ n short).x 1 b *
            (alignedSourceRoots Q split hK μ n short).x 3 d) :
    (alignedSourceRoots Q split hK μ n short).x 0 a *
      MulAut.conj ((alignedSourceRoots Q split hK μ n short).x 5 1)
        ((alignedSourceRoots Q split hK μ n short).x 4 b) *
      ((alignedSourceRoots Q split hK μ n short).x 1 d *
        (alignedSourceRoots Q split hK μ n short).x 2 d) =
      (alignedSourceRoots Q split hK μ n short).x 4 d *
        (alignedSourceRoots Q split hK μ n short).x 3 d := by
  let L := alignedSourceRoots Q split hK μ n short
  let R : L.CommutingRelations := aligned_commuting_of_dc Q split hK μ n short hm hdc
  let s : X ⧸ Q.D := (n short).val
  let f := MulAut.conj (L.x 5 1)
  let w := MulAut.conj s
  let t := MulAut.conj (L.x 5 1*s)
  have hFD : f (L.x 3 d) = L.x 0 a * L.x 1 b * L.x 3 d := hab
  have hFC : f (L.x 2 d) = L.x 1 d * L.x 2 d := by
    change L.x 5 1 * L.x 2 d * (L.x 5 1)⁻¹ = _
    rw [aligned_fc_of_dc Q split hK μ n short hm
      (aligned_ec_of_dc Q split hK μ n short hm hdc) hdc,mul_one,
      mul_assoc,mul_inv_cancel,mul_one]
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
  have he : L.x 0 a * f (L.x 4 b) * (L.x 1 d * L.x 2 d) = L.x 4 d * L.x 3 d := by
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

include hm hdc in
private theorem fd_unit_b (a b : F)
    (hab : ⁅(alignedSourceRoots Q split hK μ n short).x 5 1,
      (alignedSourceRoots Q split hK μ n short).x 3 1⁆ =
        (alignedSourceRoots Q split hK μ n short).x 0 a *
          (alignedSourceRoots Q split hK μ n short).x 1 b) : b = 1 := by
  let L := alignedSourceRoots Q split hK μ n short
  change ⁅L.x 5 1,L.x 3 1⁆ = L.x 0 a * L.x 1 b at hab
  have hFD : MulAut.conj (L.x 5 1) (L.x 3 1) = L.x 0 a * L.x 1 b * L.x 3 1 := by
    have hh := congrArg (fun v : X ⧸ Q.D => v*L.x 3 1) hab
    simpa only [MulAut.conj_apply,commutatorElement_def,mul_assoc,
      inv_mul_cancel,mul_one] using hh
  have he := short_cubic_constraint Q split hK μ n short hm hdc a b 1 hFD
  change L.x 0 a * MulAut.conj (L.x 5 1) (L.x 4 b) * (L.x 1 1 * L.x 2 1) =
    L.x 4 1 * L.x 3 1 at he
  let V := simpleRemainder Q split (1-short)
  have hij : short ≠ 1-short := by fin_cases short <;> decide
  have hM : middleRoots Q split short (1-short) ≤ V :=
    middleRoots_le_remainder Q split hm short (1-short) hij
  have hA : L.x 0 a ∈ V := hM ((show positiveCarrier Q split short 0 ≤ middleRoots Q split short (1-short) from le_sup_right) (root_mem Q split hK μ n short 0 a))
  have hB : L.x 1 1 ∈ V :=
    hM ((show positiveCarrier Q split short 1 ≤ middleRoots Q split short (1-short) from le_sup_left.trans le_sup_left) (root_mem Q split hK μ n short 1 1))
  have hC : L.x 2 1 ∈ V :=
    hM ((show positiveCarrier Q split short 2 ≤ middleRoots Q split short (1-short) from le_sup_right.trans le_sup_left) (root_mem Q split hK μ n short 2 1))
  have hD : L.x 3 1 ∈ V :=
    (exchanged_roots_le_remainder Q split hm short (1-short) hij).1
      (root_mem Q split hK μ n short 3 1)
  have hF : L.x 5 1 ∈ V :=
    simpleRoot_le_other_remainder Q split hm short (1-short) hij
      (root_mem Q split hK μ n short 5 1)
  have hEN : L.x 4 1 ∈ normalizer (V : Set (X ⧸ Q.D)) :=
    remainder_parabolic_normalizes Q split (1-short) (hK (1-short))
      ((split.U_le.trans (Q.tits.B_le_standardParabolic _))
        ((simpleRoot_le Q split (1-short)) (root_mem Q split hK μ n short 4 1)))
  have hsolve : L.x 4 b * (L.x 4 1)⁻¹ =
      (L.x 5 1)⁻¹ * (L.x 0 a)⁻¹ *
        (L.x 4 1 * (L.x 3 1 * (L.x 1 1 * L.x 2 1)⁻¹ * L.x 5 1) * (L.x 4 1)⁻¹) := by
    have hh := congrArg (fun v : X ⧸ Q.D =>
      (L.x 5 1)⁻¹ * (L.x 0 a)⁻¹ * v * (L.x 1 1 * L.x 2 1)⁻¹ * L.x 5 1 * (L.x 4 1)⁻¹) he
    change _ * _ * (L.x 0 a * (L.x 5 1*L.x 4 b*(L.x 5 1)⁻¹) * _) * _ * _ * _ = _ at hh
    simpa only [mul_assoc,mul_inv_rev,inv_mul_cancel_left,mul_inv_cancel_left,
      inv_mul_cancel,mul_inv_cancel,mul_one,one_mul] using hh
  have hV : L.x 4 b * (L.x 4 1)⁻¹ ∈ V := by
    rw [hsolve]
    exact V.mul_mem (V.mul_mem (V.inv_mem hF) (V.inv_mem hA))
      ((mem_normalizer_iff.mp hEN _).mp
        (V.mul_mem (V.mul_mem hD (V.inv_mem (V.mul_mem hB hC))) hF))
  have hroot : L.x 4 b * (L.x 4 1)⁻¹ ∈ simpleRoot Q split (1-short) :=
    (simpleRoot Q split (1-short)).mul_mem (root_mem Q split hK μ n short 4 b)
      ((simpleRoot Q split (1-short)).inv_mem (root_mem Q split hK μ n short 4 1))
  have h1 := disjoint_def.mp (simpleRoot_disjoint_remainder Q split (1-short)) hroot hV
  exact root_inj Q split hK μ n short 4 (mul_inv_eq_one.mp h1)



include hm hdc in
/-- The short cubic and the long reflection fix both unit FD coefficients. -/
theorem aligned_fd_unit_of_dc :
    (alignedSourceRoots Q split hK μ n short).x 5 1 *
      (alignedSourceRoots Q split hK μ n short).x 3 1 =
        (alignedSourceRoots Q split hK μ n short).x 0 1 *
          (alignedSourceRoots Q split hK μ n short).x 1 1 *
            (alignedSourceRoots Q split hK μ n short).x 3 1 *
              (alignedSourceRoots Q split hK μ n short).x 5 1 := by
  let L := alignedSourceRoots Q split hK μ n short
  obtain ⟨a,b,hab⟩ := aligned_fd_unit_mem_of_dc Q split hK μ n short hm hdc
  have hb := fd_unit_b Q split hK μ n short hm hdc a b hab
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
  have ha := fd_unit_b Q split hK μ n short hm hdc b a he'
  rw [ha,hb] at hab
  have hh := congrArg (fun v : X ⧸ Q.D => v*(L.x 3 1*L.x 5 1)) hab
  change L.x 5 1 * L.x 3 1 = L.x 0 1 * L.x 1 1 * L.x 3 1 * L.x 5 1
  simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh

include hm hdc in
/-- Transport the unit equation with the actual source torus. -/
theorem aligned_fd_of_dc (z d : F) :
    (alignedSourceRoots Q split hK μ n short).x 5 z *
      (alignedSourceRoots Q split hK μ n short).x 3 d =
        (alignedSourceRoots Q split hK μ n short).x 0 (d^2*z) *
          (alignedSourceRoots Q split hK μ n short).x 1 (d*z^2) *
            (alignedSourceRoots Q split hK μ n short).x 3 d *
              (alignedSourceRoots Q split hK μ n short).x 5 z := by
  let L := alignedSourceRoots Q split hK μ n short
  change L.x 5 z * L.x 3 d = L.x 0 (d^2*z)*L.x 1 (d*z^2)*L.x 3 d*L.x 5 z
  by_cases hz : z = 0
  · subst z
    simp
  by_cases hd : d = 0
  · subst d
    simp
  let zu : Fˣ := Units.mk0 z hz
  let du : Fˣ := Units.mk0 d hd
  let t := (sourceBorelWeyl Q split hK μ n short split.abelian).torus (zu*du,du)
  have ht (i : Fin 6) : MulAut.conj t (L.x i 1) =
      L.x i (BorelWeylData.weight (zu*du) du i) := by
    simpa only [MulAut.conj_apply,t,L,mul_one] using sourceBorelWeyl_torus_root_of_dc Q split hK μ n short hm hdc (zu*du) du i 1
  have he := congrArg (MulAut.conj t) (aligned_fd_unit_of_dc Q split hK μ n short hm hdc)
  change MulAut.conj t (L.x 5 1*L.x 3 1) = MulAut.conj t (L.x 0 1*L.x 1 1*L.x 3 1*L.x 5 1) at he
  simp only [map_mul,ht] at he
  change L.x 5 (z*d/d)*L.x 3 d = L.x 0 ((z*d)*d)*L.x 1 ((z*d)^2/d)*L.x 3 d*L.x 5 (z*d/d) at he
  have hF : z*d/d = z := mul_div_cancel_right₀ z hd
  have hA : (z*d)*d = d^2*z := by ring
  have hB : (z*d)^2/d = d*z^2 := by field_simp
  simpa only [hF,hA,hB] using he



private theorem append_exchange {Y : Type*} [Group Y] {a b c : Y}
    (h : a*b=c) (z : Y) : a*(b*z)=c*z := by rw [← mul_assoc,h]

private theorem collect_root {K Y : Type*} [Field K] [Group Y]
    (L : PositiveRoots K Y) (i : Fin 6) (a b : K) (z : Y) :
    L.x i a * (L.x i b * z) = L.x i (a+b) * z := by
  rw [← mul_assoc,← L.x_add]

include hm hdc in
/-- The short cubic on C(e) forces the complete unit-short FE equation. -/
theorem aligned_fe_one_of_dc (e : F) :
    (alignedSourceRoots Q split hK μ n short).x 5 1 *
      (alignedSourceRoots Q split hK μ n short).x 4 e =
        (alignedSourceRoots Q split hK μ n short).x 0 (e^2) *
          (alignedSourceRoots Q split hK μ n short).x 1 e *
            (alignedSourceRoots Q split hK μ n short).x 2 e *
              (alignedSourceRoots Q split hK μ n short).x 3 e *
                (alignedSourceRoots Q split hK μ n short).x 4 e *
                  (alignedSourceRoots Q split hK μ n short).x 5 1 := by
  let L := alignedSourceRoots Q split hK μ n short
  let R : L.CommutingRelations := aligned_commuting_of_dc Q split hK μ n short hm hdc
  have hFD : MulAut.conj (L.x 5 1) (L.x 3 e) = L.x 0 (e^2)*L.x 1 e*L.x 3 e := by
    change L.x 5 1*L.x 3 e*(L.x 5 1)⁻¹ = _
    have hfd := aligned_fd_of_dc Q split hK μ n short hm hdc 1 e
    change L.x 5 1*L.x 3 e = L.x 0 (e^2*1)*L.x 1 (e*1^2)*L.x 3 e*L.x 5 1 at hfd
    rw [hfd]
    simp only [one_pow,mul_one,mul_assoc,mul_inv_cancel]
  have he := short_cubic_constraint Q split hK μ n short hm hdc (e^2) e e hFD
  change L.x 0 (e^2)*MulAut.conj (L.x 5 1) (L.x 4 e)*(L.x 1 e*L.x 2 e) = L.x 4 e*L.x 3 e at he
  have hsolve : MulAut.conj (L.x 5 1) (L.x 4 e) =
      (L.x 0 (e^2))⁻¹ * (L.x 4 e*L.x 3 e) * (L.x 1 e*L.x 2 e)⁻¹ := by
    have hh := congrArg (fun v : X ⧸ Q.D => (L.x 0 (e^2))⁻¹*v*(L.x 1 e*L.x 2 e)⁻¹) he
    simpa only [mul_assoc,mul_inv_rev,inv_mul_cancel_left,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh
  have hdc' : ∀ d c, L.x 3 d*L.x 2 c = L.x 0 (c*d)*L.x 2 c*L.x 3 d := hdc
  have heb : ∀ e b, L.x 4 e*L.x 1 b = L.x 0 (b*e)*L.x 1 b*L.x 4 e :=
    aligned_eb_of_dc Q split hK μ n short hm hdc
  have hh := congrArg (fun v : X ⧸ Q.D => v*L.x 5 1) hsolve
  simp only [MulAut.conj_apply,mul_inv_rev,root_inv] at hh
  simp only [mul_assoc,append_exchange (R.ea _ _),append_exchange (R.ec _ _),
    append_exchange (R.ed _ _),append_exchange (R.ca _ _),append_exchange (R.cb _ _),
    append_exchange (R.da _ _),append_exchange (R.db _ _),
    append_exchange (hdc' _ _),append_exchange (heb _ _),
    collect_root,← L.x_add,CharTwo.add_self_eq_zero,L.x_zero,mul_one] at hh
  change L.x 5 1*L.x 4 e = L.x 0 (e^2)*L.x 1 e*L.x 2 e*L.x 3 e*L.x 4 e*L.x 5 1
  simpa only [mul_assoc,add_assoc,CharTwo.add_self_eq_zero,add_zero] using hh

include hm hdc in
/-- The full FE equation, including its highest coefficient, follows from DC. -/
theorem aligned_fe_of_dc (z e : F) :
    (alignedSourceRoots Q split hK μ n short).x 5 z *
      (alignedSourceRoots Q split hK μ n short).x 4 e =
        (alignedSourceRoots Q split hK μ n short).x 0 (e^2*z^3) *
          (alignedSourceRoots Q split hK μ n short).x 1 (e*z^3) *
            (alignedSourceRoots Q split hK μ n short).x 2 (e*z^2) *
              (alignedSourceRoots Q split hK μ n short).x 3 (e*z) *
                (alignedSourceRoots Q split hK μ n short).x 4 e *
                  (alignedSourceRoots Q split hK μ n short).x 5 z := by
  let L := alignedSourceRoots Q split hK μ n short
  change L.x 5 z*L.x 4 e = L.x 0 (e^2*z^3)*L.x 1 (e*z^3)*L.x 2 (e*z^2)*L.x 3 (e*z)*L.x 4 e*L.x 5 z
  by_cases hz : z = 0
  · subst z
    simp
  let zu : Fˣ := Units.mk0 z hz
  let t := (sourceBorelWeyl Q split hK μ n short split.abelian).torus (zu,1)
  have ht (i : Fin 6) (c : F) : MulAut.conj t (L.x i c) =
      L.x i (BorelWeylData.weight zu 1 i*c) := by
    change t * L.x i c * t⁻¹ = _
    exact sourceBorelWeyl_torus_root_of_dc Q split hK μ n short hm hdc zu 1 i c
  have he := congrArg (MulAut.conj t) (aligned_fe_one_of_dc Q split hK μ n short hm hdc (e*z))
  change MulAut.conj t (L.x 5 1*L.x 4 (e*z)) =
    MulAut.conj t (L.x 0 ((e*z)^2)*L.x 1 (e*z)*L.x 2 (e*z)*L.x 3 (e*z)*L.x 4 (e*z)*L.x 5 1) at he
  simp only [map_mul,ht] at he
  change L.x 5 (z/1*1)*L.x 4 (1^2/z*(e*z)) =
    L.x 0 (z*1*(e*z)^2)*L.x 1 (z^2/1*(e*z))*L.x 2 (z*(e*z))*L.x 3 (1*(e*z))*
      L.x 4 (1^2/z*(e*z))*L.x 5 (z/1*1) at he
  have hE : 1^2/z*(e*z) = e := by field_simp
  have hA : z*1*(e*z)^2 = e^2*z^3 := by ring
  have hB : z^2/1*(e*z) = e*z^3 := by ring
  have hC : z*(e*z) = e*z^2 := by ring
  rw [hE,hA,hB,hC] at he
  simpa only [mul_one,one_mul,div_one] using he



include hm hdc in
/-- The entire positive multiplication table follows from the single normalized
DC pairing on the actual source roots. No FD or FE equation is an input. -/
theorem aligned_positive_relations_of_dc :
    (alignedSourceRoots Q split hK μ n short).CharTwoRelations where
  toCommutingRelations := aligned_commuting_of_dc Q split hK μ n short hm hdc
  dc := hdc
  eb := aligned_eb_of_dc Q split hK μ n short hm hdc
  fc := aligned_fc_of_dc Q split hK μ n short hm
    (aligned_ec_of_dc Q split hK μ n short hm hdc) hdc
  fd := aligned_fd_of_dc Q split hK μ n short hm hdc
  fe := aligned_fe_of_dc Q split hK μ n short hm hdc

include hm hdc in
/-- Assemble the full source Borel--Weyl equations from normalized DC and the
actual aligned pinnings. Compatible labels giving DC remain a source obligation. -/
theorem sourceBorelWeyl_relations_of_dc :
    (sourceBorelWeyl Q split hK μ n short split.abelian).Relations := by
  let R := aligned_positive_relations_of_dc Q split hK μ n short hm hdc
  obtain ⟨hE,hF⟩ := sourceBorelWeyl_simple_weights_of_cross_actions
    Q split hK μ n short split.abelian
    (alignedTorus_short_cross_action_of_dc Q split hK μ n short hm hdc)
    (alignedTorus_long_cross_action_of_dc Q split hK μ n short hm hdc)
  exact {
    toCharTwoRelations := R
    torus_root := sourceBorelWeyl_torus_root_of_dc Q split hK μ n short hm hdc
    r_sq := sourceBorelWeyl_r_sq Q split hK μ n short split.abelian
    s_sq := sourceBorelWeyl_s_sq Q split hK μ n short split.abelian
    braid := sourceBorelWeyl_braid Q split hK μ n short split.abelian hm R.toCommutingRelations
    r_torus := sourceBorelWeyl_r_torus_of_simple_weight Q split hK μ n short split.abelian
      (fun l m => by simpa only [mul_one] using hE l m 1)
    s_torus := sourceBorelWeyl_s_torus_of_simple_weight Q split hK μ n short split.abelian
      (fun l m => by simpa only [mul_one] using hF l m 1)
    rA := sourceBorelWeyl_rA Q split hK μ n short split.abelian
    rB := sourceBorelWeyl_rB Q split hK μ n short split.abelian
    rC := sourceBorelWeyl_rC Q split hK μ n short split.abelian hm R.toCommutingRelations
    rD := sourceBorelWeyl_rD Q split hK μ n short split.abelian
    rF := sourceBorelWeyl_rF Q split hK μ n short split.abelian
    sA := sourceBorelWeyl_sA Q split hK μ n short split.abelian hm R.toCommutingRelations
    sB := sourceBorelWeyl_sB Q split hK μ n short split.abelian
    sC := sourceBorelWeyl_sC Q split hK μ n short split.abelian
    sD := sourceBorelWeyl_sD Q split hK μ n short split.abelian
    sE := sourceBorelWeyl_sE Q split hK μ n short split.abelian
    long_word := sourceBorelWeyl_long_word Q split hK μ n short split.abelian
    short_word := sourceBorelWeyl_short_word Q split hK μ n short split.abelian }

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
