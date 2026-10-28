module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CommutationFromMixed

/-!
# The actual long-root natural action from the DC pairing

In the source hexagon, the commutator EB belongs to the radical-derived
middle triple DAC. Both E and B centralize C and D. The nondegenerate DC
pairing therefore puts EB in A. The long SL₂ cubic, acting on the disjoint
root lines A and B, forces E(1) to send B(b) to A(b)B(b).

For the full field multiplication, write [E(e),B(b)] = A(f(e,b)). The short
reflection interchanges E and B and fixes A, so f is symmetric. The long
rank-one word identifies the action of its torus on A with f(a,-).
Multiplicativity of that actual torus gives f(ab,c)=f(a,f(b,c)); the unit
calculation and symmetry give f(b,1)=b. Hence f(e,b)=eb. This proves the
needed natural-module calculation directly, without taking (4.7) or an
auxiliary two-parameter torus as a premise, including q=2 and q=4.

The natural-action calculation is also exposed from commutation and EB
containment alone. CommonField supplies that containment from the nonzero
additive middle pairing, before normalization of the field labels.

ReducedMixedData retains DC, FD, the lower FE coefficients and the auxiliary
torus needed by the other coefficient calculation. Its construction from
6E(a), and the compatible field markings giving DC, remain source obligations.
LongModuleApplication feeds the reduced input to the existing positive,
full marked, original and geometric comparisons on the same quotient.

Source: Fong--Seitz II (9.8), printed p.212, and the natural-module calculation
preceding (9.19), p.217. The displayed equations use the consumer's LEFT
commutator and ordered-exchange convention; characteristic two and the
central A root justify reversing the long-root commutator under the short
reflection. No external Thomas recognition is used.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
private theorem unit_action_from_cubic {K Y : Type*} [Field K] [Group Y]
    (L : PositiveRoots K Y) (R : L.CommutingRelations)
    (hinj : Function.Injective (fun p : K × K => L.x 0 p.1 * L.x 1 p.2))
    (r : Y) (hrA : ∀ a, MulAut.conj r (L.x 0 a) = L.x 1 a)
    (hrB : ∀ a, MulAut.conj r (L.x 1 a) = L.x 0 a)
    (hcube : (L.x 4 1 * r)^3 = 1)
    (hmem : ∀ b, ⁅L.x 4 1,L.x 1 b⁆ ∈ (L.root 0).range) (b : K) :
    L.x 4 1 * L.x 1 b * (L.x 4 1)⁻¹ = L.x 0 b * L.x 1 b := by
  classical
  have hex (a : K) : ∃ c : K, ⁅L.x 4 1,L.x 1 a⁆ = L.x 0 c := by
    obtain ⟨c,hc⟩ := hmem a
    exact ⟨c.toAdd,hc.symm⟩
  choose f hf using hex
  let t := MulAut.conj (L.x 4 1 * r)
  have hEA (a : K) : MulAut.conj (L.x 4 1) (L.x 0 a) = L.x 0 a := by
    change L.x 4 1 * L.x 0 a * (L.x 4 1)⁻¹ = _
    rw [R.ea,mul_assoc,mul_inv_cancel,mul_one]
  have hEB (a : K) : MulAut.conj (L.x 4 1) (L.x 1 a) =
      L.x 0 (f a) * L.x 1 a := by
    have hh := congrArg (fun x : Y => x * L.x 1 a) (hf a)
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one,MulAut.conj_apply] using hh
  have ht (x : Y) : t x = MulAut.conj (L.x 4 1) (MulAut.conj r x) := by
    simp only [t,MulAut.conj_apply,mul_inv_rev]
    group
  have hA (a : K) : t (L.x 0 a) = L.x 0 (f a) * L.x 1 a := by
    rw [ht,show MulAut.conj r (L.x 0 a) = L.x 1 a from
      hrA a,hEB]
  have hB (a : K) : t (L.x 1 a) = L.x 0 a := by
    rw [ht,show MulAut.conj r (L.x 1 a) = L.x 0 a from
      hrB a,hEA]
  have h3 : t (t (t (L.x 1 b))) = L.x 0 (f (f b)+b) * L.x 1 (f b) := by
    rw [hB,hA,map_mul,hA,hB,mul_assoc,R.ba,← mul_assoc,← L.x_add]
  have hcycle : t (t (t (L.x 1 b))) = L.x 1 b := by
    change _ * (_ * (_ * L.x 1 b * _) * _) * _ = _
    calc
      _ = (L.x 4 1*r)^3 * L.x 1 b * ((L.x 4 1*r)^3)⁻¹ := by
        simp only [pow_succ,pow_zero,mul_inv_rev]
        group
      _ = L.x 1 b := by rw [hcube]; simp
  have hp : L.x 0 (f (f b)+b) * L.x 1 (f b) = L.x 0 0 * L.x 1 b := by
    rw [L.x_zero,one_mul]
    exact h3.symm.trans hcycle
  have hf' : f b = b := congrArg Prod.snd
    (@hinj (f (f b)+b,f b) (0,b) hp)
  simpa only [hf',MulAut.conj_apply] using hEB b


private theorem conj_mul_apply {Y : Type*} [Group Y] (x y z : Y) :
    MulAut.conj (x*y) z = MulAut.conj x (MulAut.conj y z) := by
  simp only [MulAut.conj_apply,mul_inv_rev]
  group

private theorem append_exchange {Y : Type*} [Group Y] {a b c : Y}
    (h : a*b=c) (z : Y) : a*(b*z)=c*z := by rw [← mul_assoc,h]

private theorem collect_root {K Y : Type*} [Field K] [Group Y]
    (L : PositiveRoots K Y) (i : Fin 6) (a b : K) (z : Y) :
    L.x i a * (L.x i b * z) = L.x i (a+b) * z := by
  rw [← mul_assoc,← L.x_add]

private theorem torus_action_from_word {K Y : Type*} [Field K] [CharP K 2] [Group Y]
    (L : PositiveRoots K Y) (R : L.CommutingRelations)
    (hinj : Function.Injective (fun p : K × K => L.x 0 p.1 * L.x 1 p.2))
    (r : Y) (hrA : ∀ a, MulAut.conj r (L.x 0 a) = L.x 1 a)
    (hrB : ∀ a, MulAut.conj r (L.x 1 a) = L.x 0 a) (hrInv : r⁻¹ = r)
    (f : K → K → K)
    (hf : ∀ e b, MulAut.conj (L.x 4 e) (L.x 1 b) = L.x 0 (f e b) * L.x 1 b)
    (a : Kˣ) (t : Y)
    (hword : L.x 4 (a : K) * (r*L.x 4 (↑a⁻¹ : K)*r⁻¹) * L.x 4 (a : K) = t*r)
    (ht : ∀ b, ∃ c, MulAut.conj t (L.x 0 b) = L.x 0 c) (b : K) :
    MulAut.conj t (L.x 0 b) = L.x 0 (f a b) := by
  have hfix (e c : K) : MulAut.conj (L.x 4 e) (L.x 0 c) = L.x 0 c := by
    change L.x 4 e * L.x 0 c * (L.x 4 e)⁻¹ = _
    rw [R.ea,mul_assoc,mul_inv_cancel,mul_one]
  obtain ⟨c,hc⟩ := ht b
  have he := congrArg (fun v : Y => MulAut.conj v (L.x 1 b)) hword
  simp only [hrInv,map_mul,MulAut.mul_apply,hf,hrA,hrB,hfix,hc] at he
  simp only [mul_assoc,append_exchange (R.ba _ _),collect_root,
    CharTwo.add_self_eq_zero,add_zero] at he
  have hp : L.x 0 (f a (f (↑a⁻¹ : K) (f a b))) * L.x 1 (f (↑a⁻¹ : K) (f a b)+b) =
      L.x 0 c * L.x 1 0 := by simpa only [L.x_zero,mul_one,← L.x_add] using he
  have hh := @hinj (f a (f (↑a⁻¹ : K) (f a b)),f (↑a⁻¹ : K) (f a b)+b) (c,0) hp
  have hy : f (↑a⁻¹ : K) (f a b) = b := CharTwo.add_eq_zero.mp (congrArg Prod.snd hh)
  have hx : f a b = c := by simpa only [hy] using congrArg Prod.fst hh
  exact hc.trans (congrArg (L.x 0) hx.symm)

variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)


variable (hm : rotationOrder Q = 6)
  (hdc : ∀ d c : F, (alignedSourceRoots Q split hK μ n short).x 3 d * (alignedSourceRoots Q split hK μ n short).x 2 c = (alignedSourceRoots Q split hK μ n short).x 0 (c*d) * (alignedSourceRoots Q split hK μ n short).x 2 c * (alignedSourceRoots Q split hK μ n short).x 3 d)

include hm hdc in
/-- The DC pairing supplies all ten source commutations. -/
theorem aligned_commuting_of_dc : (alignedSourceRoots Q split hK μ n short).CommutingRelations :=
  aligned_commuting_of_two Q split hK μ n short hm
    (aligned_ba_of_dc Q split hK μ n short hm hdc)
    (aligned_ec_of_dc Q split hK μ n short hm hdc)

private theorem root_mem (i : Fin 6) (a : F) : (alignedSourceRoots Q split hK μ n short).x i a ∈ positiveCarrier Q split short i := by
  rw [← alignedSourceRoots_range Q split hK μ n short i]
  exact ⟨.ofAdd a,rfl⟩

private theorem root_inj (i : Fin 6) : Function.Injective ((alignedSourceRoots Q split hK μ n short).x i) :=
  (alignedSourceRoots_injective Q split hK μ n short i).comp Multiplicative.ofAdd.injective

private theorem root_commute (i : Fin 6) (a b : F) : Commute ((alignedSourceRoots Q split hK μ n short).x i a) ((alignedSourceRoots Q split hK μ n short).x i b) := by
  change (alignedSourceRoots Q split hK μ n short).x i a * (alignedSourceRoots Q split hK μ n short).x i b = (alignedSourceRoots Q split hK μ n short).x i b * (alignedSourceRoots Q split hK μ n short).x i a
  rw [← (alignedSourceRoots Q split hK μ n short).x_add,← (alignedSourceRoots Q split hK μ n short).x_add,add_comm]

include hm hdc in
/-- The middle Heisenberg group has no extra vectors fixed by both C and D.
This uses the literal nondegenerate DC pairing, not a representation tag. -/
theorem middle_centralizer_of_dc (x : X ⧸ Q.D)
    (hx : x ∈ middleRoots Q split (1-short) short)
    (hC : Commute x ((alignedSourceRoots Q split hK μ n short).x 2 1)) (hD : Commute x ((alignedSourceRoots Q split hK μ n short).x 3 1)) :
    x ∈ ((alignedSourceRoots Q split hK μ n short).root 0).range := by
  have hij : (1-short : Fin 2) ≠ short := by fin_cases short <;> decide
  have hx' : x ∈ (middleRoots Q split (1-short) short : Set (X ⧸ Q.D)) := hx
  rw [middleRoots_product Q split hm (1-short) short hij] at hx'
  obtain ⟨da,⟨d,hd,a,ha,rfl⟩,c,hc,rfl⟩ := hx'
  change d ∈ positiveCarrier Q split short 3 at hd
  change a ∈ positiveCarrier Q split short 0 at ha
  change c ∈ positiveCarrier Q split short 2 at hc
  rw [← alignedSourceRoots_range Q split hK μ n short 3] at hd
  rw [← alignedSourceRoots_range Q split hK μ n short 0] at ha
  rw [← alignedSourceRoots_range Q split hK μ n short 2] at hc
  obtain ⟨d,rfl⟩ := hd
  obtain ⟨a,rfl⟩ := ha
  obtain ⟨c,rfl⟩ := hc
  change (alignedSourceRoots Q split hK μ n short).x 3 d.toAdd *
    (alignedSourceRoots Q split hK μ n short).x 0 a.toAdd *
    (alignedSourceRoots Q split hK μ n short).x 2 c.toAdd ∈ _
  change Commute ((alignedSourceRoots Q split hK μ n short).x 3 d.toAdd * (alignedSourceRoots Q split hK μ n short).x 0 a.toAdd * (alignedSourceRoots Q split hK μ n short).x 2 c.toAdd) ((alignedSourceRoots Q split hK μ n short).x 2 1) at hC
  change Commute ((alignedSourceRoots Q split hK μ n short).x 3 d.toAdd * (alignedSourceRoots Q split hK μ n short).x 0 a.toAdd * (alignedSourceRoots Q split hK μ n short).x 2 c.toAdd) ((alignedSourceRoots Q split hK μ n short).x 3 1) at hD
  let R := aligned_commuting_of_dc Q split hK μ n short hm hdc
  have hAC : Commute ((alignedSourceRoots Q split hK μ n short).x 0 a.toAdd) ((alignedSourceRoots Q split hK μ n short).x 2 1) := (R.ca _ _).symm
  have hCC := root_commute Q split hK μ n short 2 c.toAdd 1
  have hDC : Commute ((alignedSourceRoots Q split hK μ n short).x 3 d.toAdd) ((alignedSourceRoots Q split hK μ n short).x 2 1) := by
    have hh := hC.mul_left (hAC.mul_left hCC).inv_left
    simpa only [mul_assoc,mul_inv_rev,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh
  have hd0 : d.toAdd = 0 := by
    apply root_inj Q split hK μ n short 0
    rw [(alignedSourceRoots Q split hK μ n short).x_zero]
    apply mul_right_cancel (b := (alignedSourceRoots Q split hK μ n short).x 2 1 * (alignedSourceRoots Q split hK μ n short).x 3 d.toAdd)
    simpa only [one_mul,mul_assoc] using ((hdc d.toAdd 1).symm.trans hDC.eq)
  simp only [hd0,(alignedSourceRoots Q split hK μ n short).x_zero,one_mul] at hD ⊢
  have hAD : Commute ((alignedSourceRoots Q split hK μ n short).x 0 a.toAdd) ((alignedSourceRoots Q split hK μ n short).x 3 1) := (R.da _ _).symm
  have hCD : Commute ((alignedSourceRoots Q split hK μ n short).x 2 c.toAdd) ((alignedSourceRoots Q split hK μ n short).x 3 1) := by
    have hh := hAD.inv_left.mul_left hD
    simpa only [inv_mul_cancel_left] using hh
  have hc0 : c.toAdd = 0 := by
    apply root_inj Q split hK μ n short 0
    rw [(alignedSourceRoots Q split hK μ n short).x_zero]
    apply mul_right_cancel (b := (alignedSourceRoots Q split hK μ n short).x 2 c.toAdd * (alignedSourceRoots Q split hK μ n short).x 3 1)
    simpa only [one_mul,mul_one,mul_assoc] using ((hdc 1 c.toAdd).symm.trans hCD.eq.symm)
  simpa only [hc0,(alignedSourceRoots Q split hK μ n short).x_zero,mul_one,PositiveRoots.x,ofAdd_toAdd] using
    (show (alignedSourceRoots Q split hK μ n short).root 0 a ∈ ((alignedSourceRoots Q split hK μ n short).root 0).range from ⟨a,rfl⟩)

include hm hdc in
/-- Radical containment and the DC pairing put EB in the actual highest root. -/
theorem aligned_eb_mem_of_dc (b e : F) : ⁅(alignedSourceRoots Q split hK μ n short).x 4 e,(alignedSourceRoots Q split hK μ n short).x 1 b⁆ ∈ ((alignedSourceRoots Q split hK μ n short).root 0).range := by
  have hij : short ≠ 1-short := by fin_cases short <;> decide
  have hE : (alignedSourceRoots Q split hK μ n short).x 4 e ∈ simpleRemainder Q split short :=
    simpleRoot_le_other_remainder Q split hm (1-short) short hij.symm
      (root_mem Q split hK μ n short 4 e)
  have hB : (alignedSourceRoots Q split hK μ n short).x 1 b ∈ simpleRemainder Q split short :=
    (exchanged_roots_le_remainder Q split hm (1-short) short hij.symm).1
      (root_mem Q split hK μ n short 1 b)
  have hx := radical_commutator_le_middle_of_linear Q split hm (1-short) short hij.symm
    (hK (1-short)) (μ (1-short)) (commutator_mem_commutator hE hB)
  let R := aligned_commuting_of_dc Q split hK μ n short hm hdc
  apply middle_centralizer_of_dc Q split hK μ n short hm hdc _ hx
  · have he : Commute ((alignedSourceRoots Q split hK μ n short).x 4 e) ((alignedSourceRoots Q split hK μ n short).x 2 1) := R.ec _ _
    have hb : Commute ((alignedSourceRoots Q split hK μ n short).x 1 b) ((alignedSourceRoots Q split hK μ n short).x 2 1) := (R.cb _ _).symm
    exact ((he.mul_left hb).mul_left he.inv_left).mul_left hb.inv_left
  · have he : Commute ((alignedSourceRoots Q split hK μ n short).x 4 e) ((alignedSourceRoots Q split hK μ n short).x 3 1) := R.ed _ _
    have hb : Commute ((alignedSourceRoots Q split hK μ n short).x 1 b) ((alignedSourceRoots Q split hK μ n short).x 3 1) := (R.db _ _).symm
    exact ((he.mul_left hb).mul_left he.inv_left).mul_left hb.inv_left

include hm in
private theorem highest_pair_injective :
    Function.Injective (fun p : F × F => (alignedSourceRoots Q split hK μ n short).x 0 p.1 * (alignedSourceRoots Q split hK μ n short).x 1 p.2) := by
  have hij : (1-short : Fin 2) ≠ short := by fin_cases short <;> decide
  have hAB : Disjoint (positiveCarrier Q split short 0) (positiveCarrier Q split short 1) :=
    ((terminal_disjoint_middle Q split hm (1-short) short hij).mono_right
      (show positiveCarrier Q split short 0 ≤ middleRoots Q split (1-short) short from
        le_sup_right.trans le_sup_left)).symm
  intro p q hpq
  have he := mul_injective_of_disjoint hAB
    (show (fun g : positiveCarrier Q split short 0 × positiveCarrier Q split short 1 =>
      (g.1 : X ⧸ Q.D) * g.2)
        (⟨(alignedSourceRoots Q split hK μ n short).x 0 p.1,root_mem Q split hK μ n short 0 p.1⟩,
          ⟨(alignedSourceRoots Q split hK μ n short).x 1 p.2,root_mem Q split hK μ n short 1 p.2⟩) =
      (fun g : positiveCarrier Q split short 0 × positiveCarrier Q split short 1 =>
        (g.1 : X ⧸ Q.D) * g.2)
        (⟨(alignedSourceRoots Q split hK μ n short).x 0 q.1,root_mem Q split hK μ n short 0 q.1⟩,
          ⟨(alignedSourceRoots Q split hK μ n short).x 1 q.2,root_mem Q split hK μ n short 1 q.2⟩) from hpq)
  exact Prod.ext (root_inj Q split hK μ n short 0 (congrArg (fun p => (p.1 : X ⧸ Q.D)) he))
    (root_inj Q split hK μ n short 1 (congrArg (fun p => (p.2 : X ⧸ Q.D)) he))

include hm in
/-- The actual long SL₂ cubic forces the natural action at the unit root.
No invocation of the representation classification (4.7) is needed here. -/
theorem aligned_eb_unit_action_of_mem
    (R : (alignedSourceRoots Q split hK μ n short).CommutingRelations)
    (hmem : ∀ b e : F, ⁅(alignedSourceRoots Q split hK μ n short).x 4 e,
      (alignedSourceRoots Q split hK μ n short).x 1 b⁆ ∈
        ((alignedSourceRoots Q split hK μ n short).root 0).range) (b : F) :
    (alignedSourceRoots Q split hK μ n short).x 4 1 *
      (alignedSourceRoots Q split hK μ n short).x 1 b *
      ((alignedSourceRoots Q split hK μ n short).x 4 1)⁻¹ =
        (alignedSourceRoots Q split hK μ n short).x 0 b *
          (alignedSourceRoots Q split hK μ n short).x 1 b := by
  apply unit_action_from_cubic _ R
    (highest_pair_injective Q split hK μ n short hm) ((n (1-short)).val)
    (sourceBorelWeyl_rA Q split hK μ n short split.abelian)
    (sourceBorelWeyl_rB Q split hK μ n short split.abelian) ?_
    (fun a => hmem a 1)
  let φ := alignedPinningHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
  have hm : (Theory.PSL2.SemilinearCoverage.uni (1 : F) *
      Theory.PSL2.SemilinearCoverage.weyl F)^3 = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ,Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
  have he := congrArg φ hm
  change (φ (Theory.PSL2.SemilinearCoverage.uni 1) * ((n (1-short)).val : X ⧸ Q.D))^3 = 1
  simpa only [map_pow,map_mul,map_one,φ,alignedPinningHom_weyl] using he


include hm hdc in
/-- The actual long SL₂ cubic forces the natural action at the unit root.
No invocation of the representation classification (4.7) is needed here. -/
theorem aligned_eb_unit_action_of_dc (b : F) :
    (alignedSourceRoots Q split hK μ n short).x 4 1 *
      (alignedSourceRoots Q split hK μ n short).x 1 b *
      ((alignedSourceRoots Q split hK μ n short).x 4 1)⁻¹ =
        (alignedSourceRoots Q split hK μ n short).x 0 b *
          (alignedSourceRoots Q split hK μ n short).x 1 b :=
  aligned_eb_unit_action_of_mem Q split hK μ n short hm
    (aligned_commuting_of_dc Q split hK μ n short hm hdc)
    (aligned_eb_mem_of_dc Q split hK μ n short hm hdc) b

include hm hdc in
/-- In particular, the separately assumed unit EB commutator is redundant. -/
theorem aligned_eb_one_of_dc : ⁅(alignedSourceRoots Q split hK μ n short).x 4 1,(alignedSourceRoots Q split hK μ n short).x 1 1⁆ = (alignedSourceRoots Q split hK μ n short).x 0 1 := by
  rw [commutatorElement_def,aligned_eb_unit_action_of_dc Q split hK μ n short hm hdc,
    mul_assoc,mul_inv_cancel,mul_one]

include hm in
/-- The complete long-root field multiplication is forced by the actual two
Weyl actions and the multiplicative long torus. The auxiliary two-parameter
torus is not used. This is the natural-module calculation behind (9.19). -/
theorem aligned_long_natural_action_of_commutator_mem
    (R : (alignedSourceRoots Q split hK μ n short).CommutingRelations)
    (hmem : ∀ b e : F, ⁅(alignedSourceRoots Q split hK μ n short).x 4 e,
      (alignedSourceRoots Q split hK μ n short).x 1 b⁆ ∈
        ((alignedSourceRoots Q split hK μ n short).root 0).range) :
    (∀ e b : F, (alignedSourceRoots Q split hK μ n short).x 4 e *
      (alignedSourceRoots Q split hK μ n short).x 1 b =
        (alignedSourceRoots Q split hK μ n short).x 0 (b*e) *
          (alignedSourceRoots Q split hK μ n short).x 1 b *
            (alignedSourceRoots Q split hK μ n short).x 4 e) ∧
      ∀ (a : Fˣ) (b : F), MulAut.conj
        (alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a)
        ((alignedSourceRoots Q split hK μ n short).x 0 b) =
          (alignedSourceRoots Q split hK μ n short).x 0 ((a : F)*b) := by
  classical
  let L := alignedSourceRoots Q split hK μ n short
  have hinj (i : Fin 6) : Function.Injective (L.x i) := root_inj Q split hK μ n short i
  have hex (e b : F) : ∃ a : F, ⁅L.x 4 e,L.x 1 b⁆ = L.x 0 a := by
    obtain ⟨a,ha⟩ := hmem b e
    exact ⟨a.toAdd,ha.symm⟩
  choose f hf using hex
  have hact (e b : F) : MulAut.conj (L.x 4 e) (L.x 1 b) = L.x 0 (f e b) * L.x 1 b := by
    have hh := congrArg (fun x : X ⧸ Q.D => x * L.x 1 b) (hf e b)
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one,MulAut.conj_apply] using hh
  have hsym (e b : F) : f e b = f b e := by
    let s : X ⧸ Q.D := (n short).val
    have hsA (a : F) : MulAut.conj s (L.x 0 a) = L.x 0 a :=
      sourceBorelWeyl_sA Q split hK μ n short split.abelian hm R a
    have hsB (a : F) : MulAut.conj s (L.x 1 a) = L.x 4 a :=
      sourceBorelWeyl_sB Q split hK μ n short split.abelian a
    have hsE (a : F) : MulAut.conj s (L.x 4 a) = L.x 1 a :=
      sourceBorelWeyl_sE Q split hK μ n short split.abelian a
    have he := congrArg (MulAut.conj s) (hf e b)
    rw [map_commutatorElement,hsE,hsB,hsA,← commutatorElement_inv,hf,root_inv] at he
    exact (hinj 0 he).symm
  have hone (b : F) : f 1 b = b := by
    apply hinj 0
    apply mul_right_cancel (b := L.x 1 b)
    exact (hact 1 b).symm.trans (aligned_eb_unit_action_of_mem Q split hK μ n short hm R hmem b)
  have hright (e : F) : f e 1 = e := (hsym e 1).trans (hone e)
  let T := alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))
  let r : X ⧸ Q.D := (n (1-short)).val
  have hT (a : Fˣ) (b : F) : MulAut.conj (T a) (L.x 0 b) = L.x 0 (f a b) := by
    apply torus_action_from_word L R (highest_pair_injective Q split hK μ n short hm) r
      (sourceBorelWeyl_rA Q split hK μ n short split.abelian)
      (sourceBorelWeyl_rB Q split hK μ n short split.abelian)
      (inv_eq_of_mul_eq_one_right (sourceReflection_sq Q split (1-short)
        (hK (1-short)) (μ (1-short)) (n (1-short)))) f hact a (T a) ?_ ?_ b
    · have hh := sourceBorelWeyl_long_word Q split hK μ n short split.abelian a
      change _ = alignedPairTorus Q split hK μ n short split.abelian (1,a) * r at hh
      rw [alignedPairTorus_long] at hh
      exact hh
    · intro c
      have ht := alignedTorus_mem_cartan Q split (1-short)
        (hK (1-short)) (μ (1-short)) (n (1-short)) a
      have hc := (mem_normalizer_iff.mp
        (positiveCarrier_torus_normalizes Q split short 0 ht) _).mp
          (root_mem Q split hK μ n short 0 c)
      rw [← alignedSourceRoots_range Q split hK μ n short 0] at hc
      obtain ⟨d,hd⟩ := hc
      exact ⟨d.toAdd,hd.symm⟩
  have hmul (a b : Fˣ) (c : F) : f (a*b : Fˣ) c = f a (f b c) := by
    apply hinj 0
    have he := congrArg (fun t : X ⧸ Q.D => MulAut.conj t (L.x 0 c)) (T.map_mul a b)
    rw [hT,conj_mul_apply,hT,hT] at he
    exact he
  have hform (e b : F) : f e b = e*b := by
    by_cases he : e = 0
    · subst e
      apply hinj 0
      simpa only [L.x_zero,commutatorElement_def,one_mul,inv_one,mul_one,mul_inv_cancel,
        zero_mul] using (hf 0 b).symm
    by_cases hb : b = 0
    · subst b
      rw [hsym]
      apply hinj 0
      simpa only [L.x_zero,commutatorElement_def,one_mul,inv_one,mul_one,mul_inv_cancel,
        mul_zero] using (hf 0 e).symm
    let a' := Units.mk0 e he
    let b' := Units.mk0 b hb
    have hh := hmul a' b' 1
    simpa only [hright,Units.val_mul,Units.val_mk0,a',b'] using hh.symm
  constructor
  · intro e b
    have he := congrArg (fun x : X ⧸ Q.D => x * L.x 4 e) (hact e b)
    simpa only [MulAut.conj_apply,mul_assoc,inv_mul_cancel,mul_one,hform,mul_comm e b] using he

  · intro a b
    simpa only [hform] using hT a b


include hm in
/-- The multiplication law from the actual long natural action. -/
theorem aligned_eb_of_commutator_mem
    (R : (alignedSourceRoots Q split hK μ n short).CommutingRelations)
    (hmem : ∀ b e : F, ⁅(alignedSourceRoots Q split hK μ n short).x 4 e,
      (alignedSourceRoots Q split hK μ n short).x 1 b⁆ ∈
        ((alignedSourceRoots Q split hK μ n short).root 0).range) (e b : F) :
    (alignedSourceRoots Q split hK μ n short).x 4 e *
      (alignedSourceRoots Q split hK μ n short).x 1 b =
        (alignedSourceRoots Q split hK μ n short).x 0 (b*e) *
          (alignedSourceRoots Q split hK μ n short).x 1 b *
            (alignedSourceRoots Q split hK μ n short).x 4 e :=
  (aligned_long_natural_action_of_commutator_mem Q split hK μ n short hm R hmem).1 e b


include hm hdc in
/-- The complete long-root field multiplication is forced by the actual two
Weyl actions and the multiplicative long torus. The auxiliary two-parameter
torus is not used. This is the natural-module calculation behind (9.19). -/
theorem aligned_eb_of_dc (e b : F) :
    (alignedSourceRoots Q split hK μ n short).x 4 e *
      (alignedSourceRoots Q split hK μ n short).x 1 b =
        (alignedSourceRoots Q split hK μ n short).x 0 (b*e) *
          (alignedSourceRoots Q split hK μ n short).x 1 b *
            (alignedSourceRoots Q split hK μ n short).x 4 e :=
  aligned_eb_of_commutator_mem Q split hK μ n short hm
    (aligned_commuting_of_dc Q split hK μ n short hm hdc)
    (aligned_eb_mem_of_dc Q split hK μ n short hm hdc) e b

include hm hdc in
/-- The normalized long-root commutator, in the consumer's left convention. -/
theorem aligned_eb_commutator_of_dc (e b : F) :
    ⁅(alignedSourceRoots Q split hK μ n short).x 4 e,
      (alignedSourceRoots Q split hK μ n short).x 1 b⁆ =
        (alignedSourceRoots Q split hK μ n short).x 0 (b*e) := by
  rw [commutatorElement_def,aligned_eb_of_dc Q split hK μ n short hm hdc]
  simp only [mul_assoc,mul_inv_cancel,mul_one]

/-- Remaining short-root mixed equations and torus action.  The long-root
commutator containment and unit value are now theorems, not fields of this input.
Constructing this record from 6E(a), including the binary case, remains required. -/
structure ReducedMixedData {K Y : Type*} [Field K] [Group Y] (roots : PositiveRoots K Y) where
  dc : ∀ d c, roots.x 3 d * roots.x 2 c = roots.x 0 (c*d) * roots.x 2 c * roots.x 3 d
  fd : ∀ z d, roots.x 5 z * roots.x 3 d =
    roots.x 0 (d^2*z) * roots.x 1 (d*z^2) * roots.x 3 d * roots.x 5 z
  fe_mem : ∀ z e, ∃ a, roots.x 5 z * roots.x 4 e =
    roots.x 0 a * roots.x 1 (e*z^3) * roots.x 2 (e*z^2) * roots.x 3 (e*z) * roots.x 4 e * roots.x 5 z
  torus : Kˣ × Kˣ → Y
  torus_root : ∀ l m i a, torus (l,m)*roots.x i a*(torus (l,m))⁻¹ =
    roots.x i (BorelWeylData.weight l m i*a)

/-- Supply the two old EB premises from the actual source radical and rank-one action. -/
def aligned_lower_of_reduced (d : ReducedMixedData (alignedSourceRoots Q split hK μ n short)) : LowerPositiveData (alignedSourceRoots Q split hK μ n short) where
  dc := d.dc
  fd := d.fd
  eb_mem b e := by
    rw [aligned_eb_commutator_of_dc Q split hK μ n short hm d.dc]
    exact ⟨.ofAdd (b*e),rfl⟩
  eb_one := by
    simpa only [one_mul] using aligned_eb_commutator_of_dc Q split hK μ n short hm d.dc 1 1
  fe_mem := d.fe_mem
  torus := d.torus
  torus_root := d.torus_root

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
