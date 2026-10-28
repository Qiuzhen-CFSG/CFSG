module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SectionMovement

/-!
# The literal natural section in the triality source

For the long endpoint j, the three middle roots M in its five-root radical
V_j are preserved by R_j. The short radical's derived subgroup is contained
in M by 6E(b), so U_j normalizes M; the Weyl lift preserves M by root geometry.
Together these generate R_j. Normality throughout is relative to V_j or U.

The earlier radical commutator bound makes V_j/M abelian. The five-root
product gives surjectivity of its two outside-root coordinates, and the
intersection description of M proves their independence. Thus the actual
section, before any representation classification, is the direct product of
its two outside roots. Its transported action is literal quotient conjugation,
and inclusion in U/M is injective.

Source: Fong--Seitz I (6E)(b), II (9.22)--(9.27), printed pp.217--219.
Here i is the cubic/short endpoint (source 2), j the fixed/long endpoint
(source 1); M is the source's U_1^{s_2} U_2^{s_1 s_2} U_1^{s_2 s_1}.
The companion NaturalSectionApplication supplies its actual field coordinates
and ScalarAlignment consumer. No scalar-linearity or tensor action is assumed
or asserted by this construction.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.NaturalSection
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
  (hKi : simpleRemainder Q split i ≤ localKernel Q i)
  (hKj : simpleRemainder Q split j ≤ localKernel Q j)
  (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
  (hVi : ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ ≤ middleRoots Q split i j)

include hm hij hVi in
/-- The acting rank-one group preserves the three middle roots. -/
theorem rankOne_normalizes :
    rankOne Q split j ≤ normalizer (middleRoots Q split i j : Set _) := by
  have hB : simpleRoot Q split j ≤ normalizer (middleRoots Q split i j : Set _) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    exact (commutator_mono (simpleRoot_le_other_remainder Q split hm j i hij.symm)
      (middleRoots_le_other_remainder Q split hm i j hij)).trans hVi
  let n := representative (Q.simple j)
  have hn : (n : X ⧸ Q.D) ∈ normalizer (middleRoots Q split i j : Set _) := by
    apply mem_normalizer_iff.mpr
    intro x
    exact (SetLike.ext_iff.mp
      (middleRoots_conjugate Q split hm i j hij n (representative_spec _)) x).symm
  rw [rankOne_eq Q split j n (representative_spec _)]
  apply sup_le hB
  intro x hx
  let N := normalizer (middleRoots Q split i j : Set (X ⧸ Q.D))
  have ht := N.mul_mem (N.mul_mem (N.inv_mem hn) (hB hx)) hn
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using ht

/-- The actual natural section, with normality only in its radical. -/
def sourceSection : RootSection Q split j :=
  middleFactorSection Q split j hKj hm i hij hKi hA
    (rankOne_normalizes Q split hm i j hij hVi)

local notation "d" => sourceSection Q split hm i j hij hKi hKj hA hVi

include hm hij hKi hA hVi in
/-- The three middle roots are normal in the full positive subgroup as well. -/
theorem unipotent_normalizes : split.U ≤ normalizer (middleRoots Q split i j : Set _) := by
  have hB := (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left).trans
    (rankOne_normalizes Q split hm i j hij hVi)
  have hV := radical_normalizes_middle Q split j hm i hij hKi hA
  intro x hx
  have he : x ∈ (simpleRoot Q split j : Set (X ⧸ Q.D)) *
      (simpleRemainder Q split j : Set (X ⧸ Q.D)) := by
    rw [simpleRoot_mul_remainder]; exact hx
  obtain ⟨a,ha,b,hb,rfl⟩ := he
  exact (normalizer _).mul_mem (hB ha) (hV hb)

/-- This is already an abelian quotient; no Frattini enlargement is neede(d). -/
instance commutative : IsMulCommutative (d).Carrier := by
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  change _root_.commutator (simpleRemainder Q split j) ≤
    (middleRoots Q split i j).comap (simpleRemainder Q split j).subtype
  rw [← map_le_iff_le_comap, map_commutator_eq]
  simpa only [range_subtype] using radical_commutator_le_middle Q split hm i j hij hKi hA

/-- The first outside root in the actual quotient. -/
def first : simpleRoot Q split i →* (d).Carrier :=
  (QuotientGroup.mk' (d).denominator).comp
    (inclusion (simpleRoot_le_other_remainder Q split hm i j hij))

/-- The second outside root in the actual quotient. -/
def second : rootAt Q split i (Q.simple j) →* (d).Carrier :=
  (QuotientGroup.mk' (d).denominator).comp
    (inclusion (exchanged_roots_le_remainder Q split hm i j hij).1)

/-- The ordered outside-root coordinate map. -/
def coordinates : simpleRoot Q split i × rootAt Q split i (Q.simple j) →* (d).Carrier where
  toFun z := first Q split hm i j hij hKi hKj hA hVi z.1 *
    second Q split hm i j hij hKi hKj hA hVi z.2
  map_one' := by simp
  map_mul' x y := by simp only [Prod.fst_mul, Prod.snd_mul, map_mul]; exact mul_mul_mul_comm _ _ _ _

include hm hij in
private theorem second_le_other : rootAt Q split i (Q.simple j) ≤ simpleRemainder Q split i :=
  (show rootAt Q split i (Q.simple j) ≤ middleRoots Q split j i from
    le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm j i hij.symm)

/-- The two outside coordinates remain independent after taking the quotient. -/
theorem coordinates_injective : Function.Injective
    (coordinates Q split hm i j hij hKi hKj hA hVi) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  rintro ⟨a,c⟩ hz
  have hac : (a : X ⧸ Q.D)*c ∈ middleRoots Q split i j := by
    let av : (d).numerator := inclusion (simpleRoot_le_other_remainder Q split hm i j hij) a
    let cv : (d).numerator := inclusion (exchanged_roots_le_remainder Q split hm i j hij).1 c
    have he : (QuotientGroup.mk' (d).denominator) (av*cv) = 1 := by
      rw [map_mul]
      exact hz
    exact (QuotientGroup.eq_one_iff (av*cv)).mp he
  have hcV := second_le_other Q split hm i j hij c.property
  have haV : (a : X ⧸ Q.D) ∈ simpleRemainder Q split i := by
    have hh := (simpleRemainder Q split i).mul_mem
      (middleRoots_le_other_remainder Q split hm i j hij hac)
      ((simpleRemainder Q split i).inv_mem hcV)
    simpa only [mul_inv_cancel_right] using hh
  have ha : a = 1 := Subtype.ext
    (disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) a.property haV)
  have hcM : (c : X ⧸ Q.D) ∈ middleRoots Q split i j := by simpa [ha] using hac
  have hc : c = 1 := by
    have hc' := (middleRoots_eq_intersection Q split hm i j hij
      (representative (Q.simple j)) (representative_spec _) ▸ hcM).2
    have ht := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) c.property hc'
    apply Subtype.ext
    apply (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)).injective
    change (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)) (c : X ⧸ Q.D) =
      (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)) 1
    rw [map_one]
    exact ht
  exact mem_bot.mpr (Prod.ext ha hc)

/-- The five-root product supplies both outside coordinates, without counting. -/
theorem coordinates_surjective : Function.Surjective
    (coordinates Q split hm i j hij hKi hKj hA hVi) := by
  intro z
  induction z using QuotientGroup.induction_on with
  | H x =>
    have hx : (x : X ⧸ Q.D) ∈ (simpleRemainder Q split j : Set _) := x.property
    rw [radical_five_product Q split hm i j hij] at hx
    obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,v,hv,rfl⟩,e,he,hx⟩ := hx
    have hbM : b ∈ middleRoots Q split i j := (show rootAt Q split j (Q.simple i) ≤ _ from
      le_sup_left.trans le_sup_left) hb
    have hcM : c ∈ middleRoots Q split i j := (show rootAt Q split i (Q.simple j*Q.simple i) ≤ _ from
      le_sup_right.trans le_sup_left) hc
    have hvM : v ∈ middleRoots Q split i j := (show rootAt Q split j (Q.simple i*Q.simple j) ≤ _ from
      le_sup_right) hv
    have hMV := middleRoots_le_remainder Q split hm i j hij
    let av : (d).numerator := ⟨a,simpleRoot_le_other_remainder Q split hm i j hij ha⟩
    let bv : (d).numerator := ⟨b,hMV hbM⟩
    let cv : (d).numerator := ⟨c,hMV hcM⟩
    let vv : (d).numerator := ⟨v,hMV hvM⟩
    let ev : (d).numerator := ⟨e,(exchanged_roots_le_remainder Q split hm i j hij).1 he⟩
    have hx' : av*bv*cv*vv*ev = x := Subtype.ext hx
    have hb1 : (QuotientGroup.mk' (d).denominator) bv = 1 := (QuotientGroup.eq_one_iff _).mpr hbM
    have hc1 : (QuotientGroup.mk' (d).denominator) cv = 1 := (QuotientGroup.eq_one_iff _).mpr hcM
    have hv1 : (QuotientGroup.mk' (d).denominator) vv = 1 := (QuotientGroup.eq_one_iff _).mpr hvM
    refine ⟨(⟨a,ha⟩,⟨e,he⟩),?_⟩
    change (QuotientGroup.mk' (d).denominator) av * (QuotientGroup.mk' (d).denominator) ev =
      (QuotientGroup.mk' (d).denominator) x
    rw [← hx', map_mul, map_mul, map_mul, map_mul, hb1,hc1,hv1,mul_one,mul_one,mul_one]

/-- The source section is the direct product of its two literal outside roots. -/
def coordinateEquiv : simpleRoot Q split i × rootAt Q split i (Q.simple j) ≃* (d).Carrier :=
  MulEquiv.ofBijective (coordinates Q split hm i j hij hKi hKj hA hVi)
    ⟨coordinates_injective Q split hm i j hij hKi hKj hA hVi,
      coordinates_surjective Q split hm i j hij hKi hKj hA hVi⟩

/-- The first coordinate embeds in the source section. -/
theorem first_injective : Function.Injective (first Q split hm i j hij hKi hKj hA hVi) := by
  intro a b he
  have hh := coordinates_injective Q split hm i j hij hKi hKj hA hVi
    (a₁ := (a,1)) (a₂ := (b,1)) (by simpa [coordinates] using he)
  exact congrArg Prod.fst hh

/-- The second coordinate embeds in the source section. -/
theorem second_injective : Function.Injective (second Q split hm i j hij hKi hKj hA hVi) := by
  intro a b he
  have hh := coordinates_injective Q split hm i j hij hKi hKj hA hVi
    (a₁ := (1,a)) (a₂ := (1,b)) (by simpa [coordinates] using he)
  exact congrArg Prod.snd hh

/-- The conjugation action on the actual section, in its two outside-root coordinates. -/
def coordinateAction : rankOne Q split j →* MulAut
    (simpleRoot Q split i × rootAt Q split i (Q.simple j)) :=
  (MulAut.congr (coordinateEquiv Q split hm i j hij hKi hKj hA hVi).symm).toMonoidHom.comp
    (d).action

/-- The coordinate action intertwines literal quotient conjugation. -/
theorem coordinateAction_intertwines (r : rankOne Q split j)
    (z : simpleRoot Q split i × rootAt Q split i (Q.simple j)) :
    coordinateEquiv Q split hm i j hij hKi hKj hA hVi
        (coordinateAction Q split hm i j hij hKi hKj hA hVi r z) =
      (d).action r (coordinateEquiv Q split hm i j hij hKi hKj hA hVi z) := by
  exact (coordinateEquiv Q split hm i j hij hKi hKj hA hVi).apply_symm_apply _

variable [((middleRoots Q split i j).subgroupOf split.U).Normal]

/-- Inclusion of the natural section into the same U modulo the same denominator. -/
def intoPositive : (d).Carrier →* (split.U ⧸ (middleRoots Q split i j).subgroupOf split.U) := by
  letI : ((middleRoots Q split i j).subgroupOf (simpleRemainder Q split j)).Normal := (d).normal
  exact QuotientGroup.map (d).denominator ((middleRoots Q split i j).subgroupOf split.U)
    (inclusion (show (d).numerator ≤ split.U from inf_le_left)) (fun _ hx => hx)

/-- No additional kernel arises on enlarging the numerator from the radical to U. -/
theorem intoPositive_injective : Function.Injective
    (intoPositive Q split hm i j hij hKi hKj hA hVi) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H x =>
    apply mem_bot.mpr
    apply (QuotientGroup.eq_one_iff x).mpr
    exact (QuotientGroup.eq_one_iff (inclusion (show (d).numerator ≤ split.U from inf_le_left) x)).mp hz

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.NaturalSection
