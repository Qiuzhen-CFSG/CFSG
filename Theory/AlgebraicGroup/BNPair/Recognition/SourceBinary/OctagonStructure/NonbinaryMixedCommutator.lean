module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicCentralizerDichotomy
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicMiddleSection
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MiddleSection
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FourRootIntervals
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.TorusIrreducibility

/-!
# Mixed-root vanishing in the unequal linear octagon

The five middle roots cannot be invariant under the larger linear rank-one
group. Root movement gives a faithful effective action on the corresponding
quotient, whose two end coordinates make it smaller than the minimum binary
SL₂ degree allows. The derived radical is therefore strictly smaller than
the five-root subgroup.

The long commutator supplies the two smaller-field middle roots in the
derived radical. The four-root interval confines the mixed commutator to
two coordinates; derived placement removes the outside one. If nonzero,
Cartan irreducibility fills the remaining root, and two reflections then
put all five middle roots in the derived radical, a contradiction.
The two fixed middle roots consequently centralize the whole radical.
Their product cannot be invariant under the larger rank-one group: the
same degree bound would force the reflection to fix both exchanged roots.

Source: Fong--Seitz I (1973), (6G), printed p.50, “We claim that”, using
(4B) and the preceding long-commutator identity. The original-factor and
Chapter 12 applications construct all field and long-commutator inputs.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
  (μ : localGroup Q split j ≃* PSL(2,F)) (s : HexagonStructure.RootReflection Q split j)

private theorem end_root_le (hm : rotationOrder Q = 8)
    (i : Fin 2) (hij : i ≠ j) : simpleRoot Q split i ≤ simpleRemainder Q split j := by
  intro x hx
  change x ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D))
  rw [radical_end_product Q split hm j i hij.symm]
  exact ⟨x,hx,1,⟨1,one_mem _,1,one_mem _,one_mul _⟩,mul_one _⟩

private theorem octagon_oddProduct_moves_section (hm : rotationOrder Q = 8)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (d : RootSection Q split j)
    (hroot : simpleRoot Q split i ≤ d.numerator)
    (hden : d.denominator.map d.numerator.subtype ≤ simpleRemainder Q split i) :
    d.action (oddProduct Q split j hKj μ s) ≠ 1 := by
  intro he
  have hei : d.action (oddProduct Q split j hKj μ s)⁻¹ = 1 := by
    rw [map_inv, he, inv_one]
  let u := oddPartner Q split j hKj μ s
  have huU : (u : X ⧸ Q.D) ∈ split.U :=
    simpleRoot_le Q split j (oddPartner_mem_root Q split j hKj μ s)
  have huN : (u : X ⧸ Q.D) ∈ normalizer (simpleRemainder Q split i : Set _) :=
    remainder_parabolic_normalizes Q split i hKi
      (Q.tits.B_le_standardParabolic _ (split.U_le huU))
  apply simpleRoot_ne_bot Q split i
  apply eq_bot_iff.mpr
  intro a ha
  let x : d.numerator := ⟨a,hroot ha⟩
  let y := d.numeratorAction (oddProduct Q split j hKj μ s)⁻¹ x
  have hy : (y : X ⧸ Q.D) =
      (u : X ⧸ Q.D)⁻¹*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*u := by
    dsimp only [y]
    rw [d.numeratorAction_apply]
    simp only [coe_inv, oddProduct_coe, mul_inv_rev, inv_inv, mul_assoc]
    rfl
  have hrootV : rootAt Q split i (Q.simple j) ≤ simpleRemainder Q split i :=
    (show rootAt Q split i (Q.simple j) ≤ middleFive Q split i j from
      le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))).trans
        (middleFive_le_remainder Q split hm i j hij)
  have haR : (s.val : X ⧸ Q.D)⁻¹*a*s.val ∈ rootAt Q split i (Q.simple j) := by
    rw [rootAt_eq Q split i (Q.simple j) s.val s.class_eq]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using ha
  have hyV : (y : X ⧸ Q.D) ∈ simpleRemainder Q split i := by
    rw [hy]
    simpa only [inv_inv] using (mem_normalizer_iff.mp
      ((normalizer _).inv_mem huN) _).mp (hrootV haR)
  have hd : y / x ∈ d.denominator := by
    apply QuotientGroup.eq_iff_div_mem.mp
    change d.action (oddProduct Q split j hKj μ s)⁻¹ (QuotientGroup.mk x) =
      QuotientGroup.mk x
    rw [hei]; rfl
  have hdV : (y : X ⧸ Q.D) / a ∈ simpleRemainder Q split i :=
    hden (mem_map_of_mem d.numerator.subtype hd)
  have haV : a ∈ simpleRemainder Q split i := by
    have ht := (simpleRemainder Q split i).mul_mem (inv_mem hdV) hyV
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using ht
  exact mem_bot.mpr (disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haV)


private theorem middle_effective_card_le (hm : rotationOrder Q = 8)
    (i : Fin 2) (hij : i ≠ j)
    (hVN : simpleRemainder Q split j ≤ normalizer (middleFive Q split j i : Set _))
    (hRN : rankOne Q split j ≤ normalizer (middleFive Q split j i : Set _)) :
    Nat.card (radicalFactorSection Q split j hKj (middleFive Q split j i)
      hVN hRN).EffectiveCarrier ≤ Nat.card (simpleRoot Q split i)^2 := by
  let d := radicalFactorSection Q split j hKj (middleFive Q split j i) hVN hRN
  let V := d.numerator
  let A := simpleRoot Q split i
  let E := rootAt Q split i (Q.simple j)
  have hAV : A ≤ V := end_root_le Q split j hm i hij
  have hEV : E ≤ V := (octagon_three_roots_le_remainder Q split hm j i hij.symm).1
  have hMV : middleFive Q split j i ≤ V := middleFive_le_remainder Q split hm j i hij.symm
  let q := QuotientGroup.mk' d.effectiveDenominator
  have hkill (z : V) (hz : (z : X ⧸ Q.D) ∈ middleFive Q split j i) : q z = 1 := by
    apply (QuotientGroup.eq_one_iff z).mpr
    rw [d.effectiveDenominator_eq]
    exact (show d.denominator ≤ frattini d.numerator ⊔ d.denominator from le_sup_right) hz
  let f : A × E → d.EffectiveCarrier := fun z =>
    q (inclusion hAV z.1) * q (inclusion hEV z.2)
  have hf : Function.Surjective f := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      have hx : (x : X ⧸ Q.D) ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) := x.property
      rw [radical_end_product Q split hm j i hij.symm] at hx
      obtain ⟨a,ha,_,⟨m,hm,e,he,rfl⟩,hx⟩ := hx
      let av : V := ⟨a,hAV ha⟩
      let mv : V := ⟨m,hMV hm⟩
      let ev : V := ⟨e,hEV he⟩
      have hx' : av*(mv*ev) = x := Subtype.ext hx
      refine ⟨(⟨a,ha⟩,⟨e,he⟩),?_⟩
      change q av * q ev = q x
      rw [←hx',map_mul,map_mul,hkill mv hm,one_mul]
  have hc := Nat.card_le_card_of_surjective f hf
  have hEc : Nat.card E = Nat.card A := by simp only [E,A,rootAt,card_rightConjugate]
  simpa only [Nat.card_prod,hEc,pow_two] using hc

include hKj μ s in
/-- The five middle roots cannot be invariant under the larger linear
rank-one group: their quotient is too small for its effective action. -/
theorem linear_rankOne_not_normalizes_middleFive (hm : rotationOrder Q = 8)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b)
    (hsmall : Nat.card (simpleRoot Q split i) < Nat.card F) :
    ¬ rankOne Q split j ≤ normalizer (middleFive Q split j i : Set _) := by
  intro hR
  have hVN := middleFive_normalized_by_remainder Q split hm j i hij.symm hKi
  let d := radicalFactorSection Q split j hKj (middleFive Q split j i) hVN hR
  have hroot : simpleRoot Q split i ≤ d.numerator := end_root_le Q split j hm i hij
  have hden : d.denominator.map d.numerator.subtype ≤ simpleRemainder Q split i := by
    change ((middleFive Q split j i).subgroupOf (simpleRemainder Q split j)).map
      (simpleRemainder Q split j).subtype ≤ _
    rw [map_subgroupOf_eq_of_le (middleFive_le_remainder Q split hm j i hij.symm),
      middleFive_eq_radical_intersection Q split hm j i hij.symm]
    exact inf_le_left.trans inf_le_right
  have hf := d.effectiveRepresentation_injective
    (linear_section_effectiveAction_injective Q split j hKj μ s d
      (octagon_oddProduct_moves_section Q split j hKj μ s hm i hij hKi d hroot hden))
  have hlo := linear_effectiveSection_card_bound Q split j hKj μ s d hf hb hF
  have hup := middle_effective_card_le Q split j hKj hm i hij hVN hR
  have hh : Nat.card F ^ 2 ≤ Nat.card (simpleRoot Q split i)^2 := by
    rw [hF,←pow_mul,Nat.mul_comm b 2]
    exact hlo.trans hup
  nlinarith

include hKj μ s in
/-- The derived radical is strictly smaller than the five-root product
in the unequal linear octagon. This is the (4B) obstruction in (6G). -/
theorem linear_radical_commutator_lt_middleFive (hm : rotationOrder Q = 8)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b)
    (hsmall : Nat.card (simpleRoot Q split i) < Nat.card F) :
    ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ < middleFive Q split j i := by
  apply lt_of_le_of_ne (radical_commutator_le_middleFive Q split hm j i hij.symm hKi hA)
  intro he
  apply linear_rankOne_not_normalizes_middleFive Q split j hKj μ s hm i hij hKi hb hF hsmall
  rw [←he]
  intro r hr
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hV := (rankOne_le_parabolic Q split j).trans
    (remainder_parabolic_normalizes Q split j hKj)
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hV hr)]
private theorem ssq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
private theorem right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)
private theorem right_comm (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),
        rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
private theorem right_bot (w : Weyl Q) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
private theorem reflection_remainder (k : Fin 2) :
    rightConjugate (simpleRemainder Q split k)
      (representative (Q.simple k) : X ⧸ Q.D) = simpleRemainder Q split k := by
  rw [simpleRemainder,rightConjugate_inf,
    ←unipotentConjugate_eq split _ _ (representative_spec _),
    unipotentConjugate_right split _ _ _ (representative_spec _),ssq,
    unipotentConjugate_one,inf_comm]

include hKj μ s in
/-- A nonzero mixed commutator would fill the other root family in the
middle five-root subgroup, contradicting the effective-section bound. -/
theorem linear_mixed_commutator_eq_bot (hm : rotationOrder Q = 8)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b)
    (hsmall : Nat.card (simpleRoot Q split i) < Nat.card F)
    (hlong : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ⊔
        rootAt Q split i (Q.simple j*Q.simple i)) :
    ⁅simpleRoot Q split j,rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ := by
  let V := simpleRemainder Q split j
  let D := ⁅V,V⁆
  let M := middleFive Q split j i
  let A := rootAt Q split i (Q.simple j)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let W := rootAt Q split j (Q.simple i*Q.simple j)
  let K := ⁅simpleRoot Q split j,E⁆
  have hlt : D < M := linear_radical_commutator_lt_middleFive Q split j hKj μ s hm i hij hKi hA hb hF hsmall
  have hAD : E ⊔ C ≤ D := by
    rw [←hlong]
    exact commutator_mono (end_root_le Q split j hm i hij)
      (octagon_three_roots_le_remainder Q split hm j i hij.symm).1
  have hED : E ≤ D := le_sup_left.trans hAD
  have hCD : C ≤ D := le_sup_right.trans hAD
  have hND : Q.tits.standardParabolic {Q.simple j} ≤ normalizer (D : Set (X ⧸ Q.D)) := by
    intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅V,V⁆).map _ = _
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
      (remainder_parabolic_normalizes Q split j hKj hr)]
  have hKD : K ≤ D := (commutator_mono le_rfl hED).trans
    (le_normalizer_iff_commutator_le_right.mp
      ((simpleRoot_le Q split j).trans (split.U_le.trans
        ((Q.tits.B_le_standardParabolic _).trans hND))))
  have hWM : W ≤ M := le_sup_right
  have hAM : Disjoint A M := by
    apply disjoint_def.mpr
    intro x hxA hxM
    have hx : x ∈ rightConjugate (simpleRemainder Q split i)
        (representative (Q.simple j) : X ⧸ Q.D) := by
      have he := middleFive_eq_radical_intersection Q split hm j i hij.symm
      exact ((he ▸ hxM) : x ∈
        (simpleRemainder Q split j ⊓ simpleRemainder Q split i) ⊓
        rightConjugate (simpleRemainder Q split i)
          (representative (Q.simple j) : X ⧸ Q.D)).2
    apply (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)).injective
    exact (disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) hxA hx).trans
      (map_one _).symm
  have hKW : K ≤ W := by
    intro x hx
    obtain ⟨a,ha,w,hw,rfl⟩ := distance_three_commutator_support Q split hm j i hij.symm
      hKj hKi x hx
    have ham : a ∈ M := by
      simpa only [mul_inv_cancel_right] using M.mul_mem (hlt.le (hKD hx)) (M.inv_mem (hWM hw))
    have ha1 := disjoint_def.mp hAM ha ham
    change a*w ∈ W
    rw [ha1,one_mul]
    exact hw
  by_contra hn
  have hHW : Q.tits.B ⊓ Q.tits.N ≤ normalizer (K : Set (X ⧸ Q.D)) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅simpleRoot Q split j,E⁆).map _ = _
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (torus_normalizes_simpleRoot Q split j ht),
      mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split i
        (Q.simple j*Q.simple i*Q.simple j) ht)]
  have he : K = W := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split j μ hKj
    (Q.simple i*Q.simple j) K hKW hn hHW
  have hWD : W ≤ D := he ▸ hKD
  have hfirst : rootAt Q split j (Q.simple i) ≤ D := by
    have hh := comap_mono (f := (MulAut.conj
      (representative (Q.simple j) : X ⧸ Q.D)).toMonoidHom) hWD
    change rightConjugate W _ ≤ rightConjugate ⁅V,V⁆ _ at hh
    dsimp only [W,V] at hh
    rw [right_rep,right_comm,reflection_remainder] at hh
    simpa only [mul_assoc,ssq,mul_one] using hh
  have hmiddle : rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ≤ D := by
    have hh := congrArg (fun B => rightConjugate B
      (representative (Q.simple i) : X ⧸ Q.D)) he
    change rightConjugate ⁅simpleRoot Q split j,E⁆ _ = rightConjugate W _ at hh
    rw [right_comm] at hh
    change ⁅rootAt Q split j (Q.simple i),rightConjugate E _⁆ = rightConjugate W _ at hh
    dsimp only [E,W] at hh
    rw [right_rep,right_rep] at hh
    have hfix := perpendicular_root_stable Q split hm i j hij
      (representative (Q.simple i)) (representative_spec _)
    rw [right_rep] at hfix
    rw [hfix] at hh
    rw [←hh]
    exact commutator_mono (hfirst.trans (commutator_le_self _))
      (hED.trans (commutator_le_self _))
  apply (not_le_of_gt hlt)
  exact sup_le (sup_le (sup_le (sup_le hfirst hCD) hmiddle) hED) hWD

/-- Once the mixed commutator vanishes, the two fixed middle roots
centralize the whole larger-field radical. -/
theorem separated_middle_pair_centralizes (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (c : X ⧸ Q.D)
    (hc : ∀ w : Weyl Q,
      c ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({c} : Set (X ⧸ Q.D)) = ⊥)
    (hperp : ⁅simpleRoot Q split i,
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥)
    (hmix : ⁅simpleRoot Q split j,
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥) :
    rootAt Q split i (Q.simple j*Q.simple i) ⊔
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
      centralizer (simpleRemainder Q split j : Set (X ⧸ Q.D)) := by
  let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  have hfix : rootAt Q split i (Q.simple j*Q.simple i*Q.simple j*Q.simple i) = E := by
    rw [←right_rep]
    exact perpendicular_root_stable Q split hm i j hij _ (representative_spec _)
  have hleft : ⁅rootAt Q split j (Q.simple i),E⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple i) : X ⧸ Q.D)) hmix
    rw [right_comm] at hh
    change ⁅rootAt Q split j (Q.simple i),rightConjugate E _⁆ = _ at hh
    dsimp only [E] at hh
    rw [right_rep,hfix,right_bot] at hh
    exact hh
  obtain ⟨hnear,hother⟩ := separated_middle_commutators Q split hm i j hij hKi c hc
  obtain ⟨heven1,heven2⟩ := middle_adjacent_commutators Q split hm i j hij hKi hKj
  have hself : ⁅E,E⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)) hA
    rw [right_comm,right_bot] at hh
    exact hh
  have hM : middleFive Q split j i ≤ centralizer (E : Set (X ⧸ Q.D)) :=
    sup_le (sup_le (sup_le (sup_le
      (commutator_eq_bot_iff_le_centralizer.mp hleft)
      (commutator_eq_bot_iff_le_centralizer.mp hother))
      (commutator_eq_bot_iff_le_centralizer.mp heven1))
      (commutator_eq_bot_iff_le_centralizer.mp hself))
      (commutator_eq_bot_iff_le_centralizer.mp heven2)
  have hVE : simpleRemainder Q split j ≤ centralizer (E : Set (X ⧸ Q.D)) := by
    intro x hx
    have hp : x ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) := hx
    rw [radical_end_product Q split hm j i hij.symm] at hp
    obtain ⟨a,ha,_,⟨m,hm,b,hb,rfl⟩,rfl⟩ := hp
    exact mul_mem (commutator_eq_bot_iff_le_centralizer.mp hperp ha)
      (mul_mem (hM hm) (commutator_eq_bot_iff_le_centralizer.mp hnear hb))
  have hVzero := commutator_eq_bot_iff_le_centralizer.mpr hVE
  have hVC : ⁅simpleRemainder Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple j) : X ⧸ Q.D)) hVzero
    rw [right_comm,reflection_remainder] at hh
    dsimp only [E] at hh
    rw [right_rep,right_bot] at hh
    simpa only [mul_assoc,ssq,mul_one] using hh
  exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hVC))
    (le_centralizer_iff.mp hVE)


/-- The two middle linear roots are too small to be invariant under the
larger rank-one group. The actual reflection exchanges them. -/
theorem linear_rankOne_not_normalizes_middlePair
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* PSL(2,F))
    (s : HexagonStructure.RootReflection Q split j)
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b)
    (hsmall : Nat.card (simpleRoot Q split i) < Nat.card F)
    (hcomm : ⁅rootAt Q split i (Q.simple j*Q.simple i),
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥) :
    ¬ rankOne Q split j ≤ normalizer
      ((rootAt Q split i (Q.simple j*Q.simple i) ⊔
        rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Subgroup (X ⧸ Q.D)) : Set _) := by
  intro hN
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  let J := C ⊔ E
  have hJV : J ≤ simpleRemainder Q split j := by
    apply (show J ≤ middleFive Q split j i from
      sup_le (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))
        (le_sup_right.trans le_sup_left)).trans
    exact middleFive_le_remainder Q split hm j i hij.symm
  have hsize : Nat.card J ≤ Nat.card (simpleRoot Q split i)^2 := by
    let f : C × E → J := fun p => ⟨p.1*p.2,mul_mem_sup p.1.property p.2.property⟩
    have hf : Function.Surjective f := by
      intro x
      have hx : (x : X ⧸ Q.D) ∈ (C : Set (X ⧸ Q.D))*(E : Set (X ⧸ Q.D)) := by
        rw [←coe_mul_of_left_le_normalizer_right _ _
          ((commutator_eq_bot_iff_le_centralizer.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))]
        exact x.property
      obtain ⟨c,hc,e,he,hh⟩ := hx
      exact ⟨(⟨c,hc⟩,⟨e,he⟩),Subtype.ext hh⟩
    have hh := Nat.card_le_card_of_surjective f hf
    simpa only [C,E,Nat.card_prod,rootAt,card_rightConjugate,pow_two] using hh
  have hsize' : Nat.card J < 2^(2*b) := by
    have hh : Nat.card (simpleRoot Q split i)^2 < Nat.card F^2 := by nlinarith
    rw [hF,←pow_mul,Nat.mul_comm b 2] at hh
    exact hsize.trans_lt hh
  have hzero := linear_small_subgroup_centralized Q split j hKj μ s J hJV hN hb hF hsize'
  have hs : (s.val : X ⧸ Q.D) ∈ normalizer (E : Set (X ⧸ Q.D)) :=
    Subgroup.centralizer_le_normalizer _
      (fun x hx => commutator_eq_bot_iff_le_centralizer.mp hzero s.mem_rankOne x (mem_sup_right hx))
  have hEC : E = C := by
    have he : rightConjugate E (s.val : X ⧸ Q.D) = E := by
      ext x
      exact (mem_normalizer_iff.mp hs x).symm
    change rightConjugate (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)) _ = E at he
    rw [rootAt_right Q split i _ _ s.val s.class_eq] at he
    simp only [mul_assoc,ssq,mul_one] at he
    exact he.symm
  apply rootAt_ne_bot Q split i (Q.simple j*Q.simple i)
  apply eq_bot_iff.mpr
  intro x hx
  have hxE : x ∈ E := hEC.symm ▸ hx
  have he := octagon_three_root_product_injective Q split hm i j hij
    (a₁ := (1,⟨x,hx⟩,1)) (a₂ := (1,1,⟨x,hxE⟩)) (by simp)
  have hx1 := congrArg (fun p => (p.2.1 : X ⧸ Q.D)) he
  exact mem_bot.mpr hx1
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
