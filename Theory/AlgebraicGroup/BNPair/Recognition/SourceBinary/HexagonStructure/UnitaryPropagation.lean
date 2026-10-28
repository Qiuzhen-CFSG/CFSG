module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.ShortIntervals
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MiddleFixed
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryLowerCentral
public import Mathlib.Algebra.Group.Pointwise.Set.Card

/-!
# Propagating unitary escape through the literal lower-central series

In the three middle roots A₁ A₂ A₃, adjacent factors commute and
[A₁,A₃] lies in A₂. Unique coordinates therefore show that the source
reflection moves every element of A₁ A₂ outside A₂, and likewise for
A₂ A₃. A noncentral outer coordinate of x produces such an element in
[x,V]. Thus an escape of W intersect the middle roots from
Z(A₁) A₂ Z(A₃) makes the actual rank-one action on [W,V] nontrivial.

The unitary section bound gives |[W,V]| >= 2^(6n). When the central
coordinate product is smaller, escape persists. The third lower-central
term lies in the middle roots; all later terms remain there and are
normalized by the actual rank-one group. Induction supplies the uniform
lower-central bound, contradicting finite two-group nilpotence.

The initial escape is an explicit remaining input: this module does not
supply the sharp unitary representation argument excluding the initial
central-coordinate configuration. The CFSG companion constructs every
other input from the original regular unitary factor markings.
Source: Fong--Seitz I (3G), pp.14--16, and (6D), pp.42--43.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem conjugate_comm (A B : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ n = ⁅rightConjugate A n,rightConjugate B n⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]

/-- The three literal middle roots satisfy the short-interval relations. -/
theorem middle_root_intervals (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    ⁅rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ ∧
    ⁅rootAt Q split i (Q.simple j*Q.simple i),rootAt Q split j (Q.simple i*Q.simple j)⁆ = ⊥ ∧
    ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i*Q.simple j)⁆ ≤
      rootAt Q split i (Q.simple j*Q.simple i) := by
  let n := representative (Q.simple i)
  have hBC := congrArg (fun A : Subgroup (X ⧸ Q.D) => rightConjugate A (n : X ⧸ Q.D))
    (adjacent_commutator_eq_bot Q split hm j i hij.symm hKj hKi)
  have hBD := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom)
    (distance_two_commutator_le Q split hm j i hij.symm hKj)
  change rightConjugate _ (n : X ⧸ Q.D) ≤ rightConjugate _ (n : X ⧸ Q.D) at hBD
  rw [conjugate_comm, rootAt_right Q split _ _ _ n (representative_spec _),
    GTwoSource.orthogonal_root_stabilizer Q split hm j i hij.symm,
    rootAt_right Q split _ _ _ n (representative_spec _)] at hBD
  rw [conjugate_comm, rootAt_right Q split _ _ _ n (representative_spec _)] at hBC
  change ⁅rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j*Q.simple i)⁆ = rightConjugate ⊥ (n : X ⧸ Q.D) at hBC
  have hBC' : ⁅rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ := by
    simpa only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot] using hBC
  refine ⟨hBC',?_,hBD⟩
  have hCD := congrArg (fun A : Subgroup (X ⧸ Q.D) => rightConjugate A
    (representative (Q.simple j) : X ⧸ Q.D)) hBC'
  rw [conjugate_comm,rootAt_right Q split _ _ _ _ (representative_spec _),
    rootAt_right Q split _ _ _ _ (representative_spec _),
    GTwoSource.orthogonal_root_stabilizer Q split hm i j hij] at hCD
  rw [commutator_comm]
  simpa only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot] using hCD

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

open Subgroup
open scoped Pointwise commutatorElement

private theorem commutator_three_coordinates {G : Type*} [Group G]
    (B C D : Subgroup G) (hBC : ⁅B,C⁆ = ⊥)
    (hBD : ⁅B,D⁆ ≤ C) (b : B) (c : C) (d : D) (y : B) :
    ∃ k : C, ⁅(b : G)*c*d,(y : G)⁆ = ⁅(b : G),(y : G)⁆*k := by
  have hdy : ⁅(d : G),(y : G)⁆ ∈ C := by
    have hh : ⁅D,B⁆ ≤ C := by rwa [commutator_comm]
    exact hh (commutator_mem_commutator d.property y.property)
  have hcy : ⁅(c : G),(y : G)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      ((commutator_eq_bot_iff_le_centralizer.mp hBC y.property) c c.property)
  have hbc : ⁅(b : G)*c,(y : G)⁆ = ⁅(b : G),(y : G)⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,hcy,mul_one,mul_inv_cancel,one_mul]
  let k : C := ⟨(c : G)*⁅(d : G),(y : G)⁆*(c : G)⁻¹,
    C.mul_mem (C.mul_mem c.property hdy) (C.inv_mem c.property)⟩
  have hbk : (b : G)*k*(b : G)⁻¹ = k := by
    have hh := commutator_eq_bot_iff_le_centralizer.mp hBC b.property k k.property
    rw [←hh,mul_inv_cancel_right]
  have he : ⁅(b : G)*c*d,(y : G)⁆ = (k : G)*⁅(b : G),(y : G)⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,hbc]
    have hh : ((b : G)*c)*⁅(d : G),(y : G)⁆*((b : G)*c)⁻¹ = (b : G)*k*(b : G)⁻¹ := by
      simp only [k,mul_inv_rev,mul_assoc]
    rw [hh,hbk]
  refine ⟨k,he.trans ?_⟩
  exact commutator_eq_bot_iff_le_centralizer.mp hBC
    (commutator_le_self B (commutator_mem_commutator b.property y.property)) k k.property

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem right_conj_mem {A : Subgroup (X ⧸ Q.D)} (s : X ⧸ Q.D)
    {x : X ⧸ Q.D} (hx : x ∈ A) : s⁻¹*x*s ∈ rightConjugate A s := by
  change s*(s⁻¹*x*s)*s⁻¹ ∈ A
  simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hx

/-- Reflection fixes an outer two-root coordinate only when its outer entry is trivial. -/
theorem middle_reflection_fixed_pair (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hBC : ⁅rootAt Q split j (Q.simple i),
      rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hCD : ⁅rootAt Q split i (Q.simple j*Q.simple i),
      rootAt Q split j (Q.simple i*Q.simple j)⁆ = ⊥) :
    (∀ (b : rootAt Q split j (Q.simple i))
      (c : rootAt Q split i (Q.simple j*Q.simple i)),
      (s.val : X ⧸ Q.D)⁻¹*((b : X ⧸ Q.D)*c)*s.val = (b : X ⧸ Q.D)*c → b=1) ∧
    (∀ (c : rootAt Q split i (Q.simple j*Q.simple i))
      (d : rootAt Q split j (Q.simple i*Q.simple j)),
      (s.val : X ⧸ Q.D)⁻¹*((c : X ⧸ Q.D)*d)*s.val = (c : X ⧸ Q.D)*d → d=1) := by
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let a := MulAut.conj (s.val : X ⧸ Q.D)⁻¹
  have hB (b : B) : a b ∈ D := by
    have hh := right_conj_mem Q (s.val : X ⧸ Q.D) b.property
    rw [rootAt_right Q split _ _ _ s.val s.class_eq] at hh
    simpa only [a,MulAut.conj_apply,inv_inv] using hh
  have hC (c : C) : a c ∈ C := by
    have hh := right_conj_mem Q (s.val : X ⧸ Q.D) c.property
    rw [rootAt_right Q split _ _ _ s.val s.class_eq,
      GTwoSource.orthogonal_root_stabilizer Q split hm i j hij] at hh
    simpa only [a,MulAut.conj_apply,inv_inv] using hh
  have hD (d : D) : a d ∈ B := by
    have hh := right_conj_mem Q (s.val : X ⧸ Q.D) d.property
    have hs : Q.simple j*Q.simple j = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem j)).2
    rw [rootAt_right Q split _ _ _ s.val s.class_eq,mul_assoc,hs,mul_one] at hh
    simpa only [a,MulAut.conj_apply,inv_inv] using hh
  constructor
  · intro b c hfix
    let c' : C := ⟨a c,hC c⟩
    let d' : D := ⟨a b,hB b⟩
    have he : (b : X ⧸ Q.D)*c = (c' : X ⧸ Q.D)*d' := by
      have hh : a ((b : X ⧸ Q.D)*c) = (b : X ⧸ Q.D)*c := by simpa only [a,MulAut.conj_apply,inv_inv] using hfix
      rw [map_mul] at hh
      exact hh.symm.trans (commutator_eq_bot_iff_le_centralizer.mp hCD c'.property d' d'.property)
    have hh : (b,c,(1 : D)) = ((1 : B),c',d') := by
      apply (middleCoordinates Q split hm i j hij).injective
      apply Subtype.ext
      simpa only [middleCoordinates_apply,coe_one,mul_one,one_mul] using he
    exact congrArg Prod.fst hh
  · intro c d hfix
    let b' : B := ⟨a d,hD d⟩
    let c' : C := ⟨a c,hC c⟩
    have he : (c : X ⧸ Q.D)*d = (b' : X ⧸ Q.D)*c' := by
      have hh : a ((c : X ⧸ Q.D)*d) = (c : X ⧸ Q.D)*d := by simpa only [a,MulAut.conj_apply,inv_inv] using hfix
      rw [map_mul] at hh
      exact hh.symm.trans (commutator_eq_bot_iff_le_centralizer.mp hBC b'.property c' c'.property)
    have hh : ((1 : B),c,d) = (b',c',(1 : D)) := by
      apply (middleCoordinates Q split hm i j hij).injective
      apply Subtype.ext
      simpa only [middleCoordinates_apply,coe_one,mul_one,one_mul] using he
    exact congrArg (fun z : B × C × D => z.2.2) hh

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

private theorem reverse_three_coordinates {G : Type*} [Group G]
    (B C D : Subgroup G) (hBC : ⁅B,C⁆ = ⊥) (hCD : ⁅C,D⁆ = ⊥)
    (hBD : ⁅B,D⁆ ≤ C) (b : B) (c : C) (d : D) :
    ∃ k : C, (b : G)*c*d = (d : G)*k*b := by
  have hbd : ⁅(b : G),(d : G)⁆ ∈ C := hBD (commutator_mem_commutator b.property d.property)
  let k : C := ⟨(c : G)*⁅(b : G),(d : G)⁆,C.mul_mem c.property hbd⟩
  have he : (b : G)*(d : G) = ⁅(b : G),(d : G)⁆*d*b := by
    simp only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one]
  have hbc := commutator_eq_bot_iff_le_centralizer.mp hBC b.property c c.property
  have hkd := commutator_eq_bot_iff_le_centralizer.mp hCD k.property d d.property
  refine ⟨k,?_⟩
  calc
    (b : G)*c*d = (c : G)*(b*d) := by rw [←hbc,mul_assoc]
    _ = (c : G)*(⁅(b : G),(d : G)⁆*d*b) := by rw [he]
    _ = (k : G)*d*b := by simp only [k,mul_assoc]
    _ = (d : G)*k*b := by rw [←hkd]

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The literal product Z(A₁) A₂ Z(A₃) in the three middle roots. -/
@[expose] def middleCentralProduct (i j : Fin 2) : Set (X ⧸ Q.D) :=
  ((center (rootAt Q split j (Q.simple i))).map
    (rootAt Q split j (Q.simple i)).subtype : Set (X ⧸ Q.D)) *
  (rootAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
  ((center (rootAt Q split j (Q.simple i*Q.simple j))).map
    (rootAt Q split j (Q.simple i*Q.simple j)).subtype : Set (X ⧸ Q.D))

/-- If reflection fixes every commutator, both outer coordinates are central. -/
theorem middle_commutator_fixed_coordinates (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (W : Subgroup (X ⧸ Q.D))
    (hfix : ∀ z ∈ ⁅W,simpleRemainder Q split j⁆,
      (s.val : X ⧸ Q.D)⁻¹*z*s.val = z) :
    (W ⊓ middleRoots Q split i j : Set (X ⧸ Q.D)) ⊆ middleCentralProduct Q split i j := by
  obtain ⟨hBC,hCD,hBD⟩ := middle_root_intervals Q split hm i j hij hKi hKj
  obtain ⟨hleft,hright⟩ := middle_reflection_fixed_pair Q split hm i j hij s hBC hCD
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  have hBV : B ≤ simpleRemainder Q split j :=
    (show B ≤ middleRoots Q split i j from le_sup_left.trans le_sup_left).trans
      (middleRoots_le_remainder Q split hm i j hij)
  have hDV : D ≤ simpleRemainder Q split j :=
    (show D ≤ middleRoots Q split i j from le_sup_right).trans
      (middleRoots_le_remainder Q split hm i j hij)
  intro x hx
  obtain ⟨⟨b,c,d⟩,he⟩ := (middleCoordinates Q split hm i j hij).surjective ⟨x,hx.2⟩
  have he' : (b : X ⧸ Q.D)*c*d = x := by
    simpa only [middleCoordinates_apply] using congrArg Subtype.val he
  have hb : b ∈ center B := by
    rw [mem_center_iff]
    intro y
    obtain ⟨k,hk⟩ := commutator_three_coordinates B C D hBC hBD b c d y
    have hz := hfix _ (commutator_mem_commutator hx.1 (hBV y.property))
    rw [←he',hk] at hz
    have hh := hleft ⟨⁅(b : X ⧸ Q.D),(y : X ⧸ Q.D)⁆,
      commutator_le_self B (commutator_mem_commutator b.property y.property)⟩ k hz
    apply Subtype.ext
    exact (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hh)).symm
  have hd : d ∈ center D := by
    rw [mem_center_iff]
    intro y
    obtain ⟨k,hk⟩ := reverse_three_coordinates B C D hBC hCD hBD b c d
    have hDC : ⁅D,C⁆ = ⊥ := by rwa [commutator_comm]
    have hDB : ⁅D,B⁆ ≤ C := by rwa [commutator_comm]
    obtain ⟨l,hl⟩ := commutator_three_coordinates D C B hDC hDB d k b y
    have hz := hfix _ (commutator_mem_commutator hx.1 (hDV y.property))
    rw [←he',hk,hl] at hz
    let z : D := ⟨⁅(d : X ⧸ Q.D),(y : X ⧸ Q.D)⁆,
      commutator_le_self D (commutator_mem_commutator d.property y.property)⟩
    have hzl : (z : X ⧸ Q.D)*l = (l : X ⧸ Q.D)*z :=
      commutator_eq_bot_iff_le_centralizer.mp hCD l.property z z.property
    change (s.val : X ⧸ Q.D)⁻¹*((z : X ⧸ Q.D)*l)*s.val = (z : X ⧸ Q.D)*l at hz
    rw [hzl] at hz
    have hh := hright l z hz
    apply Subtype.ext
    exact (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hh)).symm
  exact ⟨(b : X ⧸ Q.D)*c,⟨b,mem_map_of_mem B.subtype hb,c,c.property,rfl⟩,
    d,mem_map_of_mem D.subtype hd,he'⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource BenderSuzuki.MatrixGroups
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The actual commutator with the radical, with trivial section denominator. -/
@[expose] def radicalCommutatorSection (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (W : Subgroup (X ⧸ Q.D)) (hWV : W ≤ simpleRemainder Q split j)
    (hWR : rankOne Q split j ≤ normalizer (W : Set (X ⧸ Q.D))) :
    RootSection Q split j where
  numerator := ⁅W,simpleRemainder Q split j⁆
  le_radical := (commutator_mono hWV le_rfl).trans (commutator_le_self _)
  normalized := by
    intro r hr
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hWR hr),
      mem_normalizer_iff_map_conj_eq.mp
        (remainder_parabolic_normalizes Q split j hKj (rankOne_le_parabolic Q split j hr))]
  denominator := ⊥
  invariant _ := map_bot _

/-- An escape in W intersect the middle roots forces the actual reflection
 to act nontrivially on [W,V]. In particular W itself need not lie in the
 middle roots; this is also the initial derived-subgroup application. -/
theorem radicalCommutatorSection_action_ne_one (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (W : Subgroup (X ⧸ Q.D)) (hWV : W ≤ simpleRemainder Q split j)
    (hWR : rankOne Q split j ≤ normalizer (W : Set (X ⧸ Q.D)))
    (hescape : ¬ (W ⊓ middleRoots Q split i j : Set (X ⧸ Q.D)) ⊆
      middleCentralProduct Q split i j) :
    (radicalCommutatorSection Q split j hKj W hWV hWR).action ≠ 1 := by
  let d := radicalCommutatorSection Q split j hKj W hWV hWR
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  intro he
  apply hescape
  apply middle_commutator_fixed_coordinates Q split hm i j hij s hKi hKj W
  intro z hz
  let x : d.numerator := ⟨z,hz⟩
  have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk x))
    (show d.action r⁻¹ = 1 from by rw [he]; rfl)
  rw [d.action_mk] at hh
  have hx : d.numeratorAction r⁻¹ x = x := congrArg QuotientGroup.quotientBot hh
  have hh := congrArg Subtype.val hx
  rw [d.numeratorAction_apply] at hh
  simpa only [r,coe_inv,inv_inv] using hh

/-- Literal escape supplies the unitary minimum bound for the next
 commutator. This is the source propagation step before comparing its
 cardinality with Z(A₁) A₂ Z(A₃). -/
theorem unitary_radicalCommutator_card_bound (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (W : Subgroup (X ⧸ Q.D)) (hWV : W ≤ simpleRemainder Q split j)
    (hWR : rankOne Q split j ≤ normalizer (W : Set (X ⧸ Q.D)))
    (hescape : ¬ (W ⊓ middleRoots Q split i j : Set (X ⧸ Q.D)) ⊆
      middleCentralProduct Q split i j) :
    2^(6*n) ≤ Nat.card (⁅W,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) := by
  let d := radicalCommutatorSection Q split j hKj W hWV hWR
  have hq : Nat.card d.EffectiveCarrier ≤ Nat.card d.numerator :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective d.effectiveDenominator)
  exact (unitary_section_card_bound Q split j J hn hcard hconj σ hσ d
    (radicalCommutatorSection_action_ne_one Q split hm i j hij s hKi hKj W hWV hWR hescape)).trans hq

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource BenderSuzuki.MatrixGroups
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- A cardinal bound for the literal central-coordinate product. -/
theorem middleCentralProduct_card_le (i j : Fin 2) :
    Nat.card (middleCentralProduct Q split i j) ≤
      Nat.card (center (simpleRoot Q split j))^2 * Nat.card (simpleRoot Q split i) := by
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  have hB : Nat.card ((center B).map B.subtype) = Nat.card (center (simpleRoot Q split j)) := by
    rw [←Nat.card_congr ((center B).equivMapOfInjective B.subtype B.subtype_injective).toEquiv]
    exact Nat.card_congr (Subgroup.centerCongr
      (RootAction.conjugateEquiv (simpleRoot Q split j) (representative (Q.simple i)))).toEquiv
  have hD : Nat.card ((center D).map D.subtype) = Nat.card (center (simpleRoot Q split j)) := by
    rw [←Nat.card_congr ((center D).equivMapOfInjective D.subtype D.subtype_injective).toEquiv]
    exact Nat.card_congr (Subgroup.centerCongr
      (RootAction.conjugateEquiv (simpleRoot Q split j) (representative (Q.simple i*Q.simple j)))).toEquiv
  have hC : Nat.card C = Nat.card (simpleRoot Q split i) := card_rightConjugate _ _
  have h1 := Set.natCard_mul_le (s := ((center B).map B.subtype : Set (X ⧸ Q.D)))
    (t := (C : Set (X ⧸ Q.D)))
  have h2 := Set.natCard_mul_le
    (s := ((center B).map B.subtype : Set (X ⧸ Q.D)) * (C : Set (X ⧸ Q.D)))
    (t := ((center D).map D.subtype : Set (X ⧸ Q.D)))
  change Nat.card (middleCentralProduct Q split i j) ≤ _ at h2
  calc
    Nat.card (middleCentralProduct Q split i j) ≤
      Nat.card ((center B).map B.subtype) * Nat.card C * Nat.card ((center D).map D.subtype) :=
      h2.trans (Nat.mul_le_mul_right _ h1)
    _ = _ := by rw [hB,hC,hD]; ring

private theorem radical_lowerCentral_normalized (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) (k : ℕ) :
    rankOne Q split j ≤ normalizer
      (((simpleRemainder Q split j).lowerCentralSeries k : Subgroup (X ⧸ Q.D)) : Set _) := by
  intro r hr
  rw [mem_normalizer_iff_map_conj_eq,map_lowerCentralSeries,
    mem_normalizer_iff_map_conj_eq.mp (remainder_parabolic_normalizes Q split j hKj
      (rankOne_le_parabolic Q split j hr))]

/-- The source escape propagates along every actual lower-central term.
 Only the initial escape and the small central-coordinate product are extra
 inputs; the recurrence, normalization, and middle-root placement are proved. -/
theorem unitary_lowerCentral_bound_of_escape (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hclass : ⁅⁅simpleRoot Q split i,simpleRoot Q split i⁆,simpleRoot Q split i⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hsmall : Nat.card (middleCentralProduct Q split i j) < 2^(6*n))
    (hescape : ¬ ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ⊓
      middleRoots Q split i j : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) ⊆ middleCentralProduct Q split i j) :
    ∀ k : ℕ, 2^(6*n) ≤ Nat.card ((simpleRemainder Q split j).lowerCentralSeries k) := by
  let V := simpleRemainder Q split j
  have hmid : ∀ k : ℕ, V.lowerCentralSeries (k+2) ≤ middleRoots Q split i j := by
    intro k
    exact (V.lowerCentralSeries_antitone (by omega : 2 ≤ k+2)).trans
      (radical_triple_le_middle Q split hm i j hij hKi hclass)
  have hbound : ∀ k : ℕ, 2^(6*n) ≤ Nat.card (V.lowerCentralSeries (k+2)) := by
    intro k
    induction k with
    | zero =>
      exact unitary_radicalCommutator_card_bound Q split hm i j hij s hKi hKj J hn hcard hconj σ hσ
        (V.lowerCentralSeries 1) (V.lowerCentralSeries_le_self 1)
        (radical_lowerCentral_normalized Q split j hKj 1) hescape
    | succ k ih =>
      have hesc : ¬ (V.lowerCentralSeries (k+2) ⊓ middleRoots Q split i j : Set (X ⧸ Q.D)) ⊆
          middleCentralProduct Q split i j := by
        intro he
        have hle : (V.lowerCentralSeries (k+2) : Set (X ⧸ Q.D)) ⊆ middleCentralProduct Q split i j :=
          fun x hx => he ⟨hx,hmid k hx⟩
        have hc := Nat.card_le_card_of_injective (Set.inclusion hle) (Set.inclusion_injective hle)
        exact (not_le_of_gt hsmall) (ih.trans hc)
      exact unitary_radicalCommutator_card_bound Q split hm i j hij s hKi hKj J hn hcard hconj σ hσ
        (V.lowerCentralSeries (k+2)) (V.lowerCentralSeries_le_self (k+2))
        (radical_lowerCentral_normalized Q split j hKj (k+2)) hesc
  intro k
  exact (hbound k).trans (card_le_of_le
    (V.lowerCentralSeries_antitone (by omega : k ≤ k+2)))

/-- The initial source escape contradicts finite two-group nilpotence once
 the central-coordinate product is too small to contain the next section. -/
theorem unitary_escape_contradiction (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hclass : ⁅⁅simpleRoot Q split i,simpleRoot Q split i⁆,simpleRoot Q split i⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hsmall : Nat.card (middleCentralProduct Q split i j) < 2^(6*n))
    (hescape : ¬ ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ⊓
      middleRoots Q split i j : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) ⊆ middleCentralProduct Q split i j) : False := by
  let V := simpleRemainder Q split j
  let : Group.IsNilpotent V := (split.isTwo.to_le (show V ≤ split.U from inf_le_left)).isNilpotent
  apply lowerCentralSeries_card_contradiction V (c := 2^(6*n)) (by
    calc
      2 = 2^1 := by norm_num
      _ ≤ 2^(6*n) := Nat.pow_le_pow_right (by decide) (by omega))
  exact unitary_lowerCentral_bound_of_escape Q split hm i j hij s hKi hKj hclass
    J hn hcard hconj σ hσ hsmall hescape

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
