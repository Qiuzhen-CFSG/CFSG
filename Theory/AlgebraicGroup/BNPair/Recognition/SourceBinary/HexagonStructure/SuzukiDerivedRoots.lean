module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiDerivedRadical

/-!
# Four exact root intersections with the Suzuki derived radical

The actual derived radical has order q⁵ or q⁶ and a moving rank-one action.
If its own Frattini subgroup had a moving action, two effective quotients
would each have order at least q⁴, contradicting this order bound. Thus the
actor centralizes the second Frattini layer of the radical.

Each of the four nonmiddle roots is exchanged with a disjoint root by the
actual source reflection. Its nontrivial square would detect movement on
that forbidden layer if the whole root lay in the derived radical. This
excludes all four roots. Their simple Cartan Frattini quotients consequently
embed in the radical quotient, giving the exact intersections with the
derived radical. The Frattini subgroups of all five roots are contained in it.
In the smaller-order branch, unique root coordinates then identify the
derived radical with their exact ordered five-factor product.

Source: Fong--Seitz I (6C), printed p.41, the paragraph beginning with the
derived subgroup. The larger-order root-product decomposition, placement
of the unique natural composition factor, and triple-commutator contradiction
remain separate obligations. All words and actions use the same quotient.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- A square in a root moved to a disjoint root detects action on the
Frattini subgroup of any actual invariant source numerator containing it. -/
theorem reflection_moves_frattini_section {j : Fin 2}
    (s : RootReflection Q split j) (d : RootSection Q split j)
    (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ d.numerator)
    (hdis : Disjoint A (rightConjugate A (s.val : X ⧸ Q.D)))
    (a : A) (ha : a^2 ≠ 1) :
    (frattiniSection Q split j d).action ≠ 1 := by
  let f := frattiniSection Q split j d
  let v : d.numerator := inclusion hA a
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  let x : f.numerator := ⟨(a : X ⧸ Q.D)^2,
    ⟨v^2,pth_power_mem_frattini_of_isPGroup (p := 2) v,rfl⟩⟩
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  intro he
  have hei : f.action r⁻¹ = 1 := by rw [he]; rfl
  have hx : f.numeratorAction r⁻¹ x = x := by
    have hh := congrArg (fun z : MulAut f.Carrier => z (QuotientGroup.mk x)) hei
    rw [f.action_mk] at hh
    exact congrArg QuotientGroup.quotientBot hh
  have hxa : (s.val : X ⧸ Q.D)⁻¹*(a : X ⧸ Q.D)^2*s.val = (a : X ⧸ Q.D)^2 := by
    have hh := congrArg Subtype.val hx
    rw [f.numeratorAction_apply] at hh
    simpa only [coe_inv,inv_inv] using hh
  have hconj : (a : X ⧸ Q.D)^2 ∈ rightConjugate A (s.val : X ⧸ Q.D) := by
    rw [←hxa]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*(a : X ⧸ Q.D)^2*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ A
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using pow_mem a.property 2
  exact ha (Subtype.ext (disjoint_def.mp hdis (pow_mem a.property 2) hconj))

/-- A moving Suzuki section with trivial denominator and order less than
q⁸ has trivial action on the Frattini subgroup of its numerator. Otherwise
two faithful effective quotients would each have order at least q⁴. -/
theorem suzuki_small_section_frattini_action_eq_one (j : Fin 2)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (d : RootSection Q split j) (hden : d.denominator = ⊥)
    (hmove : d.action ≠ 1) (hsmall : Nat.card d.numerator < 2^(8*(2*m+1))) :
    (frattiniSection Q split j d).action = 1 := by
  by_contra hn
  let f := frattiniSection Q split j d
  have h1 := suzuki_section_card_bound Q split j hm μ d hmove
  have h2 := suzuki_section_card_bound Q split j hm μ f hn
  have he : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq,hden,sup_bot_eq]
  change 2^(4*(2*m+1)) ≤ d.effectiveDenominator.index at h1
  rw [he] at h1
  have hc : Nat.card f.EffectiveCarrier ≤ Nat.card (frattini d.numerator) := by
    calc
      Nat.card f.EffectiveCarrier ≤ Nat.card f.numerator :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ = Nat.card (frattini d.numerator) :=
        Nat.card_congr ((frattini d.numerator).equivMapOfInjective
          d.numerator.subtype d.numerator.subtype_injective).symm.toEquiv
  have hb : 2^(8*(2*m+1)) ≤ Nat.card d.numerator := by
    calc
      2^(8*(2*m+1)) = 2^(4*(2*m+1))*2^(4*(2*m+1)) := by
        rw [←pow_add]; congr 1; omega
      _ ≤ (frattini d.numerator).index*Nat.card (frattini d.numerator) :=
        Nat.mul_le_mul h1 (h2.trans hc)
      _ = Nat.card d.numerator := (frattini d.numerator).index_mul_card
  exact (not_lt_of_ge hb) hsmall

/-- The second Frattini layer of the actual Suzuki radical is centralized
by its actual root-generated rank-one actor. -/
theorem suzuki_second_frattini_radical_action_eq_one (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    (frattiniSection Q split j (frattiniSection Q split j
      (radicalSection Q split j hKj))).action = 1 := by
  let f := frattiniSection Q split j (radicalSection Q split j hKj)
  apply suzuki_small_section_frattini_action_eq_one Q split j hm μj f rfl
    (suzuki_frattini_radical_action_ne_one Q split j hhex i hij
      (UnitarySource.actorReflection Q split j) hKj νj)
  rw [show f.numerator = ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ from
    suzuki_frattiniSection_numerator_eq_derived Q split hhex i j hij hKj hm hm νi νj]
  rcases suzuki_derived_radical_card Q split hhex i j hij hKi hKj hm μi μj νi νj with h | h
  · rw [h]; exact Nat.pow_lt_pow_right (by decide) (by omega)
  · rw [h]; exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- Each of the four nonmiddle roots is disjoint from its image under the
source reflection. This uses the literal five-root words. -/
theorem radical_nonmiddle_root_disjoint (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (t : Fin 5) (ht : t ≠ 2) :
    Disjoint (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t))
      (rightConjugate (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t))
        (s.val : X ⧸ Q.D)) := by
  have hs : Q.simple j*Q.simple j = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem j)).2
  have h0 : Disjoint (simpleRoot Q split i) (rootAt Q split i (Q.simple j)) := by
    apply (simpleRoot_disjoint_remainder Q split i).mono_right
    exact (show rootAt Q split i (Q.simple j) ≤ middleRoots Q split j i from
      le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hhex j i hij.symm)
  have h1 := exchanged_roots_disjoint Q split hhex j i hij.symm
  rw [rootAt_right Q split _ _ _ s.val s.class_eq]
  fin_cases t <;> dsimp [radicalRootKind,radicalRootWord] at *
  · simpa only [one_mul,rootAt_one] using h0
  · exact h1
  · exact (ht rfl).elim
  · rw [mul_assoc,hs,mul_one]
    exact h1.symm
  · rw [hs,rootAt_one]
    exact h0.symm

/-- The derived radical contains none of the four whole nonmiddle roots.
A nontrivial root square would give forbidden movement on Φ(Φ(U_sj)). -/
theorem suzuki_nonmiddle_root_not_le_derived (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (t : Fin 5) (ht : t ≠ 2) :
    ¬ rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ≤
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
  let f := frattiniSection Q split j (radicalSection Q split j hKj)
  let A := rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)
  let e := RootAction.conjugateEquiv
    (simpleRoot Q split (radicalRootKind i j t)) (representative (radicalRootWord Q i j t))
  have hν : Nonempty (simpleRoot Q split (radicalRootKind i j t) ≃* SuzukiRootSubgroup m) := by
    by_cases hk : radicalRootKind i j t = i
    · exact ⟨(MulEquiv.subgroupCongr (congrArg (simpleRoot Q split) hk)).trans νi⟩
    · have hk' : radicalRootKind i j t = j := by omega
      exact ⟨(MulEquiv.subgroupCongr (congrArg (simpleRoot Q split) hk')).trans νj⟩
  obtain ⟨ν⟩ := hν
  let μ : A ≃* SuzukiRootSubgroup m := e.trans ν
  obtain ⟨a,ha⟩ := suzuki_root_exists_nontrivial_square m
  have ha' : (μ.symm a)^2 ≠ 1 := by
    intro he
    apply ha
    have hh := congrArg μ he
    simpa only [map_pow,map_one,MulEquiv.apply_symm_apply] using hh
  intro hle
  have hAf : A ≤ f.numerator := by
    rw [show f.numerator = ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ from
      suzuki_frattiniSection_numerator_eq_derived Q split hhex i j hij hKj hm hm νi νj]
    exact hle
  exact reflection_moves_frattini_section Q split (UnitarySource.actorReflection Q split j) f A hAf
    (radical_nonmiddle_root_disjoint Q split hhex i j hij _ t ht) (μ.symm a) ha'
    (suzuki_second_frattini_radical_action_eq_one Q split hhex i j hij hKi hKj hm μi μj νi νj)


/-- All five root Frattini subgroups lie in the actual derived radical. -/
theorem suzuki_radical_root_frattini_le_derived (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup n) (t : Fin 5) :
    (frattini (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t))).map
      (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)).subtype ≤
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
  let V := simpleRemainder Q split j
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hh := map_mono (f := V.subtype)
    (frattini_map_le_of_isPGroup (p := 2) (inclusion (radicalRoot_le Q split hhex i j hij t)))
  rw [map_map] at hh
  have he : V.subtype.comp (inclusion (radicalRoot_le Q split hhex i j hij t)) =
      (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)).subtype := rfl
  rw [he] at hh
  rw [suzuki_radical_frattini_eq_commutator Q split hhex i j hij hm hn νi νj,
    map_subtype_commutator] at hh
  exact hh

/-- The four nonmiddle root quotients embed into the actual radical
Frattini quotient by their literal Cartan-equivariant inclusion maps. -/
theorem suzuki_nonmiddle_root_intertwiner_injective (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (t : Fin 5) (ht : t ≠ 2) :
    Function.Injective (radicalRootIntertwiner Q split hhex i j hij hKj t) := by
  let k := radicalRootKind i j t
  let w := radicalRootWord Q i j t
  let A := rootAt Q split k w
  let V := simpleRemainder Q split j
  let d := radicalSection Q split j hKj
  let f := radicalRootIntertwiner Q split hhex i j hij hKj t
  have hir : (rootAtCartanFrattiniRepresentation Q split k w).IsIrreducible := by
    by_cases hk : k = i
    · rw [hk]
      exact (suzuki_rootAt_cartan_frattini_irreducible Q split i hKi hm μi νi w).1
    · have hk' : k = j := by omega
      rw [hk']
      exact (suzuki_rootAt_cartan_frattini_irreducible Q split j hKj hm μj νj w).1
  let := hir
  apply (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right
  intro hf
  apply suzuki_nonmiddle_root_not_le_derived Q split hhex i j hij hKi hKj hm μi μj νi νj t ht
  intro a ha
  let x : A := ⟨a,ha⟩
  have hx := congrArg (fun z => z (Additive.ofMul (QuotientGroup.mk x))) hf
  have hz : (QuotientGroup.mk' d.effectiveDenominator)
      (inclusion (radicalRoot_le Q split hhex i j hij t) x) = 1 :=
    congrArg Additive.toMul hx
  have hp := (QuotientGroup.eq_one_iff _).mp hz
  rw [suzuki_radical_effectiveDenominator Q split j hKj,
    suzuki_radical_frattini_eq_commutator Q split hhex i j hij hm hm νi νj] at hp
  rw [←map_subtype_commutator]
  exact mem_map_of_mem V.subtype hp

/-- The intersection of each nonmiddle root with the derived radical is
exactly that root's Frattini subgroup, with the ambient inclusion retained. -/
theorem suzuki_nonmiddle_root_inf_derived (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (t : Fin 5) (ht : t ≠ 2) :
    rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⊓
        ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
      (frattini (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t))).map
        (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)).subtype := by
  let A := rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)
  let V := simpleRemainder Q split j
  let d := radicalSection Q split j hKj
  let f := radicalRootIntertwiner Q split hhex i j hij hKj t
  apply le_antisymm
  · rintro a ⟨ha,hD⟩
    let x : A := ⟨a,ha⟩
    let v : V := inclusion (radicalRoot_le Q split hhex i j hij t) x
    have hv : v ∈ d.effectiveDenominator := by
      rw [suzuki_radical_effectiveDenominator Q split j hKj,
        suzuki_radical_frattini_eq_commutator Q split hhex i j hij hm hm νi νj]
      rw [←map_subtype_commutator] at hD
      exact (mem_map_iff_mem V.subtype_injective).mp hD
    have he : f (Additive.ofMul (QuotientGroup.mk x)) = f 0 := by
      rw [map_zero]
      apply Additive.toMul.injective
      exact (QuotientGroup.eq_one_iff _).mpr hv
    have hx : (QuotientGroup.mk' (frattini A)) x = 1 :=
      congrArg Additive.toMul
        (suzuki_nonmiddle_root_intertwiner_injective Q split hhex i j hij hKi hKj hm μi μj νi νj t ht he)
    exact mem_map_of_mem A.subtype ((QuotientGroup.eq_one_iff _).mp hx)
  · exact le_inf (map_subtype_le _) (suzuki_radical_root_frattini_le_derived Q split hhex i j hij hm hm νi νj t)

open scoped Pointwise

/-- The Frattini subgroup of a canonical conjugate root, in the same ambient group. -/
@[expose] def rootFrattiniAt (i : Fin 2) (w : Weyl Q) : Subgroup (X ⧸ Q.D) :=
  (frattini (rootAt Q split i w)).map (rootAt Q split i w).subtype

/-- The ordered product of the five root Frattini subgroups. This is a set
product until its equality with the actual derived subgroup is proved. -/
@[expose] def radicalRootFrattiniProduct (i j : Fin 2) : Set (X ⧸ Q.D) :=
  (rootFrattiniAt Q split i 1 : Set (X ⧸ Q.D)) *
  (rootFrattiniAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
  (rootFrattiniAt Q split i (Q.simple j*Q.simple i) : Set (X ⧸ Q.D)) *
  (rootFrattiniAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) *
  (rootFrattiniAt Q split i (Q.simple j) : Set (X ⧸ Q.D))

theorem suzuki_rootAt_frattini_card (i : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (hm : 0 < m) (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m) (w : Weyl Q) :
    Nat.card (frattini (rootAt Q split i w)) = 2^(2*m+1) := by
  let A := rootAt Q split i w
  have hq := (suzuki_rootAt_cartan_frattini_regular Q split i hKi hm μ ν w).1
  have ha : Nat.card A = (2^(2*m+1))^2 := by
    change Nat.card (rootAt Q split i w) = _
    rw [rootAt,card_rightConjugate,Nat.card_congr ν.toEquiv]
    exact suzukiRootSubgroup_card m hm
  have hp := (frattini A).index_mul_card
  change Nat.card (A ⧸ frattini A)*Nat.card (frattini A) = Nat.card A at hp
  rw [hq,ha,pow_two] at hp
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 2)) hp

/-- In the smaller derived-order branch, unique root coordinates force the
exact five-Frattini product asserted in (6C). -/
theorem suzuki_derived_small_order_product (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    (hcard : Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
      Subgroup (X ⧸ Q.D)) = 2^(5*(2*m+1))) :
    ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      radicalRootFrattiniProduct Q split i j := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let E := rootAt Q split i (Q.simple j)
  let J := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
  let F := frattini A × frattini B × frattini C × frattini D × frattini E
  have hroot := suzuki_radical_root_frattini_le_derived Q split hhex i j hij hm hm νi νj
  have hA : (frattini A).map A.subtype ≤ J := by
    have hh := hroot 0
    change (frattini (rootAt Q split i 1)).map (rootAt Q split i 1).subtype ≤ J at hh
    rw [rootAt_one] at hh
    exact hh
  have hB : (frattini B).map B.subtype ≤ J := hroot 1
  have hC : (frattini C).map C.subtype ≤ J := hroot 2
  have hD : (frattini D).map D.subtype ≤ J := hroot 3
  have hE : (frattini E).map E.subtype ≤ J := hroot 4
  let f : F → J := fun z => ⟨(z.1.val : X ⧸ Q.D)*z.2.1.val*z.2.2.1.val*z.2.2.2.1.val*z.2.2.2.2.val,
    mul_mem (mul_mem (mul_mem (mul_mem
      (hA (mem_map_of_mem A.subtype z.1.property))
      (hB (mem_map_of_mem B.subtype z.2.1.property)))
      (hC (mem_map_of_mem C.subtype z.2.2.1.property)))
      (hD (mem_map_of_mem D.subtype z.2.2.2.1.property)))
      (hE (mem_map_of_mem E.subtype z.2.2.2.2.property))⟩
  have hf : Function.Injective f := by
    intro z y he
    have ht : (z.1.val,z.2.1.val,z.2.2.1.val,z.2.2.2.1.val,z.2.2.2.2.val) =
        (y.1.val,y.2.1.val,y.2.2.1.val,y.2.2.2.1.val,y.2.2.2.2.val) := by
      apply (radicalCoordinates Q split hhex i j hij).injective
      apply Subtype.ext
      rw [radicalCoordinates_apply,radicalCoordinates_apply]
      exact congrArg Subtype.val he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst ht))
      (Prod.ext (Subtype.ext (congrArg (fun z => z.2.1) ht))
        (Prod.ext (Subtype.ext (congrArg (fun z => z.2.2.1) ht))
          (Prod.ext (Subtype.ext (congrArg (fun z => z.2.2.2.1) ht))
            (Subtype.ext (congrArg (fun z => z.2.2.2.2) ht)))))
  change Nat.card J = _ at hcard
  have hc : Nat.card F = Nat.card J := by
    have hcA : Nat.card (frattini A) = 2^(2*m+1) := by
      have hh := suzuki_rootAt_frattini_card Q split i hKi hm μi νi 1
      rw [rootAt_one] at hh
      exact hh
    change Nat.card (frattini A × frattini B × frattini C × frattini D × frattini E) = _
    simp only [Nat.card_prod,hcA,
      show Nat.card (frattini B) = _ from suzuki_rootAt_frattini_card Q split j hKj hm μj νj _,
      show Nat.card (frattini C) = _ from suzuki_rootAt_frattini_card Q split i hKi hm μi νi _,
      show Nat.card (frattini D) = _ from suzuki_rootAt_frattini_card Q split j hKj hm μj νj _,
      show Nat.card (frattini E) = _ from suzuki_rootAt_frattini_card Q split i hKi hm μi νi _,hcard]
    simp only [←pow_add]
    congr 1
    omega
  have hsur := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hc⟩).surjective
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨⟨a,b,c,d,e⟩,he⟩ := hsur ⟨x,hx⟩
    have ha0 : (a.val : X ⧸ Q.D) ∈ rootFrattiniAt Q split i 1 := by
      unfold rootFrattiniAt
      rw [rootAt_one]
      exact mem_map_of_mem A.subtype a.property
    exact ⟨_,⟨_,⟨_,⟨_,ha0,_,mem_map_of_mem B.subtype b.property,rfl⟩,
      _,mem_map_of_mem C.subtype c.property,rfl⟩,_,mem_map_of_mem D.subtype d.property,rfl⟩,
        _,mem_map_of_mem E.subtype e.property,congrArg Subtype.val he⟩
  · rintro x ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd,rfl⟩,e,he,rfl⟩
    have ha' : a ∈ (frattini A).map A.subtype := by
      unfold rootFrattiniAt at ha
      rw [rootAt_one] at ha
      exact ha
    exact mul_mem (mul_mem (mul_mem (mul_mem (hA ha') (hB hb)) (hC hc)) (hD hd)) (hE he)

/-- The smaller-order branch is completely identified. The larger order
retains the further source duty of adjoining precisely the middle root. -/
theorem suzuki_derived_product_or_large_order (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μi : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (μj : rankOne Q split j ≃* SuzukiMatrixGroup m)
    (νi : simpleRoot Q split i ≃* SuzukiRootSubgroup m)
    (νj : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
        radicalRootFrattiniProduct Q split i j ∨
      Nat.card (⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ :
        Subgroup (X ⧸ Q.D)) = 2^(6*(2*m+1)) := by
  rcases suzuki_derived_radical_card Q split hhex i j hij hKi hKj hm μi μj νi νj with h | h
  · exact Or.inl (suzuki_derived_small_order_product Q split hhex i j hij hKi hKj hm μi μj νi νj h)
  · exact Or.inr h

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
