module

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.OrderReduction
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.Exclude1512.Generators
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.Exclude1512.PairCases
public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.Exclude1512.SeedOrders
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple

/-!
# Excluding order 1512 in the simple degree-nine action

In a triple-transitive action of order 1512, a three-point stabilizer has
order three. Hence an involution fixes fewer than three points; its odd
number of fixed points in degree nine makes the fixed point unique.
Normalize a seven-cycle to `(2 3 4 5 6 7 8)`. Triple transitivity conjugates
an involution so that it fixes 2 and interchanges 0 and 3. There are fifteen
possible pairings of the other six points.

`PairCases` proves that every such involution is one of the two displayed
ones or generates a subgroup with order divisible by five. `SeedOrders`
proves that both displayed pairs generate subgroups of order 504. The former
alternative contradicts Lagrange at order 1512. The latter gives a subgroup
of index three, whose coset action contradicts simplicity. The final theorem
supplies both checked finite calculations to the action argument below.

Source context: condition K for the alternating case of Aschbacher–Smith,
`refs/quasithin.pdf`, printed pp.4 and 482. No primitive catalogue or
identification with a projective group is used in this reduction.
-/

open MulAction Equiv
namespace CFSG.Quasithin.MainConverse.NineReduction

private theorem normalize_seven (s : Exclude1512.Perm) (hs : orderOf s = 7) :
    ∃ q : Exclude1512.Perm, MulAut.conj q s = Exclude1512.cycle := by
  have hsc : s.IsCycle := Perm.isCycle_of_prime_order' (hs ▸ by decide) (by simp; omega)
  have hc : Exclude1512.cycle.IsCycle := Perm.isCycle_of_prime_order'
    (Exclude1512.cycle_order ▸ by decide) (by simp [Exclude1512.cycle_order])
  apply isConj_iff.mp
  apply hsc.isConj hc
  rw [← hsc.orderOf, ← hc.orderOf, hs, Exclude1512.cycle_order]

private theorem triple_fixing_card_of_1512 (U : Subgroup (Perm (Fin 9)))
    (hthree : IsMultiplyPretransitive U (Fin 9) 3) (hcard : Nat.card U = 1512)
    (a b c : Fin 9) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Nat.card (fixingSubgroup U ({a,b,c} : Set (Fin 9))) = 3 := by
  have hs : ({a,b,c} : Set (Fin 9)).ncard = 3 := by simp [hab,hac,hbc]
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq
    (G := U) ({a,b,c} : Set (Fin 9)) (hs ▸ hthree)
  norm_num [hs, Nat.choose, Nat.factorial] at hi
  have hc := (fixingSubgroup U ({a,b,c} : Set (Fin 9))).index_mul_card
  rw [hi, hcard] at hc
  omega

private theorem involution_not_fix_three (U : Subgroup (Perm (Fin 9)))
    (hthree : IsMultiplyPretransitive U (Fin 9) 3) (hcard : Nat.card U = 1512)
    (t : U) (ht : orderOf t = 2)
    (a b c : Fin 9) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : t • a = a) (hb : t • b = b) (hc : t • c = c) : False := by
  have htD : t ∈ fixingSubgroup U ({a,b,c} : Set (Fin 9)) := by
    simpa only [mem_fixingSubgroup_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq] using And.intro ha (And.intro hb hc)
  have hd := (fixingSubgroup U ({a,b,c} : Set (Fin 9))).orderOf_dvd_natCard htD
  rw [ht, triple_fixing_card_of_1512 U hthree hcard a b c hab hac hbc] at hd
  norm_num at hd


private theorem involution_unique_fixed (U : Subgroup (Perm (Fin 9)))
    (hthree : IsMultiplyPretransitive U (Fin 9) 3) (hcard : Nat.card U = 1512)
    (t : U) (ht : orderOf t = 2) :
    ∃ a : Fin 9, ∀ x : Fin 9, t • x = x ↔ x = a := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let S : Finset (Fin 9) := (t : Perm (Fin 9)).supportᶜ
  have hmem (x : Fin 9) : x ∈ S ↔ t • x = x := by
    change x ∈ S ↔ (t : Perm (Fin 9)) x = x
    simp [S, Perm.mem_support]
  have hle : S.card ≤ 2 := by
    by_contra! hlt
    obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp hlt
    exact involution_not_fix_three U hthree hcard t ht a b c hab hac hbc
      ((hmem a).mp ha) ((hmem b).mp hb) ((hmem c).mp hc)
  have ht2 : (t : Perm (Fin 9)) ^ 2 = 1 := by
    exact congrArg (fun u : U => (u : Perm (Fin 9)))
      (ht ▸ pow_orderOf_eq_one t)
  have hmod := Perm.card_compl_support_modEq (p := 2) (n := 1) (by simpa using ht2)
  change S.card % 2 = 9 % 2 at hmod
  have hcardS : S.card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcardS
  exact ⟨a, fun x => by rw [← hmem, ha, Finset.mem_singleton]⟩

private theorem normalized_involution (U : Subgroup (Perm (Fin 9)))
    (hthree : IsMultiplyPretransitive U (Fin 9) 3) (hcard : Nat.card U = 1512) :
    ∃ t : U, (t : Perm (Fin 9)) ^ 2 = 1 ∧
      (∀ x : Fin 9, (t : Perm (Fin 9)) x = x ↔ x = 2) ∧
      (t : Perm (Fin 9)) 0 = 3 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let := hthree
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hcard]; decide)
  obtain ⟨a, ha⟩ := involution_unique_fixed U hthree hcard t ht
  obtain ⟨x, hxa⟩ := exists_ne a
  have htx : t • x ≠ x := fun h => hxa ((ha x).mp h)
  have hta : t • a = a := (ha a).mpr rfl
  have htxa : t • x ≠ a := by
    rw [← hta]
    exact (MulAction.injective t).ne hxa
  let v : Fin 3 ↪ Fin 9 := ⟨![a,x,t • x], by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact (hxa hij).elim | exact (hxa hij.symm).elim |
        exact (htx hij).elim | exact (htx hij.symm).elim |
        exact (htxa hij).elim | exact (htxa hij.symm).elim⟩
  let w : Fin 3 ↪ Fin 9 := ⟨![2,0,3], by decide⟩
  obtain ⟨g, hg⟩ := exists_smul_eq U v w
  have hga : g • a = (2 : Fin 9) := congrArg (fun e : Fin 3 ↪ Fin 9 => e 0) hg
  have hgx : g • x = (0 : Fin 9) := congrArg (fun e : Fin 3 ↪ Fin 9 => e 1) hg
  have hgtx : g • (t • x) = (3 : Fin 9) := congrArg (fun e : Fin 3 ↪ Fin 9 => e 2) hg
  refine ⟨g * t * g⁻¹, ?_, ?_, ?_⟩
  · have hv : (g * t * g⁻¹) ^ 2 = 1 := by
      change (MulAut.conj g t) ^ 2 = 1
      rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
    exact congrArg (fun u : U => (u : Perm (Fin 9))) hv
  · intro y
    change (g * t * g⁻¹) • y = y ↔ y = 2
    constructor
    · intro hy
      have hh := congrArg (fun z : Fin 9 => g⁻¹ • z) hy
      simp only [mul_smul, inv_smul_smul] at hh
      have hh' := congrArg (fun z : Fin 9 => g • z) ((ha _).mp hh)
      simpa only [smul_inv_smul, hga] using hh'
    · rintro rfl
      rw [← hga, mul_smul, mul_smul, inv_smul_smul, hta]
  · change (g * t * g⁻¹) • (0 : Fin 9) = 3
    rw [← hgx, mul_smul, mul_smul, inv_smul_smul, hgtx]


private theorem subgroup_504_impossible (U : Subgroup (Perm (Fin 9)))
    [IsSimpleGroup U] (hU : Nat.card U = 1512)
    (K : Subgroup (Perm (Fin 9))) (hKU : K ≤ U) (hK : Nat.card K = 504) : False := by
  let L := K.subgroupOf U
  have hL : Nat.card L = 504 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKU).toEquiv).trans hK
  have hi : L.index = 3 := by
    have hm := L.card_mul_index
    rw [hL, hU] at hm
    omega
  have ht : L = ⊤ := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt L
    (by rw [hi, hU]; decide)
  rw [ht, Subgroup.card_top, hU] at hL
  omega

private theorem simple_nine_ne_1512_of_pair_orders
    (hpairs : ∀ t : Exclude1512.Perm, t ^ 2 = 1 →
      (∀ x : Fin 9, t x = x ↔ x = 2) → t 0 = 3 →
      t = Exclude1512.involution false ∨ t = Exclude1512.involution true ∨
      5 ∣ Nat.card (Subgroup.closure {Exclude1512.cycle, t}))
    (hseeds : ∀ b : Bool, Nat.card (Exclude1512.seed b) = 504)
    (U : Subgroup (Perm (Fin 9))) [IsSimpleGroup U]
    (hthree : IsMultiplyPretransitive U (Fin 9) 3) : Nat.card U ≠ 1512 := by
  intro hU
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := U) 7 (by rw [hU]; decide)
  obtain ⟨q, hq⟩ := normalize_seven s ((Subgroup.orderOf_coe s).trans hs)
  let V := U.map (MulAut.conj q).toMonoidHom
  let eUV : U ≃* V := (MulAut.conj q).subgroupMap U
  let : IsSimpleGroup V := eUV.symm.isSimpleGroup
  have hV : Nat.card V = 1512 := (Nat.card_congr eUV.toEquiv).symm.trans hU
  let X : Fin 9 →ₑ[eUV.toMonoidHom] Fin 9 :=
    { toFun := q, map_smul' := fun g x => by
        change q ((g : Perm (Fin 9)) x) = (q * (g : Perm (Fin 9)) * q⁻¹) (q x)
        simp }
  have hthreeV : IsMultiplyPretransitive V (Fin 9) 3 :=
    (IsPretransitive.of_embedding_congr (n := Fin 3) (f := X)
      eUV.surjective q.bijective).mp hthree
  have hc : Exclude1512.cycle ∈ V := ⟨s, s.property, hq⟩
  obtain ⟨t, ht2, htfix, ht03⟩ := normalized_involution V hthreeV hV
  have hle : Subgroup.closure {Exclude1512.cycle, (t : Perm (Fin 9))} ≤ V := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases (Set.mem_insert_iff.mp hx) with rfl | hx
    · exact hc
    · exact (Set.mem_singleton_iff.mp hx) ▸ t.property
  have hseed (b : Bool) (hb : (t : Perm (Fin 9)) = Exclude1512.involution b) : False := by
    apply subgroup_504_impossible V hV (Exclude1512.seed b) _ (hseeds b)
    simpa only [Exclude1512.seed, hb] using hle
  rcases hpairs t ht2 htfix ht03 with ha | hb | hfive
  · exact hseed false ha
  · exact hseed true hb
  · have hd := hfive.trans (Subgroup.card_dvd_of_le hle)
    rw [hV] at hd
    norm_num at hd

/-- The action and simplicity argument, with the two explicit finite permutation
calculations left as hypotheses. -/
public theorem primitive_simple_normal_nine_order_ne_1512_of_pair_orders
    (hpairs : ∀ t : Exclude1512.Perm, t ^ 2 = 1 →
      (∀ x : Fin 9, t x = x ↔ x = 2) → t 0 = 3 →
      t = Exclude1512.involution false ∨ t = Exclude1512.involution true ∨
      5 ∣ Nat.card (Subgroup.closure {Exclude1512.cycle, t}))
    (hseeds : ∀ b : Bool, Nat.card (Exclude1512.seed b) = 504)
    (H : Subgroup (alternatingGroup (Fin 9))) (_hH : H ≠ ⊤)
    (_hp : IsPreprimitive H (Fin 9))
    (N : Subgroup H) [N.Normal] [IsSimpleGroup N]
    (_hna : ¬ IsMulCommutative N)
    (hthree : IsMultiplyPretransitive N (Fin 9) 3) : Nat.card N ≠ 1512 := by
  let f := toPermHom N (Fin 9)
  let e : N ≃* f.range := MonoidHom.ofInjective toPerm_injective
  let : IsSimpleGroup f.range := e.symm.isSimpleGroup
  let X : Fin 9 →ₑ[e.toMonoidHom] Fin 9 :=
    { toFun := id, map_smul' := fun _ _ => rfl }
  have hthreeU : IsMultiplyPretransitive f.range (Fin 9) 3 :=
    (IsPretransitive.of_embedding_congr (n := Fin 3) (f := X)
      e.surjective Function.bijective_id).mp hthree
  rw [Nat.card_congr e.toEquiv]
  exact simple_nine_ne_1512_of_pair_orders hpairs hseeds f.range hthreeU

/-- A simple normal subgroup in the given triple-transitive degree-nine action
cannot have order 1512. Both finite permutation calculations are discharged by
the checked pairing cases and seed orders. -/
public theorem primitive_simple_normal_nine_order_ne_1512
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : H ≠ ⊤)
    (hp : IsPreprimitive H (Fin 9))
    (N : Subgroup H) [N.Normal] [IsSimpleGroup N]
    (hna : ¬ IsMulCommutative N)
    (hthree : IsMultiplyPretransitive N (Fin 9) 3) : Nat.card N ≠ 1512 :=
  primitive_simple_normal_nine_order_ne_1512_of_pair_orders
    Exclude1512.normalized_involution_cases Exclude1512.seed_card H hH hp N hna hthree

end CFSG.Quasithin.MainConverse.NineReduction
