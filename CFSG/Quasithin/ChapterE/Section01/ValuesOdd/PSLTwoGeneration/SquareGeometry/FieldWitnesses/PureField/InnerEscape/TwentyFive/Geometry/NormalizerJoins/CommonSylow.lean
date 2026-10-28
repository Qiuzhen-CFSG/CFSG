module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.NormalizerJoins.Maximality
public import Theory.SpecificGroups.PSL2.FiveProjectivePermutation
public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic

/-!
# The common Sylow in the characteristic-five field model

The two centralizers of the marked involution and its twist intersect in the
actual common Sylow two-subgroup. The proof embeds this intersection into the
centralizer of the corresponding involution in `PGL₂(5) × C₂`; the permutation
model bounds the projective-factor centralizer by 12, while the field factor has order 2. The
intersection contains the Sylow subgroup, whose order is 16, so divisibility
forces equality.

Source: Aschbacher--Smith E.1.5, E.1.8 and E.1.14(6), printed pp.210--214,
using Aschbacher (1982), Lemma 4.10.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
open scoped MatrixGroups

private theorem perm_centralizer_card_le_12 (a : Equiv.Perm (Fin 5))
    (ha : orderOf a = 2) : Nat.card (centralizer ({a} : Set (Equiv.Perm (Fin 5)))) ≤ 12 := by
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order
    (show (orderOf a).Prime by rw [ha]; exact Nat.prime_two)
  have hs := a.sum_cycleType_le
  rw [hn, ha, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at hs
  norm_num at hs
  have hn' : n ≤ 1 := by omega
  interval_cases n <;>
    rw [Equiv.Perm.nat_card_centralizer, hn, ha] <;>
    norm_num [Multiset.sum_replicate, Multiset.prod_replicate]

private theorem pgl_centralizer_card_le_12 {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 5) (a : PGL2 K) (ha : orderOf a = 2) :
    Nat.card (centralizer ({a} : Set (PGL2 K))) ≤ 12 := by
  obtain ⟨e⟩ := Theory.PSL2.exists_pgl2_five_equiv K hK
  let f : centralizer ({a} : Set (PGL2 K)) ≃*
      centralizer ({e a} : Set (Equiv.Perm (Fin 5))) :=
    { toFun := fun x => ⟨e x, by
        rw [mem_centralizer_singleton_iff]
        simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property)⟩
      invFun := fun x => ⟨e.symm x, by
        rw [mem_centralizer_singleton_iff]
        apply e.injective
        simpa only [map_mul, e.apply_symm_apply] using
          (mem_centralizer_singleton_iff.mp x.property)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (e.map_mul x y) }
  rw [Nat.card_congr f.toEquiv]
  apply perm_centralizer_card_le_12
  exact (e.orderOf_eq a).trans ha


namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Geometry.Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)
variable [Finite (innerModel F σ)]

include hF hσ
omit [Finite (innerModel F σ)] in
set_option linter.style.haveILetI false in
private theorem prod_bound (C : Subgroup (innerModel F σ)) (zC : C)
    (e : C ≃* PGL2 (FixedPoints.subfield (zpowers σ) F) × zpowers σ)
    (a : PGL2 (FixedPoints.subfield (zpowers σ) F))
    (hez : (e zC).1 = a) (ha : orderOf a = 2) :
    Nat.card (centralizer ({zC} : Set C)) ≤ 24 := by
  let K := FixedPoints.subfield (zpowers σ) F
  have hK : Nat.card K = 5 := PureField.fixedSubfield_card hF σ
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
  letI : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let P : Subgroup (PGL2 K) := centralizer ({a} : Set (PGL2 K))
  let Z : Subgroup (zpowers σ) := ⊤
  letI : Finite (F ≃+* F) := Finite.of_injective (fun e : F ≃+* F => e.toFun)
    (fun e f h => by ext x; exact congrFun h x)
  letI : Finite (zpowers σ) := Finite.of_injective Subtype.val Subtype.coe_injective
  letI : Finite P := Finite.of_injective P.subtype P.subtype_injective
  letI : Finite Z := Finite.of_injective Z.subtype Z.subtype_injective
  let f : centralizer ({zC} : Set C) → P × Z := fun x =>
    ⟨⟨(e x).1, by
      rw [mem_centralizer_singleton_iff]
      have hx := congrArg e (mem_centralizer_singleton_iff.mp x.property)
      have hx' := congrArg Prod.fst hx
      simpa [hez] using hx'⟩, ⟨(e x).2, trivial⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · exact congrArg (fun q : P × Z => (q.1 : PGL2 K)) hxy
    · exact congrArg (fun q : P × Z => (q.2 : zpowers σ)) hxy
  have hcard : Nat.card (P × Z) ≤ 24 := by
    rw [Nat.card_prod]
    have hp := pgl_centralizer_card_le_12 hK a ha
    have hp' : Nat.card P ≤ 12 := by simpa [P] using hp
    have hz : Nat.card Z = 2 := by
      change Nat.card (⊤ : Subgroup (zpowers σ)) = 2
      rw [Subgroup.card_top, Nat.card_zpowers, hσ]
    rw [hz]
    omega
  exact (Nat.card_le_card_of_injective f hf).trans hcard

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Geometry.Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)
variable [Finite (innerModel F σ)]

omit [Finite F] [Finite (innerModel F σ)] hF hσ in
private theorem twist_comm_of_mem_both (x : innerModel F σ)
    (hxC : x ∈ c.centralizerAt false) (hxD : x ∈ c.centralizerAt true) :
    x * c.z = c.z * x := by
  have hc : x * pure σ = pure σ * x := mem_centralizer_singleton_iff.mp hxC
  have hd : x * (c.z * pure σ) = (c.z * pure σ) * x :=
    mem_centralizer_singleton_iff.mp hxD
  apply mul_right_cancel (b := pure σ)
  calc
    x * c.z * pure σ = x * (c.z * pure σ) := by rw [mul_assoc]
    _ = (c.z * pure σ) * x := hd
    _ = c.z * (x * pure σ) := by rw [mul_assoc, ← hc]
    _ = c.z * x * pure σ := by rw [mul_assoc]

private theorem centralizer_intersection_card_le (hF : Nat.card F = 5 ^ 2)
    (hσ : orderOf σ = 2) :
    Nat.card (c.centralizerAt false ⊓ c.centralizerAt true : Subgroup (innerModel F σ)) ≤ 24 := by
  let C : Subgroup (innerModel F σ) := c.centralizerAt false
  let I : Subgroup (innerModel F σ) := c.centralizerAt false ⊓ c.centralizerAt true
  let zC : C := ⟨c.z, c.twist_mem_pureCentralizer hσ⟩
  let e := pureCentralizerEquiv (by decide : Nat.Prime 5) (by decide) hF σ hσ
  let a : PGL2 (FixedPoints.subfield (zpowers σ) F) := (e zC).1
  have hze : (e zC).2 = 1 := by
    apply Subtype.ext
    have hh := congrArg SemidirectProduct.right
      (pureCentralizerEquiv_symm_coe (by decide : Nat.Prime 5) (by decide) hF σ hσ (e zC))
    have hsymm : (pureCentralizerEquiv (by decide : Nat.Prime 5) (by decide) hF σ hσ).symm
        (e zC) = zC := e.symm_apply_apply zC
    rw [hsymm] at hh
    change (c.z : PGammaL2 F).right = ((e zC).2 : F ≃+* F) at hh
    rw [c.z_linear] at hh
    exact hh.symm
  have hza : orderOf a = 2 := by
    have hz : orderOf zC = 2 := by
      rw [← Subgroup.orderOf_coe zC]
      exact c.z_order
    have he : orderOf (e zC) = 2 := (e.orderOf_eq zC).trans hz
    have hfirst := congrArg Prod.fst (show (e zC) ^ 2 = 1 from
      (by rw [← pow_orderOf_eq_one (e zC), he]))
    have haneq : a ≠ 1 := by
      intro ha1
      have heq : e zC = 1 := by
        apply Prod.ext
        · exact ha1
        · exact hze
      apply (show zC ≠ 1 by
        intro hz1
        have : orderOf zC = 1 := by rw [hz1]; exact orderOf_one
        omega)
      apply e.injective
      exact heq.trans (e.map_one).symm
    apply (orderOf_eq_prime_iff (x := a)).mpr
    constructor
    · simpa [a, pow_two] using hfirst
    · exact haneq
  have hzcomm (x : I) : x.1 * c.z = c.z * x.1 :=
    c.twist_comm_of_mem_both x.1 x.2.1 x.2.2
  let ψ : I → centralizer ({zC} : Set C) := fun x =>
    ⟨⟨x.1, x.2.1⟩, by
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact hzcomm x⟩
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have hxyC : (ψ x).val = (ψ y).val := congrArg Subtype.val hxy
    have hxyI : ((ψ x).val : innerModel F σ) = (ψ y).val :=
      congrArg Subtype.val hxyC
    exact Subtype.ext hxyI
  have hfirst : (e zC).1 = a := rfl
  have hKz : Nat.card (centralizer ({zC} : Set C)) ≤ 24 := by
    apply prod_bound hF hσ C zC e a hfirst
    exact hza
  exact (Nat.card_le_card_of_injective ψ hψ).trans hKz

include hF hσ
private theorem inner_sylow_card : Nat.card (c.T : Subgroup (innerModel F σ)) = 16 := by
  rw [Sylow.card_eq_multiplicity, CentralizerPair.innerModel_card
    (by decide : Nat.Prime 5) (by decide) hF σ hσ]
  have hcard : (5 ^ 2 : ℕ) * (5 ^ 4 - 1) = 15600 := by norm_num
  rw [hcard]
  have hf : (15600 : ℕ).factorization 2 = 4 := by
    have hlo : 4 ≤ (15600 : ℕ).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization (by decide)).mp (by norm_num)
    have hhi : ¬ 5 ≤ (15600 : ℕ).factorization 2 := by
      rw [← Nat.prime_two.pow_dvd_iff_le_factorization (by decide)]
      norm_num
    omega
  rw [hf]
  norm_num

include hF hσ
/-- The two actual field-involution centralizers meet exactly in their common
Sylow two-subgroup. -/
theorem centralizer_intersection_eq_sylow :
    c.centralizerAt false ⊓ c.centralizerAt true = (c.T : Subgroup _) := by
  let I : Subgroup (innerModel F σ) := c.centralizerAt false ⊓ c.centralizerAt true
  have hTI : (c.T : Subgroup (innerModel F σ)) ≤ I := by
    exact le_inf (c.sylow_le false) (c.sylow_le true)
  have hcardI : Nat.card I ≤ 24 := by
    simpa only [I] using centralizer_intersection_card_le c hF hσ
  have hdiv : Nat.card (c.T : Subgroup (innerModel F σ)) ∣ Nat.card I :=
    Subgroup.card_dvd_of_le hTI
  have hTcard : Nat.card (c.T : Subgroup (innerModel F σ)) = 16 := c.inner_sylow_card hF hσ
  have hIcard : Nat.card I = 16 := by
    obtain ⟨k, hk⟩ := hdiv
    rw [hTcard] at hk
    have hk_le : 16 * k ≤ 24 := by
      calc
        16 * k = Nat.card I := hk.symm
        _ ≤ 24 := hcardI
    have hk_lt : k < 2 := by nlinarith
    have hk_pos : 0 < k := by
      by_contra hk0
      have hkz : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst k
      have hIpos : 0 < Nat.card I := Nat.card_pos
      omega
    have hk1 : k = 1 := by omega
    rw [hk1] at hk
    simpa using hk
  have hEq : (c.T : Subgroup (innerModel F σ)) = I :=
    eq_of_le_of_card_ge hTI (le_of_eq (hIcard.trans hTcard.symm))
  exact hEq.symm

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
