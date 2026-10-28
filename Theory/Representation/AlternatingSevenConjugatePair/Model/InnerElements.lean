module

public import Theory.Representation.AlternatingSevenConjugatePair.Model.Natural
public import Theory.Representation.AlternatingSevenConjugatePair.Model.FixedSpaces
public import Theory.Representation.SixLetterTransvections
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Inner element calculations on binary four-dimensional A₇ modules

Every involution fixes a letter. Restricting a faithful action to the actual
six-letter point stabilizer rules out displacement rank at most one. The
square-zero displacement operator bounds the rank by two, giving equality.

For the cubic calculation, write `a = (0 1 2)`, `b = (3 4 5)`, `t = ab`, and
`u = ab²`. When three-cycles act without nonzero fixed vectors, the operators
satisfy `ρ a + ρ a² = ρ b + ρ b² = 1`. Thus the two cubic norm operators for
`t` and `u` sum to the identity. Their fixed spaces have zero intersection
since `tu` is a three-cycle. An explicit even conjugator identifies their
dimensions, so each fixed space is a plane.

The cubic theorem retains precisely the three-cycle fixed-point hypothesis;
its discharge by the separate normal-form development belongs to the parent
assembly. The involution theorem has no such premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.8, printed p.389/PDF p.400. The separate three-cycle input is used by the
normal-form proof associated with I.1.6(8), printed p.408/PDF p.419.
-/

public section

open Representation.BinaryOffender
namespace Representation.AlternatingSevenConjugatePair.Model
noncomputable section

section Involutions

private def sixEmbedding (i : Fin 7) : alternatingGroup (Fin 6) →* alternatingGroup (Fin 7) where
  toFun a := ⟨Equiv.Perm.ofSubtype ((finSuccAboveEquiv i).permCongr a.val), by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype,
      Equiv.Perm.sign_permCongr]
    exact a.property⟩
  map_one' := Subtype.ext (by
    change (Equiv.Perm.ofSubtype.comp (finSuccAboveEquiv i).permCongrHom.toMonoidHom) 1 = _
    exact map_one _)
  map_mul' a b := Subtype.ext (by
    change (Equiv.Perm.ofSubtype.comp (finSuccAboveEquiv i).permCongrHom.toMonoidHom)
      (a.val * b.val) = _
    exact map_mul _ _ _)

private theorem sixEmbedding_injective (i : Fin 7) : Function.Injective (sixEmbedding i) := by
  intro a b h
  apply Subtype.ext
  exact (finSuccAboveEquiv i).permCongr.injective
    (Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h))

private theorem mem_sixEmbedding_range (t : alternatingGroup (Fin 7))
    (i : Fin 7) (hi : t.val i = i) : t ∈ (sixEmbedding i).range := by
  have hstable (j : Fin 7) : t.val j ≠ i ↔ j ≠ i := by
    simpa only [hi] using (t.val.injective.ne_iff (x := j) (y := i))
  let s : Equiv.Perm {j : Fin 7 // j ≠ i} := t.val.subtypePerm hstable
  have hs : Equiv.Perm.ofSubtype s = t.val :=
    Equiv.Perm.ofSubtype_subtypePerm (p := fun j => j ≠ i) hstable
      (fun j hj hji => hj (by simpa [hji] using hi))
  let a : alternatingGroup (Fin 6) := ⟨(finSuccAboveEquiv i).permCongr.symm s, by
    rw [Equiv.Perm.mem_alternatingGroup]
    change Equiv.Perm.sign ((finSuccAboveEquiv i).symm.permCongr s) = 1
    rw [Equiv.Perm.sign_permCongr, ← Equiv.Perm.sign_ofSubtype s, hs]
    exact t.property⟩
  refine ⟨a, Subtype.ext ?_⟩
  change Equiv.Perm.ofSubtype ((finSuccAboveEquiv i).permCongr
    ((finSuccAboveEquiv i).permCongr.symm s)) = t.val
  exact (congrArg Equiv.Perm.ofSubtype ((finSuccAboveEquiv i).permCongr.apply_symm_apply s)).trans hs

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every involution in a faithful binary four-dimensional A₇ module moves a plane. -/
theorem involution_fixedCodim (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) V = 4)
    (t : alternatingGroup (Fin 7)) (ht : orderOf t = 2) :
    fixedCodim ρ (Subgroup.zpowers t) = 2 := by
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have hupper : fixedCodim ρ (Subgroup.zpowers t) ≤ 2 := by
    have hr : LinearMap.range (ρ t - LinearMap.id) ≤ fixedSpace ρ (Subgroup.zpowers t) := by
      rintro _ ⟨v, rfl⟩
      rw [mem_fixedSpace_zpowers_iff]
      change ρ t (ρ t v - v) = ρ t v - v
      have hs : ρ t (ρ t v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ht2, map_one]
        rfl
      rw [map_sub, hs]
      have hn (w : V) : -w = w := neg_eq_iff_add_eq_zero.mpr (ZModModule.add_self w)
      simp only [sub_eq_add_neg, hn, add_comm]
    have hrank := Submodule.finrank_mono hr
    have hc := fixedCodim_add_finrank ρ (Subgroup.zpowers t)
    rw [← fixedCodim_zpowers_eq_displacement_rank] at hrank
    rw [hdim] at hc
    omega
  have hlower : ¬ fixedCodim ρ (Subgroup.zpowers t) ≤ 1 := by
    intro hsmall
    have htval : t.val ^ 2 = 1 := congrArg Subtype.val ht2
    obtain ⟨i, hi⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1)
      (by decide : ¬ 2 ∣ Fintype.card (Fin 7)) (by simpa using htval)
    obtain ⟨a, ha⟩ := mem_sixEmbedding_range t i hi
    have ha1 := SixLetterTransvections.alternating_eq_one_of_displacement_le_one
      (ρ.comp (sixEmbedding i)) (hρ.comp (sixEmbedding_injective i)) a (by
        change Module.finrank (ZMod 2) (LinearMap.range (ρ (sixEmbedding i a) - LinearMap.id)) ≤ 1
        rw [← fixedCodim_zpowers_eq_displacement_rank, ha]
        exact hsmall)
    have ht1 : t = 1 := by rw [← ha, ha1, map_one]
    simp [ht1] at ht
  omega

end Involutions

section Cubics

private def firstThree : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def secondThree : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def mixedThree : alternatingGroup (Fin 7) := firstThree * secondThree ^ 2
private def cubicConjugator : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 4 5 * Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

private theorem firstThree_isThreeCycle : firstThree.val.IsThreeCycle := by
  rw [Equiv.Perm.IsThreeCycle]
  decide
private theorem secondThree_isThreeCycle : secondThree.val.IsThreeCycle := by
  rw [Equiv.Perm.IsThreeCycle]
  decide
private theorem firstThree_cube : firstThree ^ 3 = 1 := by decide
private theorem secondThree_cube : secondThree ^ 3 = 1 := by decide
private theorem mixedThree_cube : mixedThree ^ 3 = 1 := by decide
private theorem cubic_conjugate :
    cubicConjugator * doubleThreeCycle * cubicConjugator⁻¹ = mixedThree := by decide
private theorem doubleThree_cube : doubleThreeCycle ^ 3 = 1 := by
  simpa only [doubleThreeCycle_order] using pow_orderOf_eq_one doubleThreeCycle
private theorem product_isThreeCycle : (doubleThreeCycle * mixedThree).val.IsThreeCycle := by
  rw [Equiv.Perm.IsThreeCycle]
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
private theorem norm_mem (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (a : alternatingGroup (Fin 7)) (ha : a ^ 3 = 1) (v : V) :
    v + ρ a v + ρ (a ^ 2) v ∈ fixedSpace ρ (Subgroup.zpowers a) := by
  rw [mem_fixedSpace_zpowers_iff]
  have ha3 : a * a ^ 2 = 1 := by simpa only [← pow_succ'] using ha
  have haa : ρ a (ρ a v) = ρ (a ^ 2) v := by
    rw [map_pow, pow_two, Module.End.mul_apply]
  have haa2 : ρ a (ρ (a ^ 2) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ha3, map_one]
    rfl
  simp only [map_add, haa, haa2]
  abel

private theorem quadratic_sum (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (a : alternatingGroup (Fin 7)) (ha : a ^ 3 = 1)
    (hfree : ∀ v : V, ρ a v = v → v = 0) : ρ a + ρ (a ^ 2) = 1 := by
  ext v
  have hz := hfree _ ((mem_fixedSpace_zpowers_iff ρ a _).mp (norm_mem ρ a ha v))
  change ρ a v + ρ (a ^ 2) v = v
  apply add_left_cancel (a := v)
  calc
    v + (ρ a v + ρ (a ^ 2) v) = 0 := by simpa only [add_assoc] using hz
    _ = v + v := (ZModModule.add_self v).symm

variable [FiniteDimensional (ZMod 2) V]
/-- The double-three-cycle fixes a plane when three-cycles are fixed-point-free.
This calculation does not need a separate faithfulness assumption. -/
theorem doubleThreeCycle_fixed_finrank
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (hthree : ∀ a : alternatingGroup (Fin 7), a.val.IsThreeCycle →
      ∀ v : V, ρ a v = v → v = 0) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers doubleThreeCycle)) = 2 := by
  have hfirst := quadratic_sum ρ firstThree firstThree_cube (hthree _ firstThree_isThreeCycle)
  have hsecond := quadratic_sum ρ secondThree secondThree_cube (hthree _ secondThree_isThreeCycle)
  have hsum : ρ doubleThreeCycle + ρ (doubleThreeCycle ^ 2) +
      ρ mixedThree + ρ (mixedThree ^ 2) = 1 := by
    calc
      _ = (ρ firstThree + ρ (firstThree ^ 2)) *
          (ρ secondThree + ρ (secondThree ^ 2)) := by
        simp only [add_mul, mul_add, ← map_mul]
        rw [show firstThree * secondThree = doubleThreeCycle by decide,
          show firstThree * secondThree ^ 2 = mixedThree from rfl,
          show firstThree ^ 2 * secondThree = mixedThree ^ 2 by decide,
          show firstThree ^ 2 * secondThree ^ 2 = doubleThreeCycle ^ 2 by decide]
        abel
      _ = 1 := by rw [hfirst, hsecond, mul_one]
  let P := fixedSpace ρ (Subgroup.zpowers doubleThreeCycle)
  let Q := fixedSpace ρ (Subgroup.zpowers mixedThree)
  have hdisjoint : Disjoint P Q := by
    rw [Submodule.disjoint_def]
    intro v hp hq
    have hp' := (mem_fixedSpace_zpowers_iff ρ doubleThreeCycle v).mp hp
    have hq' := (mem_fixedSpace_zpowers_iff ρ mixedThree v).mp hq
    apply hthree _ product_isThreeCycle v
    rw [map_mul, Module.End.mul_apply, hq', hp']
  have hsup : P ⊔ Q = ⊤ := by
    apply eq_top_iff.mpr
    intro v _
    refine Submodule.mem_sup.mpr ⟨v + ρ doubleThreeCycle v + ρ (doubleThreeCycle ^ 2) v,
      norm_mem ρ doubleThreeCycle doubleThree_cube v,
      v + ρ mixedThree v + ρ (mixedThree ^ 2) v,
      norm_mem ρ mixedThree mixedThree_cube v, ?_⟩
    have hv := LinearMap.congr_fun hsum v
    change ρ doubleThreeCycle v + ρ (doubleThreeCycle ^ 2) v +
      ρ mixedThree v + ρ (mixedThree ^ 2) v = v at hv
    calc
      _ = (v + v) + (ρ doubleThreeCycle v + ρ (doubleThreeCycle ^ 2) v +
          ρ mixedThree v + ρ (mixedThree ^ 2) v) := by abel
      _ = v := by rw [ZModModule.add_self, zero_add, hv]
  have hdimPQ := P.finrank_sup_add_finrank_inf_eq Q
  rw [hsup, hdisjoint.eq_bot, finrank_top, finrank_bot, add_zero, hdim] at hdimPQ
  have heq := fixedCodim_zpowers_conj ρ doubleThreeCycle cubicConjugator
  rw [cubic_conjugate] at heq
  have hp := fixedCodim_add_finrank ρ (Subgroup.zpowers doubleThreeCycle)
  have hq := fixedCodim_add_finrank ρ (Subgroup.zpowers mixedThree)
  change 4 = Module.finrank (ZMod 2) P + Module.finrank (ZMod 2) Q at hdimPQ
  change fixedCodim ρ (Subgroup.zpowers doubleThreeCycle) + Module.finrank (ZMod 2) P = _ at hp
  change fixedCodim ρ (Subgroup.zpowers mixedThree) + Module.finrank (ZMod 2) Q = _ at hq
  change Module.finrank (ZMod 2) P = 2
  omega

end Cubics
end
end Representation.AlternatingSevenConjugatePair.Model
