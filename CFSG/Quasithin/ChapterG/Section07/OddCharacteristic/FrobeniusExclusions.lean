module

public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.SpecificGroups.SL2.ProjectiveBorelFrobenius
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.OrderSieve
public import Theory.Representation.GeneralLinearNatural

/-!
# The odd PSL2 Frobenius exclusions in G.7.2(2)

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004, printed pp.347--348 (PDF pp.358--359), excludes the Frobenius
kernel/complement orders `(25,12)`, `(49,24)`, `(31,15)` and `(127,63)` from
binary degree eight. Here the Frobenius groups retain actual abelian kernels,
relative normality in their overgroups, complements and conjugation actions.
The projective Borel construction supplies all four configurations inside
the actual matrix models.

A nontrivial kernel weight has a free complement orbit; independence of
weights bounds its size by the representation degree. Applied to PSL2 over
an odd field of order q, this gives degree at least `(q - 1) / 2`, without
whole-group irreducibility. In particular the parameters 49, 31 and 127
force degrees at least 24, 15 and 63. Combined with the existing order sieve,
only q at most nine or q equal to seventeen survives in degree at most eight.
-/

public section

open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section07.OddCharacteristic

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The complement of an abelian odd-order Frobenius kernel bounds binary degree. -/
theorem abelian_frobenius_degree_bound (rho : Representation (ZMod 2) G V)
    (hrho : Function.Injective rho) (B : Subgroup G) (K C : Subgroup B)
    [IsMulCommutative K] (hFrob : IsFrobeniusGroupWithKernelComplement K C)
    (hodd : Odd (Nat.card K)) : Nat.card C ≤ Module.finrank (ZMod 2) V := by
  let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hFrob.kernel_ne_bot
  let : K.Normal := hFrob.normal
  apply Representation.card_le_finrank_of_fixedPointFree_normalizer_of_field
    (rho.comp B.subtype) K C (hrho.comp Subtype.val_injective)
    (ZMod.natCast_ne_zero_iff_odd.mpr hodd)
  · rw [Subgroup.normalizer_eq_top]
    exact le_top
  · intro c hc k hk
    have hcent := (lemma_3_1 K C hFrob.kernel_ne_bot hFrob.complement_ne_bot
      hFrob.normal hFrob.isComplement').mp hFrob c hc
    have hm : (k : B) ∈ elementCentralizerIn K (c : B) :=
      ⟨k.property, Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp hk).symm⟩
    rw [hcent] at hm
    exact Subtype.ext hm

/-- All four source Frobenius configurations force binary degree greater than eight. -/
theorem source_frobenius_degree_gt_eight (rho : Representation (ZMod 2) G V)
    (hrho : Function.Injective rho) (B : Subgroup G) (K C : Subgroup B)
    [IsMulCommutative K] (hFrob : IsFrobeniusGroupWithKernelComplement K C)
    (horders : (Nat.card K = 25 ∧ Nat.card C = 12) ∨
      (Nat.card K = 49 ∧ Nat.card C = 24) ∨
      (Nat.card K = 31 ∧ Nat.card C = 15) ∨
      (Nat.card K = 127 ∧ Nat.card C = 63)) :
    8 < Module.finrank (ZMod 2) V := by
  have hodd : Odd (Nat.card K) := by
    rcases horders with h | h | h | h <;> rw [h.1] <;> decide
  have hbound := abelian_frobenius_degree_bound rho hrho B K C hFrob hodd
  rcases horders with h | h | h | h <;> omega

open Matrix.ProjectiveSpecialLinearGroup

omit [Finite G] in
/-- The genuine projective Borel gives the uniform odd PSL2 degree bound. -/
theorem psl2_frobenius_degree_bound (rho : Representation (ZMod 2) G V)
    (hrho : Function.Injective rho) {q : ℕ} (hodd : Odd q)
    (hmodel : ClassicalGroup.IsPSL G 2 q) :
    (q - 1) / 2 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  have hbound := Representation.card_le_finrank_of_fixedPointFree_normalizer_of_field
    (rho.comp e.symm.toMonoidHom) (OddBorel.kernel F) (OddBorel.complement F)
    (hrho.comp e.symm.injective)
    (ZMod.natCast_ne_zero_iff_odd.mpr (by rw [OddBorel.card_kernel, hcard]; exact hodd))
    (OddBorel.complement_normalizes F) (OddBorel.fixedPointFree F)
  rw [OddBorel.card_complement, hcard] at hbound
  have hd : 2 ∣ q - 1 := by obtain ⟨n, hn⟩ := hodd; exact ⟨n, by omega⟩
  rwa [Nat.gcd_eq_right_iff_dvd.mpr hd] at hbound

omit [Finite G] in
/-- The Borel complement in PSL2(49) forces degree at least twenty-four. -/
theorem psl2_fortyNine_degree_ge_twentyFour (rho : Representation (ZMod 2) G V)
    (hrho : Function.Injective rho) (hmodel : ClassicalGroup.IsPSL G 2 49) :
    24 ≤ Module.finrank (ZMod 2) V := by
  simpa using psl2_frobenius_degree_bound rho hrho (by decide : Odd 49) hmodel

omit [Finite G] in
/-- The Borel complement in PSL2(31) forces degree at least fifteen. -/
theorem psl2_thirtyOne_degree_ge_fifteen (rho : Representation (ZMod 2) G V)
    (hrho : Function.Injective rho) (hmodel : ClassicalGroup.IsPSL G 2 31) :
    15 ≤ Module.finrank (ZMod 2) V := by
  simpa using psl2_frobenius_degree_bound rho hrho (by decide : Odd 31) hmodel

omit [Finite G] in
/-- The Borel complement in PSL2(127) forces degree at least sixty-three. -/
theorem psl2_oneTwentySeven_degree_ge_sixtyThree (rho : Representation (ZMod 2) G V)
    (hrho : Function.Injective rho) (hmodel : ClassicalGroup.IsPSL G 2 127) :
    63 ≤ Module.finrank (ZMod 2) V := by
  simpa using psl2_frobenius_degree_bound rho hrho (by decide : Odd 127) hmodel

omit [Finite G] in
/-- The parameter forty-nine is excluded from binary degree at most eight. -/
theorem psl2_fortyNine_degree_gt_eight (rho : Representation (ZMod 2) G V)
    (hrho : Function.Injective rho) (hmodel : ClassicalGroup.IsPSL G 2 49) :
    8 < Module.finrank (ZMod 2) V := by
  have := psl2_fortyNine_degree_ge_twentyFour rho hrho hmodel
  omega

omit [Finite G] in
/-- The parameter thirty-one is excluded from binary degree at most eight. -/
theorem psl2_thirtyOne_degree_gt_eight (rho : Representation (ZMod 2) G V)
    (hrho : Function.Injective rho) (hmodel : ClassicalGroup.IsPSL G 2 31) :
    8 < Module.finrank (ZMod 2) V := by
  have := psl2_thirtyOne_degree_ge_fifteen rho hrho hmodel
  omega

omit [Finite G] in
/-- The parameter one hundred twenty-seven is excluded from binary degree at most eight. -/
theorem psl2_oneTwentySeven_degree_gt_eight (rho : Representation (ZMod 2) G V)
    (hrho : Function.Injective rho) (hmodel : ClassicalGroup.IsPSL G 2 127) :
    8 < Module.finrank (ZMod 2) V := by
  have := psl2_oneTwentySeven_degree_ge_sixtyThree rho hrho hmodel
  omega

/-- The exact four Frobenius configurations excluded from the binary general
linear group of degree eight in the proof of G.7.2(2). -/
theorem not_source_frobenius_in_GL8
    (B : Subgroup (GL (Fin 8) (ZMod 2))) (K C : Subgroup B)
    [IsMulCommutative K] (hFrob : IsFrobeniusGroupWithKernelComplement K C)
    (horders : (Nat.card K = 25 ∧ Nat.card C = 12) ∨
      (Nat.card K = 49 ∧ Nat.card C = 24) ∨
      (Nat.card K = 31 ∧ Nat.card C = 15) ∨
      (Nat.card K = 127 ∧ Nat.card C = 63)) : False := by
  have h := source_frobenius_degree_gt_eight
    (Representation.generalLinearNatural (F := ZMod 2) 8)
    (Representation.generalLinearNatural_injective 8) B K C hFrob horders
  simp at h

/-- The four excluded Frobenius configurations are realized by the upper
triangular Borel in the actual projective matrix model. -/
theorem source_psl2_frobenius_borels {F : Type*} [Field F] [Finite F]
    (hcard : Nat.card F = 25 ∨ Nat.card F = 49 ∨ Nat.card F = 31 ∨ Nat.card F = 127) :
    let K := (OddBorel.kernel F).subgroupOf (OddBorel.borel F)
    let C := (OddBorel.complement F).subgroupOf (OddBorel.borel F)
    IsFrobeniusGroupWithKernelComplement K C ∧ IsMulCommutative K ∧
      ((Nat.card K = 25 ∧ Nat.card C = 12) ∨
       (Nat.card K = 49 ∧ Nat.card C = 24) ∨
       (Nat.card K = 31 ∧ Nat.card C = 15) ∨
       (Nat.card K = 127 ∧ Nat.card C = 63)) := by
  dsimp only
  refine ⟨OddBorel.frobenius F ?_, inferInstance, ?_⟩
  · rcases hcard with h | h | h | h <;> rw [h] <;> norm_num
  · rw [OddBorel.card_kernel_in_borel, OddBorel.card_complement_in_borel]
    rcases hcard with h | h | h | h <;> rw [h] <;> norm_num

/-- The order sieve with every Frobenius exception discharged. -/
theorem psl2_parameter_sieve_after_frobenius (rho : Representation (ZMod 2) G V)
    (hrho : Function.Injective rho) {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hmodel : ClassicalGroup.IsPSL G 2 (p ^ e))
    (hd : Module.finrank (ZMod 2) V ≤ 8) : p ^ e ≤ 9 ∨ p ^ e = 17 := by
  rcases psl2_parameter_sieve_refined rho hrho hp ho he hmodel hd with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have := psl2_fortyNine_degree_gt_eight rho hrho (h ▸ hmodel)
    omega
  · have := psl2_thirtyOne_degree_gt_eight rho hrho (h ▸ hmodel)
    omega
  · have := psl2_oneTwentySeven_degree_gt_eight rho hrho (h ▸ hmodel)
    omega

end CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
