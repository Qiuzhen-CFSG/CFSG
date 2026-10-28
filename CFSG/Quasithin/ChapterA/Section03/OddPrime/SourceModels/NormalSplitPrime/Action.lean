module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.TwoCore
public import Theory.GroupAction.ComponentRankAction.ResidualSource
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# The faithful star action in the p-prime-center branch

Full p-rank makes the ordinary component centralizer p-prime. Its action
on the simple central quotient contains every inner automorphism and has
p-prime core trivial in its image. Thus its kernel is exactly O_{p′}(H),
and the literal star component is the original central quotient. The outside
split actor has outer order p. Prime generation also identifies O^{p′}(H*)
with H*; this supplies the residual needed by both odd ternary source rows.

Source: Aschbacher–Smith A.3.18, printed pp.51–53. The applications in
OddLinear and OddUnitary preserve the actual component and quotient maps.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
variable {H S : Type*} [Group H] [Finite H] [Group S] [Finite S]
variable {K : Subgroup H} [K.Normal] [IsQuasisimple K]
variable {p : ℕ} [Fact p.Prime]

omit [K.Normal] [IsQuasisimple K] [Fact p.Prime] in
theorem actionImage_eq_of_index_three {S : Type*} [Group S] [Finite S]
    (I A D : Subgroup S) (hi : I ≤ A) (ha : A ≤ D)
    (hne : A ≠ I) (hc : Nat.card D = 3 * Nat.card I) : A = D := by
  have hid : I.relIndex D = 3 := by
    have hh := (I.subgroupOf D).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (hi.trans ha)).toEquiv] at hh
    change Nat.card I * I.relIndex D = Nat.card D at hh
    rw [hc] at hh
    have hpos : 0 < Nat.card I := Nat.card_pos
    nlinarith
  have hm := I.relIndex_mul_relIndex A D hi ha
  rw [hid] at hm
  have hd : I.relIndex A ∣ 3 := ⟨A.relIndex D, hm.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact (hne (le_antisymm (relIndex_eq_one.mp h) hi)).elim
  · have h' : A.relIndex D = 1 := by rw [h] at hm; omega
    exact le_antisymm ha (relIndex_eq_one.mp h')

omit [K.Normal] [IsQuasisimple K] in
theorem component_quotient_prime_dvd
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (e : K ⧸ center K ≃* S) : p ∣ Nat.card S := by
  have he := primeRank_eq_of_surjective_of_coprime p
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
    (by rwa [QuotientGroup.ker_mk'])
  rw [primeRank_congr p e] at he
  by_contra hd
  have := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
  omega

theorem component_action_kernel
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (hH : primeRank p H ≤ 2) (e : K ⧸ center K ≃* S) :
    (normalAction K e).ker = pPrimeCore p H := by
  let : IsSimpleGroup S := e.isSimpleGroup_congr.mp IsQuasisimple.simple
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hs : center S = ⊥ := by
    rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h)).elim
  let f := normalAction K e
  have hk : Nat.Coprime p (Nat.card f.ker) := by
    rw [normalAction_ker]
    exact centralizer_coprime K hz (by omega) hH
  have hi : MulAut.innerSubgroup S ≤ f.range := by
    rw [← normalAction_component_image K e]
    exact Subgroup.map_le_range (f := normalAction K e) (H := K)
  have hc := actor_pPrimeCore_eq_bot f.range hi hs
    (component_quotient_prime_dvd hz hr e)
  have hh := pPrimeCore_comap_eq_of_surjective_coprime p f.rangeRestrict
    f.rangeRestrict_surjective (by simpa only [MonoidHom.ker_rangeRestrict] using hk)
  rw [hc] at hh
  change f.rangeRestrict.ker = pPrimeCore p H at hh
  simpa only [MonoidHom.ker_rangeRestrict] using hh

omit [Finite S] in
theorem outside_action_outer_order
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (hH : primeRank p H ≤ 2) (e : K ⧸ center K ≃* S)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) :
    orderOf (QuotientGroup.mk' (MulAut.innerSubgroup S) (normalAction K e a)) = p := by
  let f := normalAction K e
  let q := QuotientGroup.mk' (MulAut.innerSubgroup S)
  apply orderOf_eq_prime
  · rw [← map_pow, ← map_pow, ← ha, pow_orderOf_eq_one, map_one, map_one]
  · intro h
    apply haK
    apply prime_element_mem_of_image_mem f (by
      rw [normalAction_ker]
      exact centralizer_coprime K hz (by omega) hH) K a ha
    rw [normalAction_component_image]
    exact (QuotientGroup.eq_one_iff _).mp h

omit [Finite S] in
theorem prime_dvd_of_action_power_inner
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (hH : primeRank p H ≤ 2) (e : K ⧸ center K ≃* S)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) {m : ℕ}
    (hm : normalAction K e a ^ m ∈ MulAut.innerSubgroup S) : p ∣ m := by
  rw [← outside_action_outer_order hz hr hH e a ha haK]
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr hm

def componentActionStarEquiv
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (hH : primeRank p H ≤ 2) (e : K ⧸ center K ≃* S) :
    Star p H ≃* (normalAction K e).range :=
  (QuotientGroup.quotientMulEquivOfEq (component_action_kernel hz hr hH e).symm).trans
    (QuotientGroup.quotientKerEquivRange (normalAction K e))

theorem componentActionStarEquiv_mk
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (hH : primeRank p H ≤ 2) (e : K ⧸ center K ≃* S) (x : H) :
    (componentActionStarEquiv hz hr hH e (starMap p H x)).val = normalAction K e x := rfl

theorem component_star_kernel
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (hH : primeRank p H ≤ 2) : (pPrimeCore p H).comap K.subtype = center K := by
  rw [← component_action_kernel hz hr hH (MulEquiv.refl _), normalAction_ker]
  ext x
  exact ⟨fun h => mem_center_iff.mpr (fun y => Subtype.ext (h y y.property)),
    fun h y hy => congrArg Subtype.val (mem_center_iff.mp h ⟨y, hy⟩)⟩

def componentStarQuotientEquiv
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (hH : primeRank p H ≤ 2) : (K ⧸ center K) ≃* starComponent p K := by
  let f := (starMap p H).subgroupMap K
  have hk : f.ker = center K := by
    rw [ker_subgroupMap, starMap, QuotientGroup.ker_mk']
    exact component_star_kernel hz hr hH
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f ((starMap p H).subgroupMap_surjective K))

theorem componentStarQuotientEquiv_mk
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (hH : primeRank p H ≤ 2) (x : K) :
    (componentStarQuotientEquiv hz hr hH (QuotientGroup.mk' (center K) x)).val =
      starMap p H x := rfl

omit [K.Normal] in
theorem prime_closure_eq_top_of_split
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (hgen : K ⊔ zpowers a = ⊤) :
    closure {x : H | orderOf x = p} = ⊤ := by
  have hd : p ∣ Nat.card K := by
    by_contra hd
    have := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    omega
  apply top_unique
  rw [← hgen]
  exact sup_le (component_le_prime_closure K hz hd)
    (zpowers_le.mpr (subset_closure ha))

omit [K.Normal] in
theorem star_residual_eq_top_of_split
    (hz : Nat.Coprime p (Nat.card (center K))) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (hgen : K ⊔ zpowers a = ⊤) :
    primeToResidual p (Star p H) = ⊤ := by
  have he : primeToResidual p H = ⊤ := by
    apply top_unique
    rw [← prime_closure_eq_top_of_split hz hr a ha hgen]
    apply (closure_le _).mpr
    intro x hx
    change orderOf x = p at hx
    apply mem_primeToResidual_of_pow (n := 1)
    simpa only [pow_one, ← hx] using pow_orderOf_eq_one x
  rw [← map_primeToResidual_of_surjective p (starMap p H)
    (QuotientGroup.mk'_surjective _), he]
  exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
