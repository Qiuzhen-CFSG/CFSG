module
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.SemidihedralControl
public import Theory.GroupTheory.SolvableSemidihedralInvolution

/-!
# Solvable intersections controlling a marked SL₂(5)

A solvable group of order dividing 2^a times five, with order divisible by
eight, has nontrivial two-core: otherwise its cyclic five-core is
self-centralizing, contradicting the two-part of its automorphism group.
For a semidihedral Sylow subgroup of order sixteen, the central involution
is therefore characteristic. Fixing that involution preserves a marked
SL₂(5) whenever the derived involution centralizer has order at most 120.

This is the local calculation used for SU₃(5) and PSU₃(5) in the
Aschbacher–Smith 5.1.13/5.2.2 argument (printed pp.637–638,648–649).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.SylowMarkedSL2

private theorem twoCore_ne_bot_of_two_five_order
    {Y : Type*} [Group Y] [Finite Y] (hs : Group.IsSolvable Y)
    {a : ℕ} (hd : Nat.card Y ∣ 2^a * 5) (h8 : 8 ∣ Nat.card Y) :
    pCore 2 Y ≠ ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro htwo
  have hf : fittingSubgroup Y = pCore 5 Y := by
    apply le_antisymm _ (pCore_le_fitting Y 5)
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    have hp := Nat.prime_of_mem_primeFactors p.val.property
    have hh := (Nat.dvd_of_mem_primeFactors p.val.property).trans hd
    rcases hp.dvd_mul.mp hh with h | h
    · have he : p.val.val = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h)
      rw [he,htwo]
      exact bot_le
    · have he : p.val.val = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
      rw [he]
  let N := pCore 5 Y
  have hc : Nat.card N ∣ 5 := by
    obtain ⟨b,hb⟩ := (pCore_isPGroup (p := 5) (G := Y)).exists_card_eq
    have hcop : Nat.Coprime (Nat.card N) (2^a) := by
      rw [hb]
      exact ((by decide : Nat.Coprime 5 2).pow_left b).pow_right a
    exact hcop.dvd_of_dvd_mul_left (N.card_subgroup_dvd_card.trans hd)
  let : IsCyclic N := isCyclic_of_card_dvd_prime hc
  have haut : ¬ 8 ∣ Nat.card (MulAut N) := by
    rw [IsCyclic.card_mulAut]
    rcases (Nat.dvd_prime Nat.prime_five).mp hc with hc | hc <;> rw [hc] <;> decide
  let f : Y →* MulAut N := MulAut.conjNormal
  have hk : f.ker ≤ N := by
    apply le_trans _ (show centralizer (N : Set Y) ≤ N from by
      change centralizer (pCore 5 Y : Set Y) ≤ pCore 5 Y
      rw [←hf]
      exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs)
    intro y hy
    apply mem_centralizer_iff.mpr
    intro x hx
    have hh := congrArg (fun b : MulAut N => (b ⟨x,hx⟩ : Y)) hy
    change y*x*y⁻¹=x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hcop : Nat.Coprime 8 (Nat.card f.ker) :=
    (by decide : Nat.Coprime 8 5).of_dvd_right ((card_dvd_of_le hk).trans hc)
  apply haut
  apply dvd_trans _ f.range.card_subgroup_dvd_card
  apply hcop.dvd_of_dvd_mul_left
  rwa [←index_ker,card_mul_index]

private theorem fix_fourth_of_two_five_order
    {Y : Type*} [Group Y] [Finite Y] (hs : Group.IsSolvable Y)
    {k : ℕ} (hd : Nat.card Y ∣ 2^k*5)
    (S : Sylow 2 Y) (a b : S) (ha : orderOf a = 8) (hb : orderOf b = 2)
    (hab : b*a*b⁻¹=a^3) (hg : closure ({a,b} : Set S)=⊤) (φ : MulAut Y) :
    φ ((a : Y)^4) = (a : Y)^4 := by
  classical
  let z : Y := (a : Y)^4
  have hz : orderOf z = 2 := by
    rw [show z = (a : Y)^4 from rfl,orderOf_pow,orderOf_coe,ha]
    decide
  have hz1 : z ≠ 1 := fun he => by simp [he] at hz
  have h8 : 8 ∣ Nat.card Y := by
    rw [←ha,←orderOf_coe]
    exact orderOf_dvd_natCard (a : Y)
  let : (zpowers z).Characteristic :=
    Semidihedral.characteristic_zpowers_fourth_of_twoCore_ne_bot S a b ha hb hab hg
      (twoCore_ne_bot_of_two_five_order hs hd h8)
  have hm : φ z ∈ zpowers z :=
    characteristic_iff_le_comap.mp inferInstance φ (mem_zpowers z)
  rw [mem_zpowers_iff_mem_range_orderOf,hz] at hm
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
  have hi2 : i < 2 := Finset.mem_range.mp hi
  interval_cases i
  · have he' : φ z = 1 := by simpa using he.symm
    exact (hz1 (φ.injective (he'.trans φ.map_one.symm))).elim
  · simpa only [pow_one] using he.symm

/-- A solvable subgroup of order dividing a power of two times five, containing
the full semidihedral Sylow subgroup, forces its stabilizer to preserve the
marked SL₂(5) recovered from the central involution. -/
theorem automorphism_preserves_sl2_five_of_solvable_intersection
    {Y F : Type*} [Group Y] [Finite Y] [Field F] [Finite F]
    (hgens : ∀ S : Sylow 2 Y, ∃ a b : S, orderOf a = 8 ∧ orderOf b = 2 ∧
      b*a*b⁻¹=a^3 ∧ closure ({a,b} : Set S)=⊤)
    (hbound : ∀ z : Y, orderOf z = 2 →
      Nat.card (commutator (centralizer ({z} : Set Y))) ≤ 120)
    (R J : Subgroup Y) (eR : R ≃* SL(2,F)) (hF : Nat.card F = 5)
    (S : Sylow 2 Y) (hSR : (S : Subgroup Y) ≤ normalizer (R : Set Y))
    (hSJ : (S : Subgroup Y) ≤ J) (hs : Group.IsSolvable J)
    {k : ℕ} (hd : Nat.card J ∣ 2^k*5)
    (φ : MulAut Y) (hJ : J.map φ.toMonoidHom = J) : R.map φ.toMonoidHom = R := by
  let Q := S.subtype hSJ
  let e : Q ≃* S := subgroupOfEquivOfLe hSJ
  obtain ⟨a,b,ha,hb,hab,hg⟩ := hgens S
  let a' := e.symm a
  let b' := e.symm b
  have ha' : orderOf a' = 8 := (e.symm.orderOf_eq a).trans ha
  have hb' : orderOf b' = 2 := (e.symm.orderOf_eq b).trans hb
  have hab' : b'*a'*b'⁻¹=a'^3 := by
    simpa only [a',b',map_mul,map_inv,map_pow] using congrArg e.symm hab
  have hg' : closure ({a',b'} : Set Q)=⊤ := by
    have hh := congrArg (map e.symm.toMonoidHom) hg
    rw [MonoidHom.map_closure,map_top_of_surjective _ e.symm.surjective] at hh
    simpa only [Set.image_insert_eq,Set.image_singleton, MulEquiv.coe_toMonoidHom] using hh
  let ψ : MulAut J := (J.equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr hJ)
  have hh := fix_fourth_of_two_five_order hs hd Q a' b' ha' hb' hab' hg' ψ
  have hfix : φ ((a : Y)^4)=(a : Y)^4 := congrArg J.subtype hh
  exact Theory.SpecificGroups.Classical.SylowMarkedSL2.automorphism_preserves_sl2_five_of_fix_fourth
    hbound R eR hF S hSR a b ha hb hab hg φ hfix


end Theory.SpecificGroups.Classical.SylowMarkedSL2
