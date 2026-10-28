module

public import Theory.GroupTheory.SolvableFivePointSylow
public import Theory.PPrimeCore
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic

/-!
# Solvable faithful actions on five points

A faithful solvable action on five points with trivial two-core and order
 divisible by four has the Frobenius order twenty.  The proof reduces to the
 already checked subgroup calculation in `SolvableFivePointSylow`, then
 transports the odd core and Sylow conclusions back across the action image.
-/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem solvable_five_point_fifteen_certificate : ∀ g : Equiv.Perm (Fin 5),
    g ^ 15 = 1 → g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  decide +kernel

private theorem fitting_card_of_solvable_five_point_subgroup
    (K : Subgroup (Equiv.Perm (Fin 5))) (hcore : pCore 2 K = ⊥) :
    Nat.card (fittingSubgroup K) = 1 ∨ Nat.card (fittingSubgroup K) = 3 ∨
      Nat.card (fittingSubgroup K) = 5 := by
  let F := fittingSubgroup K
  have hle : F ≤ pPrimeCore 2 K := by
    dsimp [F]
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    by_cases hq : q.val.val = 2
    · rw [hq, hcore]
      exact bot_le
    · apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := q.val.val) (G := K)).exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes Nat.prime_two
        (Nat.prime_of_mem_primeFactors q.val.property)).mpr (Ne.symm hq)).pow_right _
  have hodd : Nat.Coprime 2 (Nat.card F) :=
    pPrimeCore_coprime_card.of_dvd_right (Subgroup.card_dvd_of_le hle)
  have hd : Nat.card F ∣ 120 := by
    have hh := F.card_subgroup_dvd_card.trans K.card_subgroup_dvd_card
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hh ⊢
    exact hh
  have hd15 : Nat.card F ∣ 15 := by
    have hcop : (Nat.card F).Coprime 8 := by
      simpa using hodd.symm.pow_right 3
    exact hcop.dvd_of_dvd_mul_left hd
  have hsq15 : Squarefree (15 : ℕ) := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hd
    have hh := Nat.le_of_dvd (by decide : 0 < 15) hd
    have : p ≤ 3 := by nlinarith
    interval_cases p <;> norm_num at *
  have hsq : Squarefree (Nat.card F) := hsq15.squarefree_of_dvd hd15
  let _ : IsZGroup F := IsZGroup.of_squarefree hsq
  let _ : IsCyclic F := inferInstance
  have hcases : Nat.card F = 1 ∨ Nat.card F = 3 ∨ Nat.card F = 5 ∨ Nat.card F = 15 := by
    have arith : ∀ n : ℕ, n ∣ 15 → n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by
      intro n hn
      have hh := Nat.le_of_dvd (by decide : 0 < 15) hn
      interval_cases n <;> norm_num at *
    exact arith _ hd15
  rcases hcases with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := F)
    have hg15 : orderOf g = 15 := hg.trans h
    have hperm : orderOf ((g : K) : Equiv.Perm (Fin 5)) = 15 := by
      simpa only [Subgroup.orderOf_coe] using hg15
    have hpow : (((g : K) : Equiv.Perm (Fin 5))) ^ 15 = 1 := by
      rw [← hperm]
      exact pow_orderOf_eq_one _
    rcases solvable_five_point_fifteen_certificate g hpow with h3 | h5
    · have hh := orderOf_dvd_of_pow_eq_one h3
      rw [hperm] at hh
      norm_num at hh
    · have hh := orderOf_dvd_of_pow_eq_one h5
      rw [hperm] at hh
      norm_num at hh

private theorem sylow_card_le_prime_sub_one_of_fitting_prime
    {G : Type*} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) {p : ℕ} [Fact p.Prime]
    (hp : Nat.Coprime 2 p) (hF : Nat.card (fittingSubgroup G) = p)
    (R : Sylow 2 G) : IsCyclic R ∧ Nat.card R ≤ p - 1 := by
  let F := fittingSubgroup G
  let _ : IsCyclic F := isCyclic_of_prime_card hF
  let eAut : MulAut F ≃* (ZMod p)ˣ := by
    have h := IsCyclic.mulAutMulEquiv F
    rw [hF] at h
    exact h
  let _ : IsCyclic (MulAut F) :=
    isCyclic_of_injective eAut.toMonoidHom eAut.injective
  let action : R →* MulAut F := MulAut.conjNormal.comp (R : Subgroup G).subtype
  have hdisj : Disjoint (R : Subgroup G) F := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := R.isPGroup'.exists_card_eq
    rw [hn, hF]
    exact hp.pow_left n
  have hinj : Function.Injective action := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply hdisj.le_bot
    refine ⟨x.property,
      centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv ?_⟩
    intro f hf
    have he := congrArg (fun a : MulAut F => (a ⟨f, hf⟩ : G))
      (show MulAut.conjNormal (x : G) = (1 : MulAut F) from hx)
    change (x : G) * f * (x : G)⁻¹ = f at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  refine ⟨isCyclic_of_injective action hinj, ?_⟩
  have hcard : Nat.card (MulAut F) = p - 1 := by
    rw [IsCyclic.card_mulAut, hF, Nat.totient_prime Fact.out]
  exact hcard ▸ Nat.card_le_card_of_injective action hinj

/-- A faithful solvable five-point permutation action with trivial two-core is
of order twenty; its odd core has order five and its Sylow two-subgroups are
cyclic of order four. -/
public theorem solvable_faithful_five_point_action
    {A : Type*} [Group A] [Finite A]
    (hsolv : Group.IsSolvable A) (htwo : pCore 2 A = ⊥)
    {X : Type*} [Finite X] (hX : Nat.card X = 5)
    (f : A →* Equiv.Perm X) (hf : Function.Injective f)
    (hfour : 4 ∣ Nat.card A) :
    Nat.card A = 20 ∧ Nat.card (pPrimeCore 2 A) = 5 ∧
      ∀ P : Sylow 2 A, Nat.card P = 4 ∧ IsCyclic P := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  let eX : X ≃ Fin 5 := Fintype.equivFinOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using hX)
  let permConj : Equiv.Perm X →* Equiv.Perm (Fin 5) :=
    { toFun := eX.permCongr
      map_one' := by ext x; simp [Equiv.permCongr_apply]
      map_mul' := by intro a b; apply Equiv.ext; intro x; simp [Equiv.permCongr_apply] }
  let g : A →* Equiv.Perm (Fin 5) := permConj.comp f
  have hg : Function.Injective g := by
    intro x y hxy
    apply hf
    apply eX.permCongr.injective
    exact hxy
  let K : Subgroup (Equiv.Perm (Fin 5)) := g.range
  let eA : A ≃* K := MulEquiv.ofBijective g.rangeRestrict (by
    constructor
    · intro x y hxy
      exact hg (congrArg Subtype.val hxy)
    · exact g.rangeRestrict_surjective)
  have hcoreK : pCore 2 K = ⊥ := by
    have hm := pCore_map_iso 2 eA
    rw [htwo, Subgroup.map_bot] at hm
    exact hm.symm
  let hsolvK : Group.IsSolvable K := Group.isSolvable_of_surjective eA.surjective
  have hcardK : Nat.card K = Nat.card A := Nat.card_congr eA.toEquiv.symm
  have hfourK : 4 ∣ Nat.card K := by
    rw [hcardK]
    exact hfour
  obtain ⟨R⟩ := Sylow.nonempty (p := 2) (G := K)
  have hRcyc_le := Sylow.isCyclic_and_card_le_four_of_solvable_five_point K hsolvK hcoreK R
  have hRcard : Nat.card R = 4 := by
    have hd : 4 ∣ Nat.card R := R.pow_dvd_card_of_pow_dvd_card (n := 2) hfourK
    exact Nat.le_antisymm hRcyc_le.2 (Nat.le_of_dvd (Nat.card_pos) hd)
  have hFcases := fitting_card_of_solvable_five_point_subgroup K hcoreK
  have hFcard : Nat.card (fittingSubgroup K) = 5 := by
    rcases hFcases with h1 | h3 | h5
    · have hKone : Nat.card K = 1 :=
        (fitting_eq_bot_iff_card_eq_one_of_solvable K).mp
          ((Subgroup.eq_bot_iff_card _).mpr h1)
      have : ¬ 4 ∣ Nat.card K := by
        rw [hKone]
        decide
      exact False.elim (this hfourK)
    · have hbad := (sylow_card_le_prime_sub_one_of_fitting_prime hsolvK
        (by decide : Nat.Coprime 2 3) h3 R).2
      omega
    · exact h5
  let F := fittingSubgroup K
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsCyclic F := isCyclic_of_prime_card hFcard
  let _ : CommGroup F := IsCyclic.commGroup
  let action : K →* MulAut F := MulAut.conjNormal
  have hker : action.ker = F := by
    apply le_antisymm
    · intro x hx
      have hcent : (x : K) ∈ Subgroup.centralizer (F : Set K) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have he := congrArg (fun a : MulAut F => (a ⟨y, hy⟩ : K)) hx
        change (x : K) * y * (x : K)⁻¹ = y at he
        exact (mul_inv_eq_iff_eq_mul.mp he).symm
      exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolvK hcent
    · intro x hx
      rw [MonoidHom.mem_ker]
      ext y
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      have hc := congrArg (fun y : F => (y : K))
        (mul_comm (⟨x, hx⟩ : F) y)
      change (x : K) * (y : K) = (y : K) * (x : K) at hc
      rw [hc]
      simp [mul_assoc]
  have hAut : Nat.card (MulAut F) = 4 := by
    rw [IsCyclic.card_mulAut, hFcard]
    decide
  have hdivImage : Nat.card (action.range) ∣ 4 := by
    rw [← hAut]
    exact action.range.card_subgroup_dvd_card
  have hbound : Nat.card (action.range) ≤ 4 := Nat.le_of_dvd (by decide : 0 < 4) hdivImage
  have hcardA' : Nat.card K = 5 * Nat.card (action.range) := by
    have hh := action.ker.card_mul_index
    rw [Subgroup.index_ker action, hker, hFcard] at hh
    exact hh.symm
  have hfourImage : 4 ∣ Nat.card (action.range) := by
    rw [hcardA'] at hfourK
    exact (by decide : Nat.Coprime 4 5).dvd_of_dvd_mul_left hfourK
  have hImageCard : Nat.card (action.range) = 4 :=
    Nat.dvd_antisymm hdivImage hfourImage
  have hcardA : Nat.card A = 20 := by
    rw [← hcardK, hcardA', hImageCard]
  have hcoreKcard : Nat.card (pPrimeCore 2 K) = 5 := by
    have hle : fittingSubgroup K ≤ pPrimeCore 2 K := by
      rw [fitting_eq_sup_pCore]
      refine iSup_le fun q => ?_
      by_cases hq : q.val.val = 2
      · rw [hq, hcoreK]
        exact bot_le
      · apply le_sSup
        refine ⟨inferInstance, ?_⟩
        obtain ⟨n, hn⟩ := (pCore_isPGroup (p := q.val.val) (G := K)).exists_card_eq
        rw [hn]
        exact ((Nat.coprime_primes Nat.prime_two
          (Nat.prime_of_mem_primeFactors q.val.property)).mpr (Ne.symm hq)).pow_right _
    have hd : Nat.card (fittingSubgroup K) ∣ Nat.card (pPrimeCore 2 K) :=
      Subgroup.card_dvd_of_le hle
    have hd5 : 5 ∣ Nat.card (pPrimeCore 2 K) := by
      rw [hFcard] at hd
      exact hd
    have hodd := pPrimeCore_coprime_card (p := 2) (G := K)
    have hdiv : Nat.card (pPrimeCore 2 K) ∣ 5 := by
      apply hodd.symm.pow_right 2 |>.dvd_of_dvd_mul_right
      have hK20 : Nat.card K = 20 := hcardK.trans hcardA
      have hdivK := (pPrimeCore 2 K).card_subgroup_dvd_card
      rw [hK20] at hdivK
      exact hdivK
    exact Nat.dvd_antisymm hdiv hd5
  have hcoreAcard : Nat.card (pPrimeCore 2 A) = 5 := by
    have hm := pPrimeCore_map_iso 2 eA
    have hc : Nat.card (pPrimeCore 2 K) = Nat.card (pPrimeCore 2 A) := by
      rw [← hm]
      exact Subgroup.card_map_of_injective eA.injective
    exact hc.symm.trans hcoreKcard
  refine ⟨hcardA, hcoreAcard, ?_⟩
  intro P
  have hPcard : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity, hcardA]
    rw [show 20 = 2 ^ 2 * 5 from rfl, Nat.factorization_mul (by decide) (by decide),
      Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_five.factorization]
    norm_num
  have hmapcard : Nat.card ((P : Subgroup A).map eA.toMonoidHom) = 4 := by
    calc
      Nat.card ((P : Subgroup A).map eA.toMonoidHom) = Nat.card P :=
        Subgroup.card_map_of_injective eA.injective
      _ = 4 := hPcard
  let Q : Sylow 2 K := Sylow.ofCard ((P : Subgroup A).map eA.toMonoidHom) (by
    have hK20 : Nat.card K = 20 := hcardK.trans hcardA
    rw [hmapcard, hK20]
    rw [show 20 = 2 ^ 2 * 5 from rfl, Nat.factorization_mul (by decide) (by decide),
      Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_five.factorization]
    norm_num)
  let _ : IsCyclic (Q : Subgroup K) :=
    (Sylow.isCyclic_and_card_le_four_of_solvable_five_point K hsolvK hcoreK Q).1
  let ψ : P →* Q := {
    toFun := fun x => ⟨eA x, Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩⟩
    map_one' := by simp
    map_mul' := by intro x y; apply Subtype.ext; simp }
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    exact eA.injective (congrArg (fun z : Q => (z : K)) hxy)
  exact ⟨hPcard, isCyclic_of_injective ψ hψinj⟩
