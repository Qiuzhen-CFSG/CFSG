module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SolvableReduction
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.CyclicObstruction
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.Fitting.PrimeResidual
public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# Solvable symmetric-three pairs on a small binary module

A faithful action on an elementary binary group of order at most sixteen
has order dividing |GL₄(2)|. Every prime core for a prime greater than
three is consequently cyclic. The actual symmetric-three residual
centralizes these cores, so F.6.9, applied to the genuine SQTK cover,
makes the actor a {2,3}-group. Its common Sylow has order two. Transfer
makes its two-residual odd, hence a three-group of order at most nine;
therefore the two embedded local residuals commute.

EqualCoreSource applies this to the actual omega span when the original
parabolic two-cores coincide. All quotient maps and local markings are
retained. Source: Aschbacher--Smith 13.4.7, printed p.901, first paragraph
of the solvable-action case; F.6.9, printed p.306.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
universe u v
variable {H G E : Type u} [Group H] [Finite H] [Group G] [Finite G]
  [Group E] [Finite E] [IsElementaryAbelian 2 E]

omit [Finite G] in
/-- The full automorphism order, including all possible smaller dimensions. -/
private theorem small_binary_action_card_dvd (f : G →* MulAut E) (hf : Function.Injective f)
    (hE : Nat.card E ≤ 16) : Nat.card G ∣ 20160 := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hn4 : n ≤ 4 := by
    by_contra h
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 5 ≤ n by omega)
    rw [←hn] at hh
    norm_num at hh
    omega
  have hd : Nat.card G ∣ Nat.card (MulAut E) := card_dvd_of_injective f hf
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn] at hd
  apply dvd_trans hd
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

private theorem large_prime_core_cyclic (hdiv : Nat.card G ∣ 20160)
    (q : ℕ) [Fact q.Prime] (h2 : q ≠ 2) (h3 : q ≠ 3) : IsCyclic (pCore q G) := by
  by_cases hd : q ∣ Nat.card G
  · have hh : q ∣ 2^6 * 3^2 * 5 * 7 := hd.trans hdiv
    have hp := Fact.out (p := q.Prime)
    simp only [hp.dvd_mul] at hh
    have hq : q = 5 ∨ q = 7 := by
      rcases hh with ((hh | hh) | hh) | hh
      · exact (h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow hh))).elim
      · exact (h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow hh))).elim
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hh)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hh)
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := q) (G := G)).exists_card_eq
    have hn1 : n ≤ 1 := by
      by_contra h
      have hd2 : q^2 ∣ 20160 :=
        (pow_dvd_pow q (show 2 ≤ n by omega)).trans
          (hn ▸ ((pCore q G).card_subgroup_dvd_card.trans hdiv))
      rcases hq with rfl | rfl <;> norm_num at hd2
    apply isCyclic_of_card_dvd_prime (p := q)
    rw [hn]
    interval_cases n <;> simp
  · have hc : Nat.card (pCore q G) = 1 :=
      (pCore_isPGroup (p := q) (G := G)).card_eq_or_dvd.resolve_right
        (fun hh => hd (hh.trans (card_subgroup_dvd_card _)))
    exact isCyclic_of_card_dvd_prime (p := q) (hc ▸ one_dvd _)

/-- The equal-core action branch: a solvable faithful binary action of degree
at most four has commuting local residuals. The genuine SQTK cover is retained. -/
theorem small_solvable_action_residuals_commute
    {K : GroupClass.{u}} (hH : IsSQTK K H) (q : H →* G) (hq : Function.Surjective q)
    {A B : Subgroup G} (hg : ChapterF.IsGoldschmidtTriple A B)
    (eA : A ≃* Equiv.Perm (Fin 3))
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (f : G →* MulAut E) (hf : Function.Injective f) (hE : Nat.card E ≤ 16) :
    ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ = ⊥ := by
  have hd := small_binary_action_card_dvd f hf hE
  have hc : (pResidual 2 A).map A.subtype ≤
      centralizer ((pResidual 3 (fittingSubgroup G)).map (fittingSubgroup G).subtype : Set G) := by
    apply le_centralizer_iff.mpr
    rw [fitting_pResidual_eq_sup_prime_cores]
    refine iSup_le fun p => iSup_le fun hp3 => ?_
    by_cases hp2 : p.1.1 = 2
    · rw [hp2,hcore]
      exact bot_le
    · let : IsCyclic (pCore p.1.1 G) := large_prime_core_cyclic hd _ hp2 hp3
      exact le_centralizer_iff.mp (ChapterF.symmetricThree_residual_centralizes_cyclic_normal
        (pCore p.1.1 G) A eA)
  have h23 := ChapterF.SourceAssembly.source_lemma_F_6_9 hH q hq hsolv hg (Or.inl hc)
  obtain ⟨T,hT⟩ := hg.intersection_sylow
  have hcardA : Nat.card A = 6 := by
    rw [Nat.card_congr eA.toEquiv]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hcardT : Nat.card T = 2 := by
    have hTA : (T : Subgroup G) ≤ A := hT.symm.le.trans inf_le_left
    have hi := SymmetricThreeTwoCore.sylow_index_three hg.quotient_left.some (T.subtype hTA)
    have hh := ((T : Subgroup G).subgroupOf A).index_mul_card
    rw [show ((T : Subgroup G).subgroupOf A).index = 3 from hi,
      Nat.card_congr (subgroupOfEquivOfLe hTA).toEquiv,hcardA] at hh
    omega
  have ht : IsCyclic T := isCyclic_of_prime_card hcardT
  have hodd := T.odd_card_twoResidual_of_isCyclic ht
  let R := pResidual 2 G
  have hR3 : IsPGroup 3 R := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : 3 ≠ 0)).mpr
    intro p hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp23 := (IsPiGroup_iff _ _).mp h23 ⟨p,hpp⟩
      (hpd.trans R.card_subgroup_dvd_card)
    rcases hp23 with hp2 | hp3
    · change p = 2 at hp2
      have htwo : 2 ∣ Nat.card R := by simpa only [hp2] using hpd
      exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp
        (Nat.coprime_two_left.mpr hodd)) htwo)
    · change p = 3 at hp3
      subst p
      norm_num
  obtain ⟨n,hn⟩ := hR3.exists_card_eq
  have hn2 : n ≤ 2 := by
    by_contra hh
    have h27 : 27 ∣ 20160 := (pow_dvd_pow 3 (show 3 ≤ n by omega)).trans
      (hn ▸ R.card_subgroup_dvd_card.trans hd)
    norm_num at h27
  have hcomm : IsMulCommutative R := by
    interval_cases n
    · let : Subsingleton R := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
      infer_instance
    · let : IsCyclic R := isCyclic_of_prime_card (by simpa using hn : Nat.card R = 3)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hn
  let := hcomm
  exact le_bot_iff.mp ((commutator_mono (map_pResidual_le 2 A.subtype)
    (map_pResidual_le 2 B.subtype)).trans (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer R)).le)
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
