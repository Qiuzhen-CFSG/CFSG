module

public import Theory.GroupTheory.CComponent.TwoComponent.Involution
public import Theory.SpecificGroups.Alternating.SmallFixedComponents

/-!
# B₂ for A₅, A₆ and A₇

For A₅, permutation-induced involutions have solvable centralizers of order
dividing 24. The existing A₆ calculation includes the exceptional outer
automorphisms. In A₇ the only nonsolvable fixed group is S₅. Perfectness
places a C-component of S₅ inside A₅, and minimality then identifies it with
that ordinary component. Thus this argument applies to genuine two-components,
without assuming they are ordinary components beforehand.

Sources: GLS II, Definition 2.4; GLS III, §5.2, especially Proposition 5.2.7;
Aschbacher--Smith, the small alternating cases used in E.6.22, printed p.254.
-/

public section

open Subgroup Theory.GroupTheory Equiv Equiv.Perm GLS3.Chapter5

namespace alternatingGroup

private theorem solvable_of_card_dvd_twentyFour {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G ∣ 24) : Group.IsSolvable G := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three G
  intro p hp hd
  have h : p ∣ 2 ^ 3 * 3 := hd.trans hcard
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)

/-- All automorphisms of order two of A₅ have solvable fixed subgroup. -/
theorem five_involution_fixed_solvable (a : MulAut (alternatingGroup (Fin 5)))
    (ha : orderOf a = 2) : Group.IsSolvable a.fixedSubgroup := by
  let act : Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5)) := MulAut.conjNormal
  obtain ⟨σ, hσ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    5 (by decide) (by decide)).surjective a
  have hs : orderOf σ = 2 := (orderOf_injective act
    (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 5 (by decide)) σ).symm.trans
      (hσ ▸ ha)
  have hc : Nat.card (centralizer ({σ} : Set (Perm (Fin 5)))) ∣ 24 := by
    obtain ⟨k, hk⟩ := cycleType_prime_order (σ := σ) (hs ▸ Nat.prime_two)
    rw [hs] at hk
    have hb := σ.sum_cycleType_le
    rw [hk, Multiset.sum_replicate] at hb
    simp only [smul_eq_mul, Fintype.card_fin] at hb
    have hk1 : k ≤ 1 := by omega
    interval_cases k <;> rw [nat_card_centralizer, hk] <;>
      norm_num [Multiset.replicate_succ, Nat.factorial]
  let : Group.IsSolvable (centralizer ({σ} : Set (Perm (Fin 5)))) :=
    solvable_of_card_dvd_twentyFour hc
  subst a
  have hf : (act σ).fixedSubgroup = automorphismFixedSubgroup (act σ) := by
    ext x
    rw [MulAut.mem_fixedSubgroup]
    rfl
  rw [hf]
  exact Group.isSolvable_of_isSolvable_injective
    (f := (alternatingCentralizerSignKernelEquivFixedConjNormal σ).symm.toMonoidHom)
    (alternatingCentralizerSignKernelEquivFixedConjNormal σ).symm.injective

private theorem symmetric_five_cComponent_quasisimple
    (L : Subgroup (Perm (Fin 5))) (hL : L.IsCComponent) : IsQuasisimple L := by
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hA : IsComponent (Perm (Fin 5)) (alternatingGroup (Fin 5)) :=
    ⟨(inferInstance : (alternatingGroup (Fin 5)).Normal).isSubnormal, inferInstance⟩
  let := hL.perfect
  have he := hL.eq_of_le hA.isCComponent
    (le_of_isPerfect_of_index_eq_two L _ alternatingGroup.index_eq_two)
  exact IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr he).symm

/-- The full involutory B₂ condition for A₅. -/
theorem five_hasInvolutoryB2 : HasInvolutoryB2 (alternatingGroup (Fin 5)) :=
  HasInvolutoryB2.of_fixed_solvable five_involution_fixed_solvable

/-- The full involutory B₂ condition for A₆, including exceptional automorphisms. -/
theorem six_hasInvolutoryB2 : HasInvolutoryB2 (alternatingGroup (Fin 6)) :=
  HasInvolutoryB2.of_fixed_solvable SmallFixedComponents.six_fixed_solvable

/-- The nonsolvable fixed-group case in A₇ is handled as a C-component of S₅. -/
theorem seven_hasInvolutoryB2 : HasInvolutoryB2 (alternatingGroup (Fin 7)) := by
  intro a ha L hL
  rcases SmallFixedComponents.seven_fixed_solvable_or_equiv a ha with hs | he
  · let := hs
    exact (hL.1.not_isSolvable inferInstance).elim
  · obtain ⟨e⟩ := he
    have hq := symmetric_five_cComponent_quasisimple _ (hL.1.map_equiv e)
    exact IsQuasisimple.of_mulEquiv (e.subgroupMap L).symm (hG := hq)

/-- The complete small alternating range in the known-simple catalogue. -/
theorem small_hasInvolutoryB2 (n : ℕ) (hn : 5 ≤ n) (hn7 : n ≤ 7) :
    HasInvolutoryB2 (alternatingGroup (Fin n)) := by
  interval_cases n
  · exact five_hasInvolutoryB2
  · exact six_hasInvolutoryB2
  · exact seven_hasInvolutoryB2

end alternatingGroup
