module

public import GorensteinWalter.SL2ProjectiveCover
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.QuasithinBasic

/-!
# Cyclic three-subgroups of SL₂ over an odd prime field

For p ≥ 7, an odd Sylow subgroup away from the field characteristic lies
in a cyclic PSL₂ torus. The central kernel of SL₂ → PSL₂ has order two,
so the Sylow three-subgroup embeds in its projective image. At p = 3 and
p = 5 the order formula gives 24 and 120, each divisible by three only once.

Consequently every surjective image of a group whose first commutator
subgroup embeds in SL₂(p) has derived three-rank at most one. In particular,
this does not require SL₂(3) to be perfect.

Source: the rank-one centralizer calculation underlying Aschbacher–Smith
A.3.21(a), printed p.55, and the inspection in E.6.18, printed p.252.
-/

public section

open Subgroup GorensteinWalter BenderSuzuki.MatrixGroups
namespace Matrix.SU3.InnerThreeRank

/-- Sylow three-subgroups of SL₂(p) are cyclic, including p = 3. -/
theorem sl2_sylow_three_isCyclic (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (P : Sylow 3 (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) : IsCyclic P := by
  by_cases hsmall : p < 7
  · have hnot : ¬ 3 ^ 2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
      rw [sl2_card_formula, Nat.card_zmod]
      have hpprime := (Fact.out : p.Prime)
      interval_cases p <;> norm_num at hpprime <;> norm_num
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hd := (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).card_subgroup_dvd_card
    rw [hn] at hd
    have hn1 : n ≤ 1 := by
      by_contra h
      exact hnot ((pow_dvd_pow 3 (by omega : 2 ≤ n)).trans hd)
    apply isCyclic_of_card_dvd_prime (p := 3)
    rw [hn]
    exact (pow_dvd_pow 3 hn1).trans (by simp)
  · have hp3 : p ≠ 3 := by omega
    let f := sl2ProjectiveProjection (ZMod p)
    let Q : Sylow 3 (PSL2 (ZMod p)) := P.mapSurjective (sl2ProjectiveProjection_surjective _)
    have hQ : IsCyclic Q := psl2_sylow_isCyclic_of_coprime_field_card
      (ZMod p) (p := p) (f := 1) (by simp) (by simpa using Nat.le_of_not_gt hsmall)
      3 (by decide) (by simpa using (Nat.coprime_primes Nat.prime_three (Fact.out : p.Prime)).mpr hp3.symm) Q
    let : IsCyclic Q := hQ
    let g : P →* Q := f.subgroupMap P
    apply isCyclic_of_injective g
    intro x y he
    apply injective_comp_subtype_of_coprime_ker f ?_ (P : Subgroup _) P.isPGroup'
    · exact congrArg Subtype.val he
    · rw [sl2ProjectiveProjection_ker_card (ZMod p) (by simpa using hp)]
      decide

/-- Every three-group embedded in SL₂(p) is cyclic. -/
theorem isCyclic_of_three_group_sl2_embedding (p : ℕ) [Fact p.Prime] (hp : Odd p)
    {G : Type*} [Group G] (hG : IsPGroup 3 G)
    (f : G →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) (hf : Function.Injective f) :
    IsCyclic G := by
  have hr : IsPGroup 3 f.range := hG.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := hr.exists_le_sylow
  let : IsCyclic P := sl2_sylow_three_isCyclic p hp P
  let : IsCyclic f.range := Subgroup.isCyclic_of_le hP
  exact (MonoidHom.ofInjective hf).isCyclic.mpr inferInstance

/-- An SL₂ embedding of the first commutator controls derived rank in every image. -/
theorem derived_rank_of_surjective_and_sl2_embedding (p : ℕ) [Fact p.Prime] (hp : Odd p)
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (j : commutator G →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hj : Function.Injective j) : primeRank 3 (commutator H) ≤ 1 := by
  let P : Sylow 3 (commutator G) := Sylow.nonempty.some
  have hP : IsCyclic P := isCyclic_of_three_group_sl2_embedding p hp P.isPGroup'
    (j.comp (P : Subgroup (commutator G)).subtype) (by intro x y h; exact Subtype.ext (hj h))
  have hm : (commutator G).map f = commutator H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    rfl
  let e := MulEquiv.subgroupCongr hm
  exact P.primeRank_le_one_of_surjective hP
    (e.toMonoidHom.comp (f.subgroupMap (commutator G)))
    (e.surjective.comp (f.subgroupMap_surjective _))

end Matrix.SU3.InnerThreeRank
