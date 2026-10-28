module
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Even normal subgroups meet when the Sylow center is cyclic

In a finite group whose chosen Sylow two-subgroup has cyclic center, any two
normal subgroups of even order have nontrivial intersection. The hypotheses
refer to the actual Sylow subgroup and its center; the ambient group need not
have cyclic Sylow subgroups.

Cauchy's theorem gives an involution in each even normal subgroup. Sylow
conjugacy and normality put a conjugate in the chosen Sylow subgroup, so the
normal intersection there is nontrivial. A nontrivial normal subgroup of a
finite two-group meets its center: conjugation acts on that subgroup, the
identity is fixed, and the fixed-point congruence gives a second fixed point.
Thus each original subgroup meets the Sylow center nontrivially. The unique
involution of this cyclic two-group belongs to both intersections.

This general finite-group argument supplies the minimal-normal-subgroup
intersection step of ABG Chapter II Section 2 Proposition 2, article p.15,
`refs/latex/alperin-brauer-gorenstein-pages/page-016.tex`. Its proof uses only
Sylow conjugacy, Cauchy's theorem, the p-group fixed-point congruence, and the
involution theorem for cyclic two-groups.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem normal_center_meet {P : Type*} [Group P] [Finite P]
    (hp : IsPGroup 2 P) (N : Subgroup P) [N.Normal] (hN : N ≠ ⊥) :
    ∃ c : P, c ∈ N ∧ c ∈ center P ∧ c ≠ 1 := by
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  have hn := hp.to_subgroup N
  have hd : 2 ∣ Nat.card N := by
    obtain ⟨n, hn, he⟩ := hn.nontrivial_iff_card.mp inferInstance
    rw [he]
    exact dvd_pow_self 2 (by omega)
  have hc := hp.of_equiv ConjAct.toConjAct
  have hfix : (1 : N) ∈ MulAction.fixedPoints (ConjAct P) N := by
    intro g
    exact smul_one g
  obtain ⟨c, hcfix, hcne⟩ :=
    hc.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hd hfix
  refine ⟨c, c.property, ?_, ?_⟩
  · apply Subgroup.mem_center_iff.mpr
    intro g
    have hh := congrArg Subtype.val (hcfix (ConjAct.toConjAct g))
    change g * (c : P) * g⁻¹ = (c : P) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro he
    exact hcne (Subtype.ext he.symm)

private theorem center_restriction_ne_bot (S : Sylow 2 G)
    (A : Subgroup G) [A.Normal] (hA : 2 ∣ Nat.card A) :
    A.comap ((S : Subgroup G).subtype.comp (center S).subtype) ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hA
  have hxG : orderOf (x : G) = 2^1 := by simpa using hx
  obtain ⟨y, hxy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow hxG
  have hyA : (y : G) ∈ A := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    rw [← hg]
    exact (inferInstance : A.Normal).conj_mem x x.property g
  let J := A.comap (S : Subgroup G).subtype
  have hJ : J ≠ ⊥ := by
    intro he
    have hyJ : y ∈ J := hyA
    rw [he, Subgroup.mem_bot] at hyJ
    obtain ⟨g, hg⟩ := hxy
    have hh := hg.orderOf_eq (g : G)
    rw [hxG, hyJ] at hh
    norm_num at hh
  obtain ⟨c, hcJ, hcZ, hcne⟩ := normal_center_meet S.isPGroup' J hJ
  intro he
  have hc : (⟨c, hcZ⟩ : center S) ∈
      A.comap ((S : Subgroup G).subtype.comp (center S).subtype) := hcJ
  rw [he, Subgroup.mem_bot] at hc
  exact hcne (congrArg Subtype.val hc)

/-- Two even normal subgroups meet nontrivially if a Sylow two-subgroup has
cyclic center. -/
public theorem inf_ne_bot_of_even_of_cyclic_sylow_center
    (S : Sylow 2 G) (hZ : IsCyclic (center S)) (A B : Subgroup G)
    [A.Normal] [B.Normal] (hA : 2 ∣ Nat.card A) (hB : 2 ∣ Nat.card B) :
    A ⊓ B ≠ ⊥ := by
  let f : center S →* G := (S : Subgroup G).subtype.comp (center S).subtype
  let CA := A.comap f
  let CB := B.comap f
  have hCA : CA ≠ ⊥ := center_restriction_ne_bot S A hA
  have hCB : CB ≠ ⊥ := center_restriction_ne_bot S B hB
  have hpZ := S.isPGroup'.to_subgroup (center S)
  let : IsCyclic (center S) := hZ
  obtain ⟨a, ha, hane⟩ := CA.bot_or_exists_ne_one.resolve_left hCA
  let z := a ^ (orderOf a / 2)
  have hz : orderOf z = 2 :=
    orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a)) (hpZ.dvd_orderOf hane)
  have hzA : z ∈ CA := CA.pow_mem ha _
  have hzB : z ∈ CB := hpZ.involution_mem_subgroup_of_ne_bot hz CB hCB
  intro he
  have hm : f z ∈ A ⊓ B := ⟨hzA, hzB⟩
  rw [he, Subgroup.mem_bot] at hm
  have hf : Function.Injective f :=
    (S : Subgroup G).subtype_injective.comp (center S).subtype_injective
  have hz1 : z = 1 := hf (hm.trans (map_one f).symm)
  rw [hz1, orderOf_one] at hz
  norm_num at hz
end Subgroup
