module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.Representative
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.CubicCommutators.FiniteAction
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Cubic commutator growth in the literal Held seed normalizer

Let N be the full normalizer of the join of catalogue rows 20 and 21, and Q
that literal seed restricted to N. If the two-residual has two-core quotient
of order nine, then |N| = 9 * 2^n. The certified order-nine subgroup is therefore
Sylow. Conjugating any cubic element into it reduces the claim to eight checked
finite actions. Normality of Q preserves the commutator cardinality, and the
subtype map identifies the intrinsic commutator with its literal ambient image.

Only the residual quotient order remains an explicit premise. Its independent
producer and the unconditional local-subnormal assembly are separate tasks.
Source: Aschbacher--Smith, Lemma 2.3.9(7), printed p.526; GLS3 Table 5.3p with
the convention for the two local classes fused by automorphisms.
-/

public section
namespace Held.AutomorphismLocalPair
open Subgroup

namespace CubicCommutators

variable {G : Type*} [Group G] [Finite G]

private theorem card_eq_nine_mul_two_pow
    (hnine : Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) = 9) :
    ∃ n : ℕ, Nat.card G = 9 * 2 ^ n := by
  obtain ⟨m, hm⟩ := (isPGroup_quotient_pResidual (G := G) 2).exists_card_eq
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := pResidual 2 G)).exists_card_eq
  refine ⟨n + m, ?_⟩
  rw [card_eq_card_quotient_mul_card_subgroup (pResidual 2 G), hm,
    card_eq_card_quotient_mul_card_subgroup (pCore 2 (pResidual 2 G)), hnine, hn,
    pow_add]
  ring

private def sylowOfNine (R : Subgroup G) (hR : Nat.card R = 9)
    (hnine : Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) = 9) : Sylow 3 G :=
  (IsPGroup.of_card (p := 3) (n := 2) hR).toSylow (by
    obtain ⟨n, hn⟩ := card_eq_nine_mul_two_pow hnine
    have hi : R.index = 2 ^ n := by
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 9)
      rw [← hR, R.card_mul_index, hn, hR]
    rw [hi]
    intro h
    have hbad : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at hbad)

private theorem exists_conjugate_mem (R : Subgroup G) (hR : Nat.card R = 9)
    (hnine : Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) = 9)
    (x : G) (hx : orderOf x = 3) :
    ∃ g : G, (MulAut.conj g) x ∈ R := by
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx]; rfl)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S (sylowOfNine R hR hnine)
  refine ⟨g, ?_⟩
  have he := congrArg (fun P : Sylow 3 G => (P : Subgroup G)) hg
  change (S : Subgroup G).map (MulAut.conj g).toMonoidHom = R at he
  rw [← he]
  exact mem_map_of_mem _ (hS (mem_zpowers x))

omit [Finite G] in
private theorem commutator_card_conj (Q : Subgroup G) [Q.Normal] (x g : G) :
    Nat.card (⁅Q, zpowers ((MulAut.conj g) x)⁆ : Subgroup G) =
      Nat.card (⁅Q, zpowers x⁆ : Subgroup G) := by
  have he : (⁅Q, zpowers x⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom =
      ⁅Q, zpowers ((MulAut.conj g) x)⁆ := by
    have hq : Q.map (MulAut.conj g).toMonoidHom = Q := Normal.map_conj_eq Q g
    rw [map_commutator, hq, MonoidHom.map_zpowers]
    rfl
  rw [← he, card_map_of_injective (MulAut.conj g).injective]


private def intrinsicNine : Subgroup representativeLargeLocal :=
  nineSubgroup.subgroupOf representativeLargeLocal

private theorem intrinsicNine_card : Nat.card intrinsicNine = 9 :=
  (Nat.card_congr (subgroupOfEquivOfLe nineSubgroup_le).toEquiv).trans nineSubgroup_card

private theorem intrinsicNine_bound (x : representativeLargeLocal)
    (hx : x ∈ intrinsicNine) (hne : x ≠ 1) :
    12 < Nat.card (⁅representativeLargeKernel, zpowers x⁆ :
      Subgroup representativeLargeLocal) := by
  have hne' : (x : He) ≠ 1 := by
    intro h
    exact hne (Subtype.ext h)
  have hb := nineSubgroup_commutator_bound (x := (x : He)) hx hne'
  have he : (⁅representativeLargeKernel, zpowers x⁆ :
      Subgroup representativeLargeLocal).map representativeLargeLocal.subtype =
      ⁅representativeLargeSeed, zpowers (x : He)⁆ := by
    rw [map_commutator, representativeLargeKernel_map, MonoidHom.map_zpowers]
    rfl
  rwa [← he, card_map_of_injective representativeLargeLocal.subtype_injective] at hb

end CubicCommutators

/-- Every cubic element moves enough of the literal seed to generate more than
 twelve commutators; the residual order-nine calculation is the only premise. -/
theorem representative_large_cubic_commutator_bound
    (hnine : Nat.card (pResidual 2 representativeLargeLocal ⧸
      pCore 2 (pResidual 2 representativeLargeLocal)) = 9)
    (x : representativeLargeLocal) (hx : orderOf x = 3) :
    12 < Nat.card (⁅representativeLargeKernel, zpowers x⁆ :
      Subgroup representativeLargeLocal) := by
  obtain ⟨g, hg⟩ := CubicCommutators.exists_conjugate_mem
    CubicCommutators.intrinsicNine CubicCommutators.intrinsicNine_card hnine x hx
  have hxne : x ≠ 1 := by
    intro h
    subst x
    norm_num at hx
  have hgne : (MulAut.conj g) x ≠ 1 := by
    intro h
    apply hxne
    apply (MulAut.conj g).injective
    simpa only [map_one] using h
  have hb := CubicCommutators.intrinsicNine_bound ((MulAut.conj g) x) hg hgne
  rwa [CubicCommutators.commutator_card_conj] at hb

end Held.AutomorphismLocalPair
