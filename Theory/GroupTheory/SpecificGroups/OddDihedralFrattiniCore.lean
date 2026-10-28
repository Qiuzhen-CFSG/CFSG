module
public import Theory.GroupTheory.SpecificGroups.DihedralQuotientSylow
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Frattini

/-!
# Frattini containment in an odd-dihedral core quotient

Suppose a finite group's quotient by its two-core is explicitly isomorphic
to a dihedral group of odd rotation order. For every two-subgroup X, the
ambient image of Φ(X) lies in that two-core.

The image of X under the actual core quotient map is a two-subgroup. Extend
it to a Sylow subgroup and use the odd-dihedral quotient Sylow bound to give
it order at most two. A group of order at most two has trivial Frattini
subgroup: a nontrivial Frattini subgroup would be the whole group, contrary
to the nongenerating property. Surjective Frattini functoriality for the
restricted quotient map then kills every element of Φ(X), proving the core
containment. No nontriviality assumption on X is needed.

This elementary transfer supplies the neighboring-core Frattini containment
in Stellmacher (8.2), Journal of Algebra 190 (1997), p.38;
source: `refs/latex/stellmacher-n-group.tex`. All imports are at the general
finite-group theory layer.
-/

private theorem frattini_eq_bot_of_card_le_two
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G ≤ 2) :
    frattini G = ⊥ := by
  by_cases hbot : frattini G = ⊥
  · exact hbot
  have hnontriv := (frattini G).one_lt_card_iff_ne_bot.mpr hbot
  have htop : frattini G = ⊤ := Subgroup.eq_of_le_of_card_ge le_top (by
    rw [Subgroup.card_top]
    omega)
  have hbot_top : (⊥ : Subgroup G) = ⊤ := frattini_nongenerating (by simp [htop])
  exact htop.trans hbot_top.symm

/-- A two-subgroup has Frattini image in the core of an odd-dihedral core quotient. -/
public theorem frattini_two_subgroup_le_twoCore_of_odd_dihedral_quotient
    {P : Type*} [Group P] [Finite P] (n : ℕ) (hn : Odd n)
    (model : (P ⧸ pCore 2 P) ≃* DihedralGroup n)
    (X : Subgroup P) (hX : IsPGroup 2 X) :
    (frattini X).map X.subtype ≤ pCore 2 P := by
  let q := QuotientGroup.mk' (pCore 2 P)
  let image := X.map q
  have hIp : IsPGroup 2 image := hX.map q
  obtain ⟨S, hIS⟩ := hIp.exists_le_sylow
  have hIcard : Nat.card image ≤ 2 := by
    apply (Nat.card_le_card_of_injective (Subgroup.inclusion hIS)
      (Subgroup.inclusion_injective hIS)).trans
    exact (odd_dihedral_quotient_sylow n hn model.symm.toMonoidHom
      model.symm.surjective S).1
  have hPhi : frattini X ≤ (frattini image).comap (q.subgroupMap X) :=
    frattini_le_comap_frattini_of_surjective (q.subgroupMap_surjective X)
  rw [frattini_eq_bot_of_card_le_two hIcard] at hPhi
  rintro x ⟨y, hy, rfl⟩
  have heq : q y = 1 := congrArg Subtype.val (hPhi hy)
  exact (QuotientGroup.eq_one_iff (N := pCore 2 P) (y : P)).mp heq
