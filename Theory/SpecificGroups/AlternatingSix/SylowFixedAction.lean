module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.Alternating.proposition_5_2_7_8
public import Theory.GroupAction.InnerExtension
public import Theory.ElementaryAbelian.Basic

/-!
# Four-group actions fixing a Sylow subgroup of A₆

A faithful elementary four-group fixing a Sylow two-subgroup of A₆ generates
the natural S₆ together with the inner automorphisms. The equivalence to S₆
identifies each inner automorphism with its even permutation and preserves
the given action on every element of A₆.

An involution outside the natural S₆ fixes D₁₀, which cannot contain the
Sylow D₈. Inner involutions fixing that Sylow subgroup lie in its center,
of order two. Thus the four-group is contained in S₆ and has an outer actor;
the index-two extension is consequently all of S₆.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 15.4.18, printed
pp.1162–1163. The exceptional-involution input is the actual fixed-subgroup
calculation in GLS, Volume 3, Proposition 5.2.7(a).
-/

@[expose] public section

open Subgroup
namespace AlternatingSix.ShadowLocal

private theorem sylow_center_card (P : Sylow 2 A6) : Nat.card (center (P : Subgroup A6)) = 2 := by
  obtain ⟨e⟩ := alternatingSylow_dihedral P
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

/-- An involution fixing a Sylow two-subgroup is permutation induced. -/
theorem involution_mem_natural_of_fixes_sylow (P : Sylow 2 A6)
    (β : AutA6) (hβ : orderOf β = 2)
    (hfix : ∀ x ∈ (P : Subgroup A6), β x = x) : β ∈ natural := by
  by_contra hn
  obtain ⟨e⟩ := GLS3.Chapter5.a6_outsideNatural_involution_fixed_equiv_dihedral β hβ hn
  have hp : (P : Subgroup A6) ≤ GLS3.Chapter5.automorphismFixedSubgroup β := hfix
  have hd := Subgroup.card_dvd_of_le hp
  rw [alternatingSylow_card, Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hd
  norm_num at hd

private theorem inner_actor_mem_center (P : Sylow 2 A6)
    (a : A6) (ha : a ^ 2 = 1)
    (hfix : ∀ x ∈ (P : Subgroup A6), MulAut.conj a x = x) :
    ∃ haP : a ∈ (P : Subgroup A6), (⟨a, haP⟩ : (P : Subgroup A6)) ∈ center (P : Subgroup A6) := by
  by_cases hane : a = 1
  · subst a
    exact ⟨one_mem _, one_mem _⟩
  have hao : orderOf a = 2 := orderOf_eq_prime ha hane
  have hle : (P : Subgroup A6) ≤ GLS3.Chapter5.automorphismFixedSubgroup (MulAut.conj a) := hfix
  have he : (P : Subgroup A6) = GLS3.Chapter5.automorphismFixedSubgroup (MulAut.conj a) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [alternatingSylow_card, inner_involution_fixed_card a hao])
  have haP : a ∈ (P : Subgroup A6) := by
    rw [he]
    change a * a * a⁻¹ = a
    simp
  refine ⟨haP, ?_⟩
  apply (Subgroup.mem_center_iff (G := (P : Subgroup A6))).mpr
  intro x
  apply Subtype.ext
  have hx := hfix x x.property
  change a * (x : A6) * a⁻¹ = x at hx
  exact (mul_inv_eq_iff_eq_mul.mp hx).symm

/-- A faithful four-group fixing a Sylow two-subgroup contains an outer actor. -/
theorem range_not_le_inner_of_fixes_sylow
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (P : Sylow 2 A6) (ρ : A →* AutA6) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4) (hfix : ∀ a x, x ∈ (P : Subgroup A6) → ρ a x = x) :
    ¬ ρ.range ≤ inner := by
  intro hi
  let f : A →* A6 := innerEquiv.symm.toMonoidHom.comp
    (ρ.codRestrict inner (fun a => hi ⟨a, rfl⟩))
  have hf (a : A) : MulAut.conj (f a) = ρ a := by
    exact congrArg Subtype.val (innerEquiv.apply_symm_apply ⟨ρ a, hi ⟨a, rfl⟩⟩)
  have hfinj : Function.Injective f := by
    intro a b h
    apply hρ
    rw [← hf a, ← hf b, h]
  have hc (a : A) : ∃ haP : f a ∈ (P : Subgroup A6),
      (⟨f a, haP⟩ : (P : Subgroup A6)) ∈ center (P : Subgroup A6) := by
    apply inner_actor_mem_center P (f a)
    · rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a, map_one]
    · intro x hx
      rw [hf]
      exact hfix a x hx
  let j : A → center (P : Subgroup A6) := fun a => ⟨⟨f a, (hc a).choose⟩, (hc a).choose_spec⟩
  have hj : Function.Injective j := fun a b h => hfinj
    (congrArg (fun x : center (P : Subgroup A6) => ((x : P) : A6)) h)
  have hd := Nat.card_le_card_of_injective j hj
  rw [hA, sylow_center_card] at hd
  omega

/-- The generated automorphism subgroup is exactly the natural symmetric group. -/
theorem inner_sup_range_eq_natural_of_fixes_sylow
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (P : Sylow 2 A6) (ρ : A →* AutA6) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4) (hfix : ∀ a x, x ∈ (P : Subgroup A6) → ρ a x = x) :
    inner ⊔ ρ.range = natural := by
  have hn : ρ.range ≤ natural := by
    rintro β ⟨a, rfl⟩
    by_cases ha : a = 1
    · subst a
      simp
    · apply involution_mem_natural_of_fixes_sylow P (ρ a)
      · rw [orderOf_injective _ hρ]
        exact orderOf_eq_prime
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 A) a) ha
      · exact hfix a
  have hle : inner ⊔ ρ.range ≤ natural := sup_le inner_le_natural hn
  have hlt : inner < inner ⊔ ρ.range := lt_of_le_of_ne le_sup_left (by
    intro he
    exact range_not_le_inner_of_fixes_sylow P ρ hρ hA hfix
      (he.symm ▸ (show ρ.range ≤ inner ⊔ ρ.range from le_sup_right)))
  have hi := Subgroup.index_strictAnti hlt
  have hnidx : natural.index = 2 := GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index
  rw [inner_index] at hi
  have hid := Subgroup.index_dvd_of_le (show inner ≤ inner ⊔ ρ.range from le_sup_left)
  rw [inner_index] at hid
  have hpos : (inner ⊔ ρ.range).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hge := Subgroup.index_antitone hle
  rw [hnidx] at hge
  have heq : (inner ⊔ ρ.range).index = 2 := by
    obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show (inner ⊔ ρ.range).index ∣ 2 ^ 2 from hid)
    interval_cases n
    · change (inner ⊔ ρ.range).index = 1 at he
      omega
    · exact he
    · change (inner ⊔ ρ.range).index = 4 at he
      omega
  by_contra hne
  have := Subgroup.index_strictAnti (lt_of_le_of_ne hle hne)
  omega

end AlternatingSix.ShadowLocal

namespace AlternatingSix.ShadowLocal
open Subgroup

/-- The actual permutation equivalence of the group generated by the component
and the given faithful four-group. -/
noncomputable def sylowFixedExtensionEquiv
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (P : Sylow 2 A6) (ρ : A →* AutA6) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4) (hfix : ∀ a x, x ∈ (P : Subgroup A6) → ρ a x = x) :
    MulAut.innerExtension ρ ≃* Equiv.Perm (Fin 6) :=
  (MulEquiv.subgroupCongr (inner_sup_range_eq_natural_of_fixes_sylow P ρ hρ hA hfix)).trans
    (MonoidHom.ofInjective permutationAction_injective).symm

theorem permutationAction_sylowFixedExtensionEquiv
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (P : Sylow 2 A6) (ρ : A →* AutA6) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4) (hfix : ∀ a x, x ∈ (P : Subgroup A6) → ρ a x = x)
    (g : MulAut.innerExtension ρ) :
    permutationAction (sylowFixedExtensionEquiv P ρ hρ hA hfix g) = g.val := by
  exact congrArg Subtype.val
    ((MonoidHom.ofInjective permutationAction_injective).apply_symm_apply
      (MulEquiv.subgroupCongr (inner_sup_range_eq_natural_of_fixes_sylow P ρ hρ hA hfix) g))

theorem sylowFixedExtensionEquiv_inner
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (P : Sylow 2 A6) (ρ : A →* AutA6) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4) (hfix : ∀ a x, x ∈ (P : Subgroup A6) → ρ a x = x)
    (x : A6) :
    sylowFixedExtensionEquiv P ρ hρ hA hfix
      ⟨MulAut.conj x, MulAut.conj_mem_innerExtension ρ x⟩ = (x : Equiv.Perm (Fin 6)) := by
  apply permutationAction_injective
  rw [permutationAction_sylowFixedExtensionEquiv, permutationAction_coe]

theorem sylowFixedExtensionEquiv_action
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (P : Sylow 2 A6) (ρ : A →* AutA6) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4) (hfix : ∀ a x, x ∈ (P : Subgroup A6) → ρ a x = x)
    (g : MulAut.innerExtension ρ) (x : A6) :
    (g.val x : Equiv.Perm (Fin 6)) =
      sylowFixedExtensionEquiv P ρ hρ hA hfix g * (x : Equiv.Perm (Fin 6)) *
        (sylowFixedExtensionEquiv P ρ hρ hA hfix g)⁻¹ := by
  rw [← permutationAction_sylowFixedExtensionEquiv P ρ hρ hA hfix g]
  rfl

end AlternatingSix.ShadowLocal
