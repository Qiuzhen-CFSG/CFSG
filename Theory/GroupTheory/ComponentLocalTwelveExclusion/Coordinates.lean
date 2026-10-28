module

public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Order-twelve subgroups of characteristic-two direct powers

An injective subnormal image of a centerless two-perfect group of order twelve
has a nontrivial coordinate. Each coordinate order divides twelve. Two-group
images vanish by two-perfection; order six forces a central kernel of order
two; order three contradicts characteristic two and subnormal core action.
The remaining order-twelve image is excluded by the explicit factor premise.

This general transfer calculation is used in Aschbacher–Smith, E.6.7–8,
*The Classification of Quasithin Groups*, printed pp.246–248. The intrinsic
factor exclusion is deliberately a separate hypothesis.
-/

public section

open Subgroup
namespace Theory.GroupTheory.ComponentLocalTwelveExclusion
variable {B X I : Type*} [Group B] [Finite B] [Group X]

private theorem eq_bot_of_subnormal_perfect_core_bot
    (hB : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (E : Subgroup B) (hs : E.IsSubnormal) (hp : IsPPerfect 2 E)
    (hc : pCore 2 E = ⊥) : E = ⊥ := by
  have hcomm := commutator_le_core_commutator_of_isSubnormal E (pCore 2 B)
    hs hp pCore_isPGroup (by rw [normalizer_eq_top]; exact le_top)
  rw [hc, commutator_bot_left, Subgroup.map_bot] at hcomm
  have hE : E ≤ pCore 2 B := (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hcomm))).trans hB
  have hid := hp.hom_eq_one_of_isPGroup (pCore_isPGroup.to_le hE) (MonoidHom.id E)
  apply eq_bot_iff.mpr
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun hid ⟨x, hx⟩)

private theorem ne_three_of_subnormal_perfect
    (hB : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (E : Subgroup B) (hs : E.IsSubnormal) (hp : IsPPerfect 2 E) :
    Nat.card E ≠ 3 := by
  intro hcard
  have hc : pCore 2 E = ⊥ := by
    apply eq_bot_of_card_eq
    rcases (pCore_isPGroup (p := 2) (G := E)).card_eq_or_dvd with h | h
    · exact h
    · have hd := h.trans (pCore 2 E).card_subgroup_dvd_card
      rw [hcard] at hd
      norm_num at hd
  have he := eq_bot_of_subnormal_perfect_core_bot hB E hs hp hc
  have := E.eq_bot_iff_card.mp he
  omega

/-- A centerless two-perfect group of order twelve cannot embed subnormally
in a direct power whose characteristic-two factor excludes such subnormal groups. -/
theorem no_subnormal_embedding_power
    (hB : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (hex : ∀ E : Subgroup B, E.IsSubnormal → IsPPerfect 2 E → Nat.card E ≠ 12)
    (hX : IsPPerfect 2 X) (hZ : center X = ⊥) (hc : Nat.card X = 12)
    (g : X →* (I → B)) (hg : Function.Injective g) (hs : g.range.IsSubnormal) : False := by
  have hg1 (x : X) (i : I) : g x i = 1 := by
    let ev : (I → B) →* B := Pi.evalMonoidHom (fun _ => B) i
    have hev : Function.Surjective ev := fun b => ⟨fun _ => b, rfl⟩
    let f := ev.comp g
    have hsE : f.range.IsSubnormal := by
      rw [MonoidHom.range_comp]
      exact hs.map hev
    have hpE : IsPPerfect 2 f.range :=
      hX.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hd : Nat.card f.range ∣ 12 := hc ▸ card_range_dvd f
    have hcases : Nat.card f.range = 1 ∨ Nat.card f.range = 2 ∨
        Nat.card f.range = 3 ∨ Nat.card f.range = 4 ∨
        Nat.card f.range = 6 ∨ Nat.card f.range = 12 := by
      have hle := Nat.le_of_dvd (by decide : 0 < 12) hd
      interval_cases Nat.card f.range <;> simp_all
    have ht (htwo : Nat.card f.range ∣ 2 ^ 2) : f x = 1 := by
      have hf := hX.hom_eq_one_of_isPGroup
        (IsPGroup.of_card_dvd_pow htwo) f.rangeRestrict
      exact congrArg Subtype.val (DFunLike.congr_fun hf x)
    rcases hcases with h | h | h | h | h | h
    · exact ht (by rw [h]; norm_num)
    · exact ht (by rw [h]; norm_num)
    · exact (ne_three_of_subnormal_perfect hB f.range hsE hpE h).elim
    · exact ht (by rw [h]; norm_num)
    · have hk : Nat.card f.ker = 2 := by
        have hh := f.ker.card_mul_index
        rw [index_ker, h, hc] at hh
        omega
      have hb : f.ker = ⊥ := le_bot_iff.mp
        ((central_of_normal_card_two f.ker hk).trans hZ.le)
      have := f.ker.eq_bot_iff_card.mp hb
      omega
    · exact (hex f.range hsE hpE h).elim
  have hsub : Subsingleton X := ⟨fun x y => hg (by
    ext i
    rw [hg1 x i, hg1 y i])⟩
  have : Nat.card X = 1 := Nat.card_unique
  omega
end Theory.GroupTheory.ComponentLocalTwelveExclusion
