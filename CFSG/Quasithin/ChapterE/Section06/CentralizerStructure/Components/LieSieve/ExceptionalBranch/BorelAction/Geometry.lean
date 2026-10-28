module

public import Theory.SpecificGroups.PSL2.SylowFixedQuotients
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups

/-!
# The cubic action on an A₅ Sylow four-group

The Sylow normalizer is an even point stabilizer. A three-cycle on its four
moving points fixes no nonidentity element of the four-group and cycles all
three such elements. The finite permutation calculations are checked by the
kernel; they are transported through the supplied group isomorphism.
Pointwise Sylow fixers are inner, which also identifies the Sylow centralizer.

These are the intrinsic model facts used in the PSL₂(4) Borel branch of
Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8, printed
pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.BorelAction

private abbrev A5 := alternatingGroup (Fin 5)
private def cubic (i : Fin 5) : A5 :=
  ⟨Equiv.swap 4 i * (Equiv.swap 0 1 * Equiv.swap 1 2) * Equiv.swap 4 i, by
    rw [Equiv.Perm.mem_alternatingGroup]
    by_cases h : (4 : Fin 5) = i <;> simp [h]⟩
private theorem cubic_fixes : ∀ i, (cubic i).val i = i := by decide +kernel
private theorem fourth_power : ∀ s : A5, s ^ 4 = 1 → s ^ 2 = 1 := by decide +kernel
private theorem cubic_fixed : ∀ (i : Fin 5) (s : A5), s.val i = i → s ^ 2 = 1 →
    s * cubic i = cubic i * s → s = 1 := by decide +kernel
private theorem cubic_orbits : ∀ (i : Fin 5) (s t : A5), s.val i = i → s ^ 2 = 1 → s ≠ 1 →
    t.val i = i → t ^ 2 = 1 →
    t = 1 ∨ t = s ∨ t = cubic i * s * (cubic i)⁻¹ ∨
      t = (cubic i)^2 * s * ((cubic i)^2)⁻¹ := by decide +kernel

variable {H : Type*} [Group H] [Finite H]

private theorem normalizer_coordinates (e : H ≃* A5) (S : Sylow 2 H) :
    ∃ i : Fin 5, (normalizer (S : Set H)).map e.toMonoidHom = MulAction.stabilizer A5 i := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  refine ⟨i, ?_⟩
  change (normalizer ((S : Subgroup H) : Set H)).map e.toMonoidHom = _
  rw [map_equiv_normalizer_eq]
  exact hi

private theorem sylow_square (e : H ≃* A5) (S : Sylow 2 H) (s : H) (hs : s ∈ S) :
    (e s) ^ 2 = 1 := by
  apply fourth_power
  have h := pow_card_eq_one' (x := (⟨s, hs⟩ : (S : Subgroup H)))
  have hc : Nat.card S = 4 := Theory.PSL2.SylowFixedQuotients.sylow_card_of_equiv_five e S
  rw [hc] at h
  exact (map_pow e s 4).symm.trans ((congrArg e (congrArg Subtype.val h)).trans (map_one e))

private theorem normalizer_card (e : H ≃* A5) (S : Sylow 2 H) :
    Nat.card (normalizer (S : Set H)) = 12 := by
  obtain ⟨i, hi⟩ := normalizer_coordinates e S
  rw [← card_map_of_injective (K := normalizer (S : Set H)) (f := e.toMonoidHom) e.injective, hi]
  have h : ∀ i : Fin 5, Fintype.card (MulAction.stabilizer A5 i) = 12 := by decide +kernel
  rw [Nat.card_eq_fintype_card]
  exact h i

omit [Finite H] in
private theorem center_eq_bot (e : H ≃* A5) : center H = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have he : e x ∈ center A5 := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx a)
  rw [alternatingGroup.center_eq_bot (by simp)] at he
  exact mem_bot.mpr (e.injective ((mem_bot.mp he).trans (map_one e).symm))

omit [Finite H] in
private theorem conj_injective (e : H ≃* A5) :
    Function.Injective (MulAut.conj : H →* MulAut H) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hc : x ∈ center H := by
    apply mem_center_iff.mpr
    intro y
    have h : x * y * x⁻¹ = y := congrArg (fun a : MulAut H => a y) hx
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  rwa [center_eq_bot e] at hc

private theorem centralizer_sylow_le (e : H ≃* A5) (S : Sylow 2 H) :
    centralizer (S : Set H) ≤ S := by
  intro x hx
  obtain ⟨s, hs, he⟩ := Theory.PSL2.SylowFixedQuotients.sylow_fixed_inner_of_equiv_five e S
    (MulAut.conj x) (by
      intro t ht
      change x * t * x⁻¹ = t
      rw [← mem_centralizer_iff.mp hx t ht, mul_inv_cancel_right])
  exact (conj_injective e he).symm ▸ hs

private theorem sylow_not_fixed (e : H ≃* A5) (S : Sylow 2 H)
    (s : H) (hs : s ∈ S) (hne : s ≠ 1) :
    ∃ b ∈ normalizer (S : Set H), ⁅s, b⁆ ≠ 1 := by
  obtain ⟨i, hi⟩ := normalizer_coordinates e S
  have hsi : (e s).val i = i := by
    have h : e s ∈ MulAction.stabilizer A5 i :=
      hi ▸ mem_map_of_mem e.toMonoidHom ((S : Subgroup H).le_normalizer hs)
    exact h
  obtain ⟨b, hb, he⟩ : cubic i ∈ (normalizer (S : Set H)).map e.toMonoidHom := by
    rw [hi]
    exact cubic_fixes i
  change e b = cubic i at he
  refine ⟨b, hb, ?_⟩
  intro hc
  have hm := congrArg e (commutatorElement_eq_one_iff_mul_comm.mp hc)
  simp only [map_mul, he] at hm
  exact hne (e.injective ((cubic_fixed i (e s) hsi (sylow_square e S s hs) hm).trans
    (map_one e).symm))

private theorem sylow_irreducible (e : H ≃* A5) (S : Sylow 2 H)
    (D : Subgroup H) (hDS : D ≤ S) (hn : normalizer (S : Set H) ≤ normalizer (D : Set H))
    (hne : D ≠ ⊥) : D = S := by
  obtain ⟨s, hs, hs1⟩ := (Subgroup.bot_or_exists_ne_one D).resolve_left hne
  obtain ⟨i, hi⟩ := normalizer_coordinates e S
  have fixed (t : H) (ht : t ∈ S) : (e t).val i = i := by
    have h : e t ∈ MulAction.stabilizer A5 i :=
      hi ▸ mem_map_of_mem e.toMonoidHom ((S : Subgroup H).le_normalizer ht)
    exact h
  obtain ⟨b, hb, he⟩ : cubic i ∈ (normalizer (S : Set H)).map e.toMonoidHom := by
    rw [hi]
    exact cubic_fixes i
  change e b = cubic i at he
  apply le_antisymm hDS
  intro t ht
  have hs' : e s ≠ 1 := fun h => hs1 (e.injective (h.trans (map_one e).symm))
  rcases cubic_orbits i (e s) (e t) (fixed s (hDS hs)) (sylow_square e S s (hDS hs)) hs'
      (fixed t ht) (sylow_square e S t ht) with h | h | h | h
  · have : t = 1 := e.injective (h.trans (map_one e).symm)
    exact this ▸ D.one_mem
  · exact (e.injective h).symm ▸ hs
  · have heq : t = b * s * b⁻¹ := e.injective (by simpa only [map_mul, map_inv, he] using h)
    rw [heq]
    exact (hn hb s).mp hs
  · have heq : t = b^2 * s * (b^2)⁻¹ := e.injective (by simpa only [map_mul, map_inv, map_pow, he] using h)
    rw [heq]
    exact (hn ((normalizer (S : Set H)).pow_mem hb 2) s).mp hs

/-- The normalizer acts irreducibly on the Sylow four-group, with no common
fixed element; its order and the Sylow centralizer retain the actual embedding. -/
theorem sylow_borel_geometry (e : H ≃* alternatingGroup (Fin 5)) (S : Sylow 2 H) :
    Nat.card (normalizer (S : Set H)) = 12 ∧ center H = ⊥ ∧
    centralizer (S : Set H) ≤ S ∧
    (∀ s ∈ S, s ≠ 1 → ∃ b ∈ normalizer (S : Set H), ⁅s, b⁆ ≠ 1) ∧
    (∀ D : Subgroup H, D ≤ S → normalizer (S : Set H) ≤ normalizer (D : Set H) →
      D ≠ ⊥ → D = S) := by
  exact ⟨normalizer_card e S, center_eq_bot e, centralizer_sylow_le e S,
    sylow_not_fixed e S, sylow_irreducible e S⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.BorelAction
