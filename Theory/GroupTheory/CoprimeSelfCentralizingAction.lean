module

public import Theory.GroupTheory.PGroupSelfCentralizingAction

/-!
# Coprime actors fixing a self-centralizing normal subgroup

If A normalizes Y and fixes its normal self-centralizing subgroup N, the
three-subgroups lemma puts [A,Y] in N. Each displacement has order dividing
the order of A. Coprimality with |N| therefore makes every displacement
trivial. All normalization is relative to Y and the action is ambient
conjugation.

Source: the self-centralizing action argument of Aschbacher–Smith A.1.9,
and its application to the odd Hall axis in 10.2.3, printed p.747.
-/

open Subgroup
open scoped commutatorElement

/-- A coprime actor fixing a normal self-centralizing subgroup fixes the whole target. -/
public theorem Subgroup.centralizes_of_coprime_of_selfCentralizing_normal
    {G : Type*} [Group G] [Finite G]
    (A Y : Subgroup G) (N : Subgroup Y) [N.Normal]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card N))
    (hn : A ≤ normalizer (Y : Set G))
    (hself : centralizer (N : Set Y) ≤ N)
    (hfix : A ≤ centralizer (N.map Y.subtype : Set G)) :
    A ≤ centralizer (Y : Set G) := by
  let F := N.map Y.subtype
  have hYN : Y ≤ normalizer (F : Set G) := by
    have hh := N.le_normalizer_map Y.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hNA : ⁅F,A⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hfix
  have hNYA : ⁅⁅F,Y⁆,A⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono (le_normalizer_iff_commutator_le_left.mp hYN) le_rfl).trans hNA.le
  have hAYN : ⁅⁅A,Y⁆,F⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · simpa only [commutator_comm Y F] using hNYA
    · simp only [hNA, commutator_bot_left]
  have hAYY : ⁅A,Y⁆ ≤ Y := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hn
  have hAYC : ⁅A,Y⁆ ≤ centralizer (F : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hAYN
  intro a ha y hy
  let x := ⁅a,y⁆
  have hxY : x ∈ Y := hAYY (commutator_mem_commutator ha hy)
  have hxN : (⟨x,hxY⟩ : Y) ∈ N := by
    apply hself
    intro z hz
    exact Subtype.ext (hAYC (commutator_mem_commutator ha hy) z (mem_map_of_mem Y.subtype hz))
  have hxF : x ∈ F := mem_map_of_mem Y.subtype hxN
  have hax : Commute a x := (hfix ha x hxF).symm
  have hapow : a ^ Nat.card A = 1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨a,ha⟩ : A)))
  have hpow : x ^ Nat.card A = 1 := by
    have he : a⁻¹ * x = y * a⁻¹ * y⁻¹ := by dsimp [x]; group
    have hh : Commute a (a⁻¹*x) := (Commute.refl a).inv_right.mul_right hax
    calc
      x ^ Nat.card A = (a * (a⁻¹*x)) ^ Nat.card A := by simp
      _ = a ^ Nat.card A * (a⁻¹*x) ^ Nat.card A := hh.mul_pow _
      _ = 1 := by rw [he, conj_pow, inv_pow, hapow]; simp
  let c : N := ⟨⟨x,hxY⟩,hxN⟩
  have hc : c ^ Nat.card A = 1 := Subtype.ext (Subtype.ext hpow)
  have ho : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hc) (_root_.orderOf_dvd_natCard c)
  have hxone : x = 1 := congrArg (fun z : N => (z : G)) (orderOf_eq_one_iff.mp ho)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hxone).symm
