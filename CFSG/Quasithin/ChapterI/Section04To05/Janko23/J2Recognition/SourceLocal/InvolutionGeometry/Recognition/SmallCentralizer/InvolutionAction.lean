module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.Transport
public import Theory.GroupTheory.FixedInvertedFactorization

/-!
# The order-27 inversion contradiction

If z inverts an odd subgroup V and s normalizes V with square one, the
unique fixed/inverted factorization under s gives
|V| = |V ∩ C_G(s)| |V ∩ C_G(sz)|. For |V| = 27, one factor is divisible
by nine. When s and z are distinct commuting involutions, both factors
are subgroups of involution centralizers.

In the hypothetical small-centralizer branch these centralizers have orders
1920 and 48, neither divisible by nine. This proves the terminal contradiction
once the actual Sylow-five normalizer supplies V and s. Their construction
is a separate obligation; no ambient group order is assumed here.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.1, printed p.260.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer

variable {G : Type*} [Group G] [Finite G]

private theorem fixed_product (V : Subgroup G) (hodd : Odd (Nat.card V))
    (s z : G) (hs : s ^ 2 = 1) (hn : s ∈ normalizer (V : Set G))
    (hi : ∀ v ∈ V, z * v * z⁻¹ = v⁻¹) :
    Nat.card V = Nat.card ↥(V ⊓ involutionCentralizer s) *
      Nat.card ↥(V ⊓ involutionCentralizer (s * z)) := by
  let φ : MulAut V := V.normalizerMonoidHom ⟨s, hn⟩
  have hφ : Function.Involutive φ := by
    have he : φ ^ 2 = 1 := by
      change V.normalizerMonoidHom (⟨s, hn⟩ : normalizer (V : Set G)) ^ 2 = 1
      rw [← map_pow, show (⟨s, hn⟩ : normalizer (V : Set G)) ^ 2 = 1 from
        Subtype.ext hs, map_one]
    exact fun v => congrArg (fun f : MulAut V => f v) he
  have hf (v : V) : φ v = v ↔ (v : G) ∈ involutionCentralizer s := by
    rw [Subtype.ext_iff]
    change s * (v : G) * s⁻¹ = (v : G) ↔ _
    rw [mul_inv_eq_iff_eq_mul, mem_centralizer_singleton_iff]
    exact eq_comm
  have hin (v : V) : φ v = v⁻¹ ↔ (v : G) ∈ involutionCentralizer (s * z) := by
    have he : (MulAut.conj (s * z)) (v : G) = ((φ v : V) : G)⁻¹ := by
      calc
        (MulAut.conj (s * z)) (v : G) =
            (MulAut.conj s) ((MulAut.conj z) (v : G)) := by
              simp only [MulAut.conj_apply, mul_inv_rev]
              group
        _ = (MulAut.conj s) ((v : G)⁻¹) := by rw [show (MulAut.conj z) (v : G) = (v : G)⁻¹ from hi v v.property]
        _ = ((φ v : V) : G)⁻¹ := map_inv _ _
    rw [Subtype.ext_iff]
    change ((φ v : V) : G) = (v : G)⁻¹ ↔ _
    rw [mem_centralizer_singleton_iff, eq_comm (a := (v : G) * (s * z)), ← mul_inv_eq_iff_eq_mul]
    change ((φ v : V) : G) = (v : G)⁻¹ ↔
      (MulAut.conj (s * z)) (v : G) = (v : G)
    rw [he, inv_eq_iff_eq_inv]
  let F := {v : V // φ v = v}
  let I := {v : V // φ v = v⁻¹}
  let m : F × I → V := fun p => p.1.val * p.2.val
  have hm : Function.Bijective m := by
    constructor
    · intro a b hab
      obtain ⟨p, _, hp⟩ := existsUnique_fixed_inverted_mul_of_odd_card hodd φ hφ (m a)
      have ha := hp (a.1.val, a.2.val) ⟨a.1.property, a.2.property, rfl⟩
      have hb := hp (b.1.val, b.2.val) ⟨b.1.property, b.2.property, hab.symm⟩
      have he := ha.trans hb.symm
      exact Prod.ext (Subtype.ext (congrArg Prod.fst he))
        (Subtype.ext (congrArg Prod.snd he))
    · intro v
      obtain ⟨⟨a, b⟩, ⟨ha, hb, he⟩, _⟩ := existsUnique_fixed_inverted_mul_of_odd_card hodd φ hφ v
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), he⟩
  let eF : F ≃ ↥(V ⊓ involutionCentralizer s) :=
    { toFun := fun v => ⟨v.val.val, v.val.property, (hf v.val).mp v.property⟩
      invFun := fun v => ⟨⟨v.val, v.property.1⟩, (hf _).mpr v.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eI : I ≃ ↥(V ⊓ involutionCentralizer (s*z)) :=
    { toFun := fun v => ⟨v.val.val, v.val.property, (hin v.val).mp v.property⟩
      invFun := fun v => ⟨⟨v.val, v.property.1⟩, (hin _).mpr v.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr (Equiv.ofBijective m hm), Nat.card_prod,
    Nat.card_congr eF, Nat.card_congr eI]


/-- The order-27 core forces a factor divisible by nine in one of the two
full centralizers. The subgroup action is the literal conjugation action. -/
theorem nine_dvd_one_centralizer (V : Subgroup G) (hV : Nat.card V = 27)
    (s z : G) (hs : s ^ 2 = 1) (hn : s ∈ normalizer (V : Set G))
    (hi : ∀ v ∈ V, z * v * z⁻¹ = v⁻¹) :
    9 ∣ Nat.card (involutionCentralizer s) ∨
      9 ∣ Nat.card (involutionCentralizer (s * z)) := by
  have hodd : Odd (Nat.card V) := by rw [hV]; decide
  have hp := fixed_product V hodd s z hs hn hi
  rw [hV] at hp
  have hd (x : G) : Nat.card ↥(V ⊓ involutionCentralizer x) ∣ 3 ^ 3 := by
    simpa only [hV, Nat.reducePow] using (card_dvd_of_le (show V ⊓ involutionCentralizer x ≤ V from inf_le_left))
  have hc (n : ℕ) (hdn : n ∣ 3^3) : n ≤ 3 ∨ 9 ∣ n := by
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdn
    interval_cases k <;> norm_num
  rcases hc _ (hd s) with h | h
  · rcases hc _ (hd (s*z)) with h' | h'
    · have hh := Nat.mul_le_mul h h'
      omega
    · exact Or.inr (dvd_trans h' (card_dvd_of_le inf_le_right))
  · exact Or.inl (dvd_trans h (card_dvd_of_le inf_le_right))

/-- Under the small-centralizer hypothesis, neither involution class can
have a centralizer with order divisible by nine. -/
theorem not_nine_dvd_centralizer {D : Seed G} {t : G}
    (ht : OtherInvolution D t) (hC : Nat.card (involutionCentralizer t) = 48)
    (u : G) (hu : orderOf u = 2) : ¬ 9 ∣ Nat.card (involutionCentralizer u) := by
  rcases ht.classes u hu with h | h
  · rw [← centralizer_card_conj h, D.localType.centralizer_card]
    decide
  · rw [← centralizer_card_conj h, hC]
    decide

/-- The source order-27 inversion configuration contradicts the two
involution-centralizer orders. No class marking for `s` is required. -/
theorem not_inverted_27 {D : Seed G} {t : G}
    (ht : OtherInvolution D t) (hC : Nat.card (involutionCentralizer t) = 48)
    (V : Subgroup G) (hV : Nat.card V = 27)
    (s : G) (hs : orderOf s = 2) (hsz : Commute s D.z) (hne : s ≠ D.z)
    (hn : s ∈ normalizer (V : Set G))
    (hi : ∀ v ∈ V, D.z * v * D.z⁻¹ = v⁻¹) : False := by
  have hs2 : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hz2 : D.z ^ 2 = 1 := by rw [← D.localType.involution]; exact pow_orderOf_eq_one D.z
  have hzInv : D.z⁻¹ = D.z := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hz2)
  have hsz2 : orderOf (s * D.z) = 2 := by
    apply orderOf_eq_prime
    · rw [hsz.mul_pow, hs2, hz2, mul_one]
    · intro he
      exact hne ((mul_eq_one_iff_eq_inv.mp he).trans hzInv)
  exact (nine_dvd_one_centralizer V hV s D.z hs2 hn hi).elim
    (not_nine_dvd_centralizer ht hC s hs)
    (not_nine_dvd_centralizer ht hC (s * D.z) hsz2)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
