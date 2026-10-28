module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Dihedral subgroup conjugacy through two Sylow arguments

Let `f` and `j` embed D₂ₚ into a finite group G. If p² does not divide |G|,
their rotation subgroups are Sylow and can be conjugated to each other.
Both images then lie in the normalizer of the marked rotation subgroup.
If four does not divide the order of that normalizer, their reflection
subgroups are Sylow there and a second conjugation aligns them. This second
conjugation preserves the aligned rotation subgroup, giving conjugate images.

This argument only asserts subgroup conjugacy: the rotation generators need
not match pointwise. Its concrete consumer is the marked D₁₀ in SL₃(4) used
in the local placement in Aschbacher, *Sporadic Groups* (1994), proof of 49.5,
pp.283–284. The matrix normalizer bound is a separate premise.
-/

set_option backward.isDefEq.respectTransparency false
open scoped Pointwise
public section

namespace DihedralSylowConjugacy
variable {G : Type*} [Group G]

/-- Subgroups of prime order are conjugate when the prime occurs only once
in the order of the ambient group. -/
theorem prime_subgroups_conjugate [Finite G] {p : ℕ} (hp : p.Prime)
    (hsq : ¬ p ^ 2 ∣ Nat.card G) (P Q : Subgroup G)
    (hP : Nat.card P = p) (hQ : Nat.card Q = p) :
    ∃ g : G, P.map (MulAut.conj g).toMonoidHom = Q := by
  let : Fact p.Prime := ⟨hp⟩
  have sylow (H : Subgroup G) (hH : Nat.card H = p) :
      ∃ S : Sylow p G, (S : Subgroup G) = H := by
    have hi : ¬ p ∣ H.index := by
      intro hi
      apply hsq
      rw [← H.card_mul_index, hH, pow_two]
      exact Nat.mul_dvd_mul_left p hi
    exact ⟨(IsPGroup.of_card (hH.trans (pow_one p).symm)).toSylow hi, rfl⟩
  obtain ⟨S, hS⟩ := sylow P hP
  obtain ⟨T, hT⟩ := sylow Q hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  refine ⟨g, ?_⟩
  have he := congrArg (fun U : Sylow p G => (U : Subgroup G)) hg
  change (S : Subgroup G).map (MulAut.conj g).toMonoidHom = (T : Subgroup G) at he
  simpa only [hS, hT] using he

variable {n : ℕ} [NeZero n]

/-- The rotation and one reflection generate the entire dihedral image. -/
theorem range_eq_rotation_sup_reflection (f : DihedralGroup n →* G) :
    f.range = Subgroup.zpowers (f (.r 1)) ⊔ Subgroup.zpowers (f (.sr 0)) := by
  apply le_antisymm
  · rintro _ ⟨d, rfl⟩
    cases d with
    | r i =>
      have he : DihedralGroup.r i = (.r 1 : DihedralGroup n) ^ i.val := by
        simp
      rw [he, map_pow]
      exact (Subgroup.zpowers (f (.r 1)) ⊔ Subgroup.zpowers (f (.sr 0))).pow_mem
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) _
    | sr i =>
      have he : DihedralGroup.sr i = (.sr 0 : DihedralGroup n) * (.r 1) ^ i.val := by
        simp
      rw [he, map_mul, map_pow]
      exact (Subgroup.zpowers (f (.r 1)) ⊔ Subgroup.zpowers (f (.sr 0))).mul_mem
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        ((Subgroup.zpowers (f (.r 1)) ⊔ Subgroup.zpowers (f (.sr 0))).pow_mem
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) _)
  · exact sup_le (Subgroup.zpowers_le.mpr ⟨_, rfl⟩)
      (Subgroup.zpowers_le.mpr ⟨_, rfl⟩)

/-- Every dihedral image normalizes its cyclic rotation subgroup. -/
theorem range_le_rotation_normalizer (f : DihedralGroup n →* G) :
    f.range ≤ Subgroup.normalizer (Subgroup.zpowers (f (.r 1)) : Set G) := by
  rw [range_eq_rotation_sup_reflection]
  apply sup_le Subgroup.le_normalizer
  apply Subgroup.zpowers_le.mpr
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  have he : (MulAut.conj (f (.sr 0))).toMonoidHom (f (.r 1)) = (f (.r 1))⁻¹ := by
    change f (.sr 0) * f (.r 1) * (f (.sr 0))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    simp
  change Subgroup.zpowers ((MulAut.conj (f (.sr 0))).toMonoidHom (f (.r 1))) = _
  rw [he, Subgroup.zpowers_inv]

/-- Two successive Sylow conjugations align the rotations and reflections. -/
theorem ranges_conjugate [Finite G] {p : ℕ} (hp : p.Prime)
    (hsq : ¬ p ^ 2 ∣ Nat.card G)
    (f j : DihedralGroup p →* G) (hf : Function.Injective f)
    (hj : Function.Injective j)
    (hN : ¬ 2 ^ 2 ∣ Nat.card
      (Subgroup.normalizer (Subgroup.zpowers (f (.r 1)) : Set G))) :
    ∃ g : G, j.range.map (MulAut.conj g).toMonoidHom = f.range := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have card_rotation (k : DihedralGroup p →* G) (hk : Function.Injective k) :
      Nat.card (Subgroup.zpowers (k (.r 1))) = p := by
    rw [Nat.card_zpowers, orderOf_injective k hk, DihedralGroup.orderOf_r_one]
  obtain ⟨a, ha⟩ := prime_subgroups_conjugate hp hsq
    (Subgroup.zpowers (j (.r 1))) (Subgroup.zpowers (f (.r 1)))
    (card_rotation j hj) (card_rotation f hf)
  let k : DihedralGroup p →* G := (MulAut.conj a).toMonoidHom.comp j
  have hk : Function.Injective k := (MulAut.conj a).injective.comp hj
  have hrot : Subgroup.zpowers (k (.r 1)) = Subgroup.zpowers (f (.r 1)) := by
    simpa only [MonoidHom.map_zpowers, k, MonoidHom.comp_apply] using ha
  let N := Subgroup.normalizer (Subgroup.zpowers (f (.r 1)) : Set G)
  have hkN : k.range ≤ N := by
    have h := range_le_rotation_normalizer k
    rwa [hrot] at h
  have hfN : f.range ≤ N := range_le_rotation_normalizer f
  let kN : DihedralGroup p →* N := k.codRestrict N (fun d => hkN ⟨d, rfl⟩)
  let fN : DihedralGroup p →* N := f.codRestrict N (fun d => hfN ⟨d, rfl⟩)
  have hkNi : Function.Injective kN := by
    intro x y h
    exact hk (congrArg Subtype.val h)
  have hfNi : Function.Injective fN := by
    intro x y h
    exact hf (congrArg Subtype.val h)
  have hc (q : DihedralGroup p →* N) (hq : Function.Injective q) :
      Nat.card (Subgroup.zpowers (q (.sr 0))) = 2 := by
    rw [Nat.card_zpowers, orderOf_injective q hq, DihedralGroup.orderOf_sr]
  obtain ⟨b, hb⟩ := prime_subgroups_conjugate Nat.prime_two hN
    (Subgroup.zpowers (kN (.sr 0))) (Subgroup.zpowers (fN (.sr 0)))
    (hc kN hkNi) (hc fN hfNi)
  have href : (Subgroup.zpowers (k (.sr 0))).map
      (MulAut.conj (b : G)).toMonoidHom = Subgroup.zpowers (f (.sr 0)) := by
    have he := congrArg (Subgroup.map N.subtype) hb
    simpa [MonoidHom.map_zpowers, kN, fN, MulAut.conj_apply] using he
  have hbrot : (Subgroup.zpowers (f (.r 1))).map
      (MulAut.conj (b : G)).toMonoidHom = Subgroup.zpowers (f (.r 1)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp b.property
  have hrange : k.range.map (MulAut.conj (b : G)).toMonoidHom = f.range := by
    rw [range_eq_rotation_sup_reflection k, Subgroup.map_sup, hrot, hbrot, href,
      range_eq_rotation_sup_reflection f]
  refine ⟨(b : G) * a, ?_⟩
  have he : (MulAut.conj (b : G)).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj ((b : G) * a)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  simpa only [k, MonoidHom.range_comp, Subgroup.map_map, he] using hrange
end DihedralSylowConjugacy
