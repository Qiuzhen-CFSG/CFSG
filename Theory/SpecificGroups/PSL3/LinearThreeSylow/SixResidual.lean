module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.RootScalars
public import Theory.NumberTheory.BinarySignedTorus
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# The {2,3}-residual detects noncentral Borel two-subgroups

Let P be a Sylow two-subgroup of a finite central cover K of PSL₃(2ⁿ).
Suppose W ≤ P is normalized by N_K(P), has nontrivial image in K/Z(K),
and is centralized by every element of N_K(P) of order coprime to six.
Then n > 1 forces n = 2. No restriction on the central kernel is required.

The nontrivial normal image of W in the image Sylow meets its center.
Highest-root coordinates identify the normalizer action on that center
with all field scalars. Outside degree two, 2ⁿ − 1 has a prime divisor
larger than three. Sylow surjectivity lifts a nontrivial scalar at this
prime all the way to N_K(P), where it centralizes W by hypothesis. The
scalar formula contradicts its fixing the chosen nonzero root coordinate.
This uses actual elements of order coprime to six, without replacing the
literal residual by an iteration of prime residuals.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the
larger-field paragraph in the proof of 15.3.35, printed p.1139. The
highest-root character is the intrinsic PSL₃ calculation used in E.6.8.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.RootScalars

private theorem exists_coprime_six_moving_scalar
    {A F : Type*} [Group A] [Finite A] [Field F] [Finite F]
    (φ : A →* Fˣ) (hφ : Function.Surjective φ)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) :
    ∃ a : A, Nat.Coprime (orderOf a) 6 ∧ φ a ≠ 1 := by
  have hp : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ n - 1 := by
    by_cases hn3 : n = 3
    · subst n
      exact ⟨7, by decide, by decide, by decide⟩
    · exact Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub (by omega)
  obtain ⟨p,hp,hp3,hd⟩ := hp
  let : Fact p.Prime := ⟨hp⟩
  have hd' : p ∣ Nat.card Fˣ := by rwa [Nat.card_units, hF]
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' p hd'
  have hU : IsPGroup p (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨T,hT⟩ := hU.exists_le_sylow
  obtain ⟨Q,hQ⟩ := Sylow.mapSurjective_surjective hφ p T
  have huT : u ∈ (Q : Subgroup A).map φ := by
    change u ∈ (Q.mapSurjective hφ : Subgroup Fˣ)
    rw [hQ]
    exact hT (mem_zpowers u)
  obtain ⟨a,ha,hau⟩ := huT
  have hp6 : Nat.Coprime p 6 := hp.coprime_iff_not_dvd.mpr (by
    intro hd6
    have hor := hp.dvd_mul.mp (show p ∣ 2 * 3 from hd6)
    rcases hor with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 2) h
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h
      omega)
  refine ⟨a, ?_, ?_⟩
  · simpa using Q.isPGroup'.orderOf_coprime hp6 ⟨a,ha⟩
  · rw [hau]
    intro h
    rw [h, orderOf_one] at hu
    omega

/-- A Borel-invariant Sylow two-subgroup section with nontrivial image in
the central quotient cannot be centralized by the literal {2,3}-residual
outside F₄. -/
theorem field_degree_eq_two_of_central_cover
    {K F : Type*} [Group K] [Finite K] [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : (K ⧸ center K) ≃* PSL(3,F)) (P : Sylow 2 K) (W : Subgroup K)
    (hWP : W ≤ (P : Subgroup K)) (hWZ : ¬ W ≤ center K)
    (hWN : normalizer (P : Set K) ≤ normalizer (W : Set K))
    (hfix : ∀ b ∈ normalizer (P : Set K), Nat.Coprime (orderOf b) 6 →
      b ∈ centralizer (W : Set K)) : n = 2 := by
  by_contra hn2
  let π := QuotientGroup.mk' (center K)
  have hπ := QuotientGroup.mk'_surjective (center K)
  let Q := P.mapSurjective hπ
  let D := W.map π
  have hDQ : D ≤ (Q : Subgroup (K ⧸ center K)) := map_mono hWP
  have hDne : D ≠ ⊥ := by
    intro h
    exact hWZ (by simpa only [π, QuotientGroup.ker_mk'] using (map_eq_bot_iff W).mp h)
  have hDN : (Q : Subgroup (K ⧸ center K)) ≤ normalizer (D : Set (K ⧸ center K)) :=
    (map_mono (P.le_normalizer.trans hWN)).trans (W.le_normalizer_map π)
  have : (D.subgroupOf (Q : Subgroup (K ⧸ center K))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDQ).mpr hDN
  have hDsub : D.subgroupOf (Q : Subgroup (K ⧸ center K)) ≠ ⊥ := by
    intro h
    have hh := congrArg (fun H => H.map (Q : Subgroup (K ⧸ center K)).subtype) h
    rw [map_subgroupOf_eq_of_le hDQ, Subgroup.map_bot] at hh
    exact hDne hh
  let : Nontrivial (D.subgroupOf (Q : Subgroup (K ⧸ center K))) :=
    (nontrivial_iff_ne_bot _).mpr hDsub
  let : Fact (IsPGroup 2 Q) := ⟨Q.isPGroup'⟩
  obtain ⟨z,hzne,hzcenter⟩ := exists_nontrivial_center_mem_normal
    (D.subgroupOf (Q : Subgroup (K ⧸ center K))) (p := 2)
  obtain ⟨r,χ,hr,hrange,hχ,hconj,_⟩ :=
    exists_sylow_center_scalar_action F (by omega) hF e Q
  have hzroot : ((z : Q) : K ⧸ center K) ∈ r.range := by
    rw [hrange]
    exact ⟨(z : Q),hzcenter,rfl⟩
  obtain ⟨t,ht⟩ := hzroot
  have ht0 : t.toAdd ≠ 0 := by
    intro h
    have ht1 : t = 1 := h
    apply hzne
    apply Subtype.ext
    apply Subtype.ext
    change ((z : Q) : K ⧸ center K) = 1
    simpa only [ht1,map_one] using ht.symm
  let N := normalizer (P : Set K)
  let fN : N →* normalizer (Q : Set (K ⧸ center K)) :=
    (π.comp N.subtype).codRestrict _ (fun x =>
      (P : Subgroup K).le_normalizer_map π (mem_map_of_mem π x.property))
  have hfN : Function.Surjective fN := by
    intro b
    have hb : (b : K ⧸ center K) ∈ N.map π := by
      rw [P.normalizer_map_surjective π hπ]
      exact b.property
    obtain ⟨x,hx,hxb⟩ := hb
    exact ⟨⟨x,hx⟩, Subtype.ext hxb⟩
  obtain ⟨b,hb6,hbχ⟩ := exists_coprime_six_moving_scalar (χ.comp fN)
    (hχ.comp hfN) hF hn hn2
  have hbfix : (b : K) ∈ centralizer (W : Set K) := hfix b b.property (by simpa using hb6)
  have hbf : π (b : K) ∈ centralizer (D : Set (K ⧸ center K)) := by
    apply mem_centralizer_iff.mpr
    rintro d ⟨w,hw,rfl⟩
    exact congrArg π (mem_centralizer_iff.mp hbfix w hw)
  have hfixed : π (b : K) * r t * (π (b : K))⁻¹ = r t := by
    have hh := mem_centralizer_iff.mp hbf _ z.property
    change ((z : Q) : K ⧸ center K) * π (b : K) =
      π (b : K) * ((z : Q) : K ⧸ center K) at hh
    rw [ht, ← hh, mul_inv_cancel_right]
  have hh := (hconj (fN b) t.toAdd).symm.trans hfixed
  have he := congrArg Multiplicative.toAdd (hr hh)
  apply hbχ
  apply Units.ext
  apply mul_right_cancel₀ ht0
  change (χ (fN b) : F) * t.toAdd = t.toAdd at he
  simpa only [MonoidHom.comp_apply, Units.val_one, one_mul] using he

end Matrix.PSL3.LinearThree.RootScalars
