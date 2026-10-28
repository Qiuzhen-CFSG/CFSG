module
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# Irreducibility of a four-group under a two-perfect subgroup

An action of a two-perfect group on a group of order four is trivial if
it fixes a nonidentity point: the point stabilizer has order at most two.
Consequently, if a two-perfect subgroup and a two-group supplement act
irreducibly on an elementary four-group, the two-perfect subgroup already
acts irreducibly. Otherwise it fixes the whole four-group, and the supplement's
fixed-point theorem supplies an invariant subgroup of order two.

The source application removes the dotted Sylow supplement from L₀T in
the orthogonal branch of Aschbacher--Smith 12.9.4, printed pp.859--860.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A two-perfect group fixing a point of a group of order four fixes the whole group. -/
theorem twoPerfect_centralizes_four_of_fixed_point
    (R D : Subgroup G) (hR : IsPPerfect 2 R) (hD : Nat.card D = 4)
    (hRD : R ≤ normalizer (D : Set G)) (z : D) (hz : z ≠ 1)
    (hf : ∀ r ∈ R, r * (z:G) * r⁻¹ = z) : R ≤ centralizer (D : Set G) := by
  let f : R →* MulAut D := D.normalizerMonoidHom.comp (inclusion hRD)
  have hc : Nat.card f.range ≤ 2 := card_mulAut_subgroup_le_two_of_fixed_point hD z hz
    f.range (by rintro _ ⟨r,rfl⟩; exact Subtype.ext (hf r r.property))
  have hp : IsPGroup 2 f.range := by
    have hp := Nat.card_pos (α := f.range)
    have he : Nat.card f.range = 2 ^ 0 ∨ Nat.card f.range = 2 ^ 1 := by omega
    rcases he with he | he
    · exact IsPGroup.of_card he
    · exact IsPGroup.of_card he
  have he := hR.hom_eq_one_of_isPGroup hp f.rangeRestrict
  intro r hr d hd
  have hh := congrArg (fun a : f.range => ((a:MulAut D) ⟨d,hd⟩ : G))
    (DFunLike.congr_fun he (⟨r,hr⟩ : R))
  change r*d*r⁻¹ = d at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Irreducibility on a four-group passes through a two-group supplement. -/
theorem four_irreducible_of_twoPerfect_supplement
    (R Q D : Subgroup G) [IsElementaryAbelian 2 D]
    (hR : IsPPerfect 2 R) (hQ : IsPGroup 2 Q) (hD : Nat.card D = 4)
    (hRD : R ≤ normalizer (D : Set G)) (hQD : Q ≤ normalizer (D : Set G))
    (hirr : ∀ A : Subgroup G, A ≤ D → R ⊔ Q ≤ normalizer (A : Set G) → A = ⊥ ∨ A = D) :
    ∀ A : Subgroup G, A ≤ D → R ≤ normalizer (A : Set G) → A = ⊥ ∨ A = D := by
  have hmove : ¬ R ≤ centralizer (D : Set G) := by
    intro hc
    let f : Q →* MulAut D := D.normalizerMonoidHom.comp (inclusion hQD)
    let : MulAction Q D := MulAction.compHom D f
    have hfix : (1:D) ∈ MulAction.fixedPoints Q D := fun q => map_one (f q)
    obtain ⟨z,hz,hz1⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point D
      (by rw [hD]; decide) hfix
    have hzG : (z:G) ≠ 1 := fun he => hz1 (Subtype.ext he).symm
    have hz2 : (z:G)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := D) (p := 2) (z:G) z.property
    have hcard : Nat.card (zpowers (z:G)) = 2 := by
      rw [Nat.card_zpowers,orderOf_eq_prime hz2 hzG]
    have hnorm : R ⊔ Q ≤ normalizer (zpowers (z:G) : Set G) := by
      apply (sup_le ?_ ?_).trans (Subgroup.centralizer_le_normalizer _)
      · intro r hr
        rw [zpowers_eq_closure,centralizer_closure]
        exact mem_centralizer_singleton_iff.mpr (hc hr z z.property).symm
      · intro q hq
        rw [zpowers_eq_closure,centralizer_closure]
        apply mem_centralizer_singleton_iff.mpr
        have hh := congrArg Subtype.val (hz ⟨q,hq⟩)
        change q*(z:G)*q⁻¹ = z at hh
        exact mul_inv_eq_iff_eq_mul.mp hh
    rcases hirr (zpowers (z:G)) (zpowers_le.mpr z.property) hnorm with he | he
    · simp [he] at hcard
    · rw [he,hD] at hcard
      contradiction
  intro A hAD hRA
  by_cases hb : A = ⊥
  · exact Or.inl hb
  by_cases he : A = D
  · exact Or.inr he
  have hA : Nat.card A = 2 := by
    have hlo := (one_lt_card_iff_ne_bot A).mpr hb
    have hhi : Nat.card A < Nat.card D := lt_of_le_of_ne (card_le_of_le hAD)
      (fun hh => he (eq_of_le_of_card_ge hAD hh.ge))
    have hd := card_dvd_of_le hAD
    rw [hD] at hhi hd
    have hne3 : Nat.card A ≠ 3 := by intro hh; rw [hh] at hd; norm_num at hd
    omega
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb
  have hfix : R ≤ centralizer (A : Set G) :=
    hRA.trans (normalizer_le_centralizer_of_card_two A hA)
  exact (hmove (twoPerfect_centralizes_four_of_fixed_point R D hR hD hRD
    ⟨z,hAD z.property⟩ (fun hh => hz (Subtype.ext (congrArg (fun x : D => (x:G)) hh)))
    (by intro r hr; exact mul_inv_eq_iff_eq_mul.mpr (hfix hr z z.property).symm))).elim
end Subgroup
