module
public import Theory.Representation.BinaryAlternatingFiveFlag.Borel
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.AutomorphismTowerSimple
/-!
# Inner projections and Borel recognition in A₅

A two-perfect group acts on A₅ by inner automorphisms, since its outer
quotient is a two-group. A nontrivial two-perfect subgroup without elements
of order five, normalized by a Sylow four-group, is the corresponding A₄
point stabilizer. The latter assertion combines the existing mutual-normalizer
calculation with a small checked generation certificate for the four-group
conjugates of a cubic. Sylow conjugacy retains an explicit inner marking.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
the projection in 13.6.15, printed p.930. These results construct the projected
Borel; identifying it with the full residual image is a separate source step.
-/

@[expose] public section
open Subgroup
open BinaryPermutation.AlternatingFiveFlag BinaryPermutation.AlternatingFiveBorel
namespace AlternatingFiveProjection
local instance : DecidablePred (· ∈ B) := fun g => inferInstanceAs (Decidable (g.val 4=4))
local instance : Fintype B := Subtype.fintype _
abbrev A5 := alternatingGroup (Fin 5)
def P : Subgroup A5 := four.subgroupOf (alternatingGroup (Fin 5))
instance : DecidablePred (· ∈ P) := fun g => inferInstanceAs (Decidable (g.val ∈ four))
instance : Fintype P := Subtype.fintype _
theorem card_P : Nat.card P = 4 :=
  (Nat.card_congr (subgroupOfEquivOfLe four_even).toEquiv).trans four_card
noncomputable def sylow : Sylow 2 A5 := Sylow.ofCard P (by
  rw [card_P, nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  rw [show 60 = 2 ^ 2 * 15 by decide, Nat.factorization_mul (by decide) (by decide),
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
  rfl)

theorem normalizer_P : normalizer (P : Set A5) = B := by
  ext g
  change (∀ k : A5, k ∈ P ↔ g*k*g⁻¹ ∈ P) ↔ g.val 4=4
  have h : ∀ g : A5, (∀ k : A5, k ∈ P ↔ g*k*g⁻¹ ∈ P) ↔ g.val 4=4 := by
    decide +kernel
  exact h g

private theorem cubic_generates : ∀ b : B, b^3=1 → b≠1 → ∀ g : B,
    g=1 ∨ (∃ p : P, g.val = p.val*b.val*p.val⁻¹ ∨ g.val = p.val*b.val⁻¹*p.val⁻¹) ∨
      ∃ p q : P, g.val = (p.val*b.val*p.val⁻¹)*(q.val*b.val⁻¹*q.val⁻¹) := by
  decide +kernel

theorem eq_borel (D : Subgroup A5) (hne : D ≠ ⊥)
    (hp : IsPPerfect 2 D) (h5 : ∀ d ∈ D, d^5=1 → d=1)
    (hn : P ≤ normalizer (D : Set A5)) : D = B := by
  have hDB : D ≤ B := by
    rw [← normalizer_P]
    exact Theory.PSL2.SylowFixedQuotients.alternating_mutual_normalizes_of_no_five
      sylow D h5 hn
  have hc : Nat.card B = 12 := (Nat.card_congr marking.toEquiv.symm).trans
    (alternatingGroup.card_of_card_eq_four (by simp))
  have hd : Nat.card D ∣ 12 := hc ▸ card_dvd_of_le hDB
  have h3 : 3 ∣ Nat.card D := by
    by_contra hh
    have hm : Nat.card D = 1 ∨ Nat.card D = 2 ∨ Nat.card D = 4 := by
      have hb := Nat.le_of_dvd (by decide : 0 < 12) hd
      generalize Nat.card D = n at *
      interval_cases n <;> omega
    have ht : IsPGroup 2 D := by
      rcases hm with hm | hm | hm
      · exact IsPGroup.of_card (n := 0) (by simpa using hm)
      · exact IsPGroup.of_card (n := 1) (by simpa using hm)
      · exact IsPGroup.of_card (n := 2) (by simpa using hm)
    have he := hp.hom_eq_one_of_isPGroup ht (MonoidHom.id D)
    apply hne
    apply (eq_bot_iff_forall _).mpr
    intro d hd
    exact congrArg Subtype.val (congrArg (fun f : D →* D => f ⟨d,hd⟩) he)
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 h3
  have hb3 : (b.val : A5)^3=1 := congrArg Subtype.val (hb ▸ pow_orderOf_eq_one b)
  have hbne : (b.val : A5) ≠ 1 := by
    intro he
    have hb1 : b=1 := Subtype.ext he
    simp [hb1] at hb
  apply le_antisymm hDB
  intro g hg
  rcases cubic_generates ⟨b.val,hDB b.property⟩ (Subtype.ext hb3)
    (fun he => hbne (congrArg Subtype.val he)) ⟨g,hg⟩ with h | ⟨p,h|h⟩ | ⟨p,q,h⟩
  · have hg1 : g=1 := congrArg Subtype.val h
    rw [hg1]
    exact D.one_mem
  · change g = p.val*b.val*p.val⁻¹ at h
    rw [h]
    exact (hn p.property b.val).mp b.property
  · change g = p.val*b.val⁻¹*p.val⁻¹ at h
    rw [h]
    exact (hn p.property b.val⁻¹).mp (D.inv_mem b.property)
  · change g = (p.val*b.val*p.val⁻¹)*(q.val*b.val⁻¹*q.val⁻¹) at h
    rw [h]
    exact D.mul_mem ((hn p.property b.val).mp b.property)
      ((hn q.property b.val⁻¹).mp (D.inv_mem b.property))

theorem conjugate_eq_borel (S : Sylow 2 A5) (D : Subgroup A5) (hne : D ≠ ⊥)
    (hp : IsPPerfect 2 D) (h5 : ∀ d ∈ D, d^5=1 → d=1)
    (hn : (S : Subgroup A5) ≤ normalizer (D : Set A5)) :
    ∃ g : A5, D.map (MulAut.conj g).toMonoidHom = B := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A5 S sylow
  let e := MulAut.conj g
  have hP : (S : Subgroup A5).map e.toMonoidHom = P := by
    have he := congrArg (fun Q : Sylow 2 A5 => (Q : Subgroup A5)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at he
    exact he
  refine ⟨g, eq_borel (D.map e.toMonoidHom) ?_ ?_ ?_ ?_⟩
  · exact fun hb => hne ((D.map_eq_bot_iff_of_injective e.injective).mp hb)
  · exact hp.of_surjective (e.toMonoidHom.subgroupMap D)
      (e.toMonoidHom.subgroupMap_surjective D)
  · rintro _ ⟨d,hd,rfl⟩ he
    have hd5 : d^5=1 := e.injective (by
      change e d ^ 5 = 1 at he
      simpa only [map_pow,map_one] using he)
    rw [h5 d hd hd5,map_one]
  · rw [← hP, ← map_equiv_normalizer_eq]
    exact map_mono hn

private theorem outer_two : IsPGroup 2 (MulAut.Outer A5) := by
  intro q
  obtain ⟨α,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A5) q
  obtain ⟨σ,rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide)
      (by decide)).surjective α
  refine ⟨1, ?_⟩
  simp only [pow_one, ← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hσ : σ^2 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup,map_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h|h <;> simp [h]
  exact ⟨⟨σ^2,hσ⟩,MulAut.conjNormal_val.symm⟩

theorem exists_inner_lift {D C : Type*} [Group D] [Group C]
    (hD : IsPPerfect 2 D) (a : D →* MulAut C) (e : C ≃* A5) :
    ∃ f : D →* C, (MulAut.conj : C →* MulAut C).comp f = a := by
  let b := (MulAut.congr e).toMonoidHom.comp a
  let q := QuotientGroup.mk' (MulAut.innerSubgroup A5)
  have ht : q.comp b = 1 := hD.hom_eq_one_of_isPGroup outer_two (q.comp b)
  have hi : ∀ d, b d ∈ MulAut.innerSubgroup A5 := by
    intro d
    exact (QuotientGroup.eq_one_iff _).mp
      (congrArg (fun f : D →* MulAut.Outer A5 => f d) ht)
  let j : A5 ≃* MulAut.innerSubgroup A5 := MonoidHom.ofInjective
    (MulAut.conj_injective_of_center_eq_bot (alternatingGroup.center_eq_bot (by simp)))
  let f := e.symm.toMonoidHom.comp (j.symm.toMonoidHom.comp (b.codRestrict _ hi))
  refine ⟨f, ?_⟩
  apply MonoidHom.ext
  intro d
  apply (MulAut.congr e).injective
  change MulAut.congr e (MulAut.conj (f d)) = b d
  rw [MulAut.congr_conj]
  have he : e (f d) = j.symm ⟨b d, hi d⟩ := e.apply_symm_apply _
  rw [he]
  exact congrArg Subtype.val (j.apply_symm_apply ⟨b d, hi d⟩)

theorem no_five_of_core_quotient_three {D : Type*} [Group D] [Finite D]
    (hc : Nat.card (D ⧸ pCore 2 D) = 3) (d : D) (hd : d^5=1) : d=1 := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
  have hcard := card_eq_card_quotient_mul_card_subgroup (pCore 2 D)
  rw [hc,hn] at hcard
  have hco : (Nat.card D).Coprime 5 := by rw [hcard]; exact (by decide : Nat.Coprime 3 5).mul_left ((by decide : Nat.Coprime 2 5).pow_left n)
  exact (powCoprime hco).injective (by simpa using hd)
end AlternatingFiveProjection
