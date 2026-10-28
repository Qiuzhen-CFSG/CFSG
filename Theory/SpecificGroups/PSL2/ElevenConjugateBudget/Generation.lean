module

public import Theory.SpecificGroups.PSL2.ElevenConjugateBudget.Models

/-!
# Concrete inner conjugate generation in PSL₂(11)

Short checked matrix words recover the upper root element from three
conjugates of t, or from the inner four-group and its u-conjugate. Two
conjugate diagonal involutions similarly recover a root element by a fifth
power. The Weyl element supplies the opposite root where needed. Over the
prime field, powers give all root parameters, and transvection generation
gives the actual projective group.

Thus the two cyclic candidates need three inner conjugates and each
four-group candidate needs two. Every conjugator is 1, u or l in PSL₂(11).
No exhaustive actor coverage is asserted here. Source application:
Guralnick–Malle, Classification of 2F-modules I, Proposition 4.1, pp.8–9;
Aschbacher–Smith K.2, printed p.453. The matrix words are direct calculations.
-/

public section

open Matrix Subgroup
namespace Theory.PSL2.ElevenConjugateBudget
open OuterSolvable OuterSolvable.OddCoverage
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

theorem inner_pair_word :
    t * (u*t*u⁻¹) * s * (u*s*u⁻¹) * t * (u*t*u⁻¹) * t *
      (u*t*u⁻¹) * s * (u*s*u⁻¹) = u := by
  simp only [t,s,u, ← map_mul, ← map_inv]
  apply (quotientMap_eq_iff _ _).mpr
  right
  decide

theorem inner_triple_word :
    (l*t*l⁻¹) * t * (u*t*u⁻¹) * (l*t*l⁻¹) * t * (u*t*u⁻¹) *
      (l*t*l⁻¹) * t * (u*t*u⁻¹) * (l*t*l⁻¹) = u := by
  simp only [t,u,l, ← map_mul, ← map_inv]
  apply (quotientMap_eq_iff _ _).mpr
  right
  decide

private theorem transvection_nat (i j : Fin 2) (hij : i ≠ j) (n : ℕ) :
    (SpecialLinearGroup.transvection hij (1 : F)) ^ n =
      SpecialLinearGroup.transvection hij (n : F) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ, hn, ← SpecialLinearGroup.transvection_add]
    simp

theorem eq_top_of_u_l (H : Subgroup S) (hu : u ∈ H) (hl : l ∈ H) : H = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨A, rfl⟩ := quotientMap_surjective F x
  apply Matrix.SL2.transvection_induction (fun A => quotientMap F A ∈ H) ?_ ?_ A
  · intro i j hij c
    rw [← ZMod.natCast_zmod_val c, ← transvection_nat, map_pow]
    apply H.pow_mem
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hu
    · exact hl
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [map_mul]
    exact H.mul_mem hA hB

theorem inner_le_of_roots (H : Subgroup (MulAut S))
    (hu : MulAut.conj u ∈ H) (hl : MulAut.conj l ∈ H) :
    (MulAut.conj : S →* MulAut S).range ≤ H := by
  rintro _ ⟨x,rfl⟩
  have he : H.comap MulAut.conj = ⊤ := eq_top_of_u_l _ hu hl
  exact show x ∈ H.comap MulAut.conj from he ▸ mem_top x

theorem inner_le_of_t_u (H : Subgroup (MulAut S))
    (ht : MulAut.conj t ∈ H) (hu : MulAut.conj u ∈ H) :
    (MulAut.conj : S →* MulAut S).range ≤ H := by
  apply inner_le_of_roots H hu
  have h := H.inv_mem (H.mul_mem (H.mul_mem ht hu) (H.inv_mem ht))
  simpa only [← map_inv, ← map_mul, t_conj_u, inv_inv] using h


private theorem displacement {G : Type*} [_root_.Group G]
    (a : MulAut G) (ha : a*a=1) (x : G) (hx : a x = x⁻¹) :
    a * (MulAut.conj x * a * (MulAut.conj x)⁻¹) =
      MulAut.conj (x⁻¹*x⁻¹) := by
  have hc := MulAut.congr_conj a x
  change a * MulAut.conj x * a⁻¹ = MulAut.conj (a x) at hc
  rw [inv_eq_of_mul_eq_one_right ha, hx] at hc
  rw [← mul_assoc, ← mul_assoc, hc, ← map_inv, ← map_mul]

theorem outer_upper_word :
    (d * (MulAut.conj u * d * (MulAut.conj u)⁻¹)) ^ 5 = MulAut.conj u := by
  rw [displacement d d_sq u d_u, ← map_pow]
  apply congrArg MulAut.conj
  simp only [u, ← map_inv, ← map_mul, ← map_pow]
  apply congrArg (quotientMap F)
  decide

theorem outer_lower_word :
    (d * (MulAut.conj l * d * (MulAut.conj l)⁻¹)) ^ 5 = MulAut.conj l := by
  rw [displacement d d_sq l d_l, ← map_pow]
  apply congrArg MulAut.conj
  simp only [l, ← map_inv, ← map_mul, ← map_pow]
  apply congrArg (quotientMap F)
  decide

private theorem inner_word_membership (H : Subgroup (MulAut S))
    {a b c e : S} (ha : MulAut.conj a ∈ H) (hb : MulAut.conj b ∈ H)
    (hc : MulAut.conj c ∈ H) (he : MulAut.conj e ∈ H) :
    MulAut.conj (a*b*c*e*a*b*a*b*c*e) ∈ H := by
  simp only [map_mul]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
    (H.mul_mem (H.mul_mem (H.mul_mem ha hb) hc) he) ha) hb) ha) hb) hc) he

theorem inner_pair_generates (H : Subgroup (MulAut S))
    (ht : MulAut.conj t ∈ H) (hs : MulAut.conj s ∈ H)
    (htu : MulAut.conj (u*t*u⁻¹) ∈ H) (hsu : MulAut.conj (u*s*u⁻¹) ∈ H) :
    (MulAut.conj : S →* MulAut S).range ≤ H := by
  apply inner_le_of_t_u H ht
  rw [← inner_pair_word]
  exact inner_word_membership H ht htu hs hsu

private theorem triple_word_membership (H : Subgroup (MulAut S))
    {a b c : S} (ha : MulAut.conj a ∈ H) (hb : MulAut.conj b ∈ H)
    (hc : MulAut.conj c ∈ H) :
    MulAut.conj (a*b*c*a*b*c*a*b*c*a) ∈ H := by
  simp only [map_mul]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
    (H.mul_mem (H.mul_mem (H.mul_mem ha hb) hc) ha) hb) hc) ha) hb) hc) ha

theorem inner_triple_generates (H : Subgroup (MulAut S))
    (ht : MulAut.conj t ∈ H) (htu : MulAut.conj (u*t*u⁻¹) ∈ H)
    (htl : MulAut.conj (l*t*l⁻¹) ∈ H) :
    (MulAut.conj : S →* MulAut S).range ≤ H := by
  apply inner_le_of_t_u H ht
  rw [← inner_triple_word]
  exact triple_word_membership H htl ht htu

theorem outer_pair_generates (H : Subgroup (MulAut S))
    (ht : MulAut.conj t ∈ H) (hd : d ∈ H)
    (hdu : MulAut.conj u*d*(MulAut.conj u)⁻¹ ∈ H) :
    (MulAut.conj : S →* MulAut S).range ≤ H := by
  apply inner_le_of_t_u H ht
  rw [← outer_upper_word]
  exact H.pow_mem (H.mul_mem hd hdu) 5

theorem outer_triple_generates (H : Subgroup (MulAut S))
    (hd : d ∈ H) (hdu : MulAut.conj u*d*(MulAut.conj u)⁻¹ ∈ H)
    (hdl : MulAut.conj l*d*(MulAut.conj l)⁻¹ ∈ H) :
    (MulAut.conj : S →* MulAut S).range ≤ H := by
  apply inner_le_of_roots H
  · rw [← outer_upper_word]
    exact H.pow_mem (H.mul_mem hd hdu) 5
  · rw [← outer_lower_word]
    exact H.pow_mem (H.mul_mem hd hdl) 5

@[expose] def triple : Fin 3 → S := ![1,u,l]
@[expose] def pair : Fin 2 → S := ![1,u]

theorem inner_cyclic_span :
    (MulAut.conj : S →* MulAut S).range ≤
      ⨆ i, (zpowers (MulAut.conj t)).map
        (MulAut.conj (MulAut.conj (triple i))).toMonoidHom := by
  let H := ⨆ i, (zpowers (MulAut.conj t)).map
    (MulAut.conj (MulAut.conj (triple i))).toMonoidHom
  have hm (i : Fin 3) : MulAut.conj (triple i) * MulAut.conj t *
      (MulAut.conj (triple i))⁻¹ ∈ H :=
    mem_iSup_of_mem i (mem_map_of_mem _ (mem_zpowers _))
  apply inner_triple_generates
  · simpa [H, triple] using hm 0
  · simpa [H, triple, map_mul, map_inv] using hm 1
  · simpa [H, triple, map_mul, map_inv] using hm 2

theorem outer_cyclic_span :
    (MulAut.conj : S →* MulAut S).range ≤
      ⨆ i, (zpowers d).map
        (MulAut.conj (MulAut.conj (triple i))).toMonoidHom := by
  let H := ⨆ i, (zpowers d).map
    (MulAut.conj (MulAut.conj (triple i))).toMonoidHom
  have hm (i : Fin 3) : MulAut.conj (triple i) * d *
      (MulAut.conj (triple i))⁻¹ ∈ H :=
    mem_iSup_of_mem i (mem_map_of_mem _ (mem_zpowers _))
  apply outer_triple_generates
  · simpa [H, triple] using hm 0
  · simpa [H, triple] using hm 1
  · simpa [H, triple] using hm 2

theorem inner_four_span :
    (MulAut.conj : S →* MulAut S).range ≤
      ⨆ i, innerFour.map (MulAut.conj (MulAut.conj (pair i))).toMonoidHom := by
  let H := ⨆ i, innerFour.map (MulAut.conj (MulAut.conj (pair i))).toMonoidHom
  have ht : MulAut.conj t ∈ innerFour := mem_sup_left (mem_zpowers _)
  have hs : MulAut.conj s ∈ innerFour := mem_sup_right (mem_zpowers _)
  have hm (i : Fin 2) {a : MulAut S} (ha : a ∈ innerFour) :
      MulAut.conj (pair i) * a * (MulAut.conj (pair i))⁻¹ ∈ H :=
    mem_iSup_of_mem i (mem_map_of_mem _ ha)
  apply inner_pair_generates
  · simpa [H, pair] using hm 0 ht
  · simpa [H, pair] using hm 0 hs
  · simpa [H, pair, map_mul, map_inv] using hm 1 ht
  · simpa [H, pair, map_mul, map_inv] using hm 1 hs

theorem outer_four_span :
    (MulAut.conj : S →* MulAut S).range ≤
      ⨆ i, outerFour.map (MulAut.conj (MulAut.conj (pair i))).toMonoidHom := by
  let H := ⨆ i, outerFour.map (MulAut.conj (MulAut.conj (pair i))).toMonoidHom
  have ht : MulAut.conj t ∈ outerFour := mem_sup_left (mem_zpowers _)
  have hd : d ∈ outerFour := mem_sup_right (mem_zpowers _)
  have hm (i : Fin 2) {a : MulAut S} (ha : a ∈ outerFour) :
      MulAut.conj (pair i) * a * (MulAut.conj (pair i))⁻¹ ∈ H :=
    mem_iSup_of_mem i (mem_map_of_mem _ ha)
  apply outer_pair_generates
  · simpa [H, pair] using hm 0 ht
  · simpa [H, pair] using hm 0 hd
  · simpa [H, pair] using hm 1 hd



end Theory.PSL2.ElevenConjugateBudget
