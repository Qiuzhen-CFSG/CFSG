module
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.LinearRank
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Inner involution fixed groups in odd-prime PSL₃

The scalar center of SL₃ has exponent dividing three. Cubing a lift gives
an actual involution above a projective involution. If a matrix commutes
with this involution projectively, its central commutator has both square
and cube one, so the matrices commute in SL₃. Thus the canonical projection
maps the full linear centralizer onto the full projective centralizer.

The existing involution eigenbasis identifies the linear centralizer with
GL₂. Its projective image therefore has derived three-rank at most one for
prime fields other than three. This treats every inner involution, including
fields with nontrivial projective scalar kernel.

Source: Aschbacher–Smith A.3.21(a), printed p.55, and the inspection in
E.6.18, printed p.252 (PDF p.263).
-/

public section
open scoped MatrixGroups
open Subgroup
namespace Matrix.PSL3.OddInvolutionFixed
variable {F : Type*} [Field F] [Finite F]

private theorem central_cube (x : SL(3,F)) (hx : x ∈ center SL(3,F)) : x ^ 3 = 1 := by
  have hd := (orderOf_dvd_natCard (⟨x,hx⟩ : center SL(3,F))).trans (SL3.card_center_dvd_three F)
  exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp hd)

theorem involution_lift (t : PSL(3,F)) (ht : orderOf t = 2) :
    ∃ x : SL(3,F), orderOf x = 2 ∧ projection F x = t := by
  obtain ⟨x, rfl⟩ := projection_surjective F t
  have ht2 : projection F x ^ 2 = 1 := ht ▸ pow_orderOf_eq_one _
  have hx2 : x ^ 2 ∈ center SL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change projection F (x ^ 2) = 1
    simpa only [map_pow] using ht2
  have hx6 : x ^ 6 = 1 := by
    simpa only [← pow_mul] using central_cube (x ^ 2) hx2
  have he : projection F (x ^ 3) = projection F x := by
    rw [map_pow, pow_succ, ht2, one_mul]
  refine ⟨x ^ 3, orderOf_eq_prime ?_ ?_, he⟩
  · simpa only [← pow_mul] using hx6
  · intro hx
    have h1 : projection F x = 1 := by rw [← he, hx, map_one]
    simp [h1] at ht

/-- Projective commutation with an involution lifts to exact commutation. -/
theorem commutes_of_projective_commutes (t x : SL(3,F)) (ht : t ^ 2 = 1)
    (hx : projection F x * projection F t = projection F t * projection F x) :
    x * t = t * x := by
  let c := x * t * x⁻¹ * t⁻¹
  have hc : c ∈ center SL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change projection F c = 1
    simp only [c, map_mul, map_inv]
    rw [hx, mul_inv_cancel_right, mul_inv_cancel]
  have hct : Commute c t := (mem_center_iff.mp hc t).symm
  have he : c * t = x * t * x⁻¹ := by simp [c, mul_assoc]
  have hc2 : c ^ 2 = 1 := by
    have h := congrArg (fun y : SL(3,F) => y ^ 2) he
    rw [hct.mul_pow, ht, mul_one, ← MulAut.conj_apply, ← map_pow, ht, map_one] at h
    exact h
  have hc1 : c = 1 := by simpa only [pow_succ, hc2, one_mul] using central_cube c hc
  have hconj : x * t * x⁻¹ = t := by rw [← he, hc1, one_mul]
  exact mul_inv_eq_iff_eq_mul.mp hconj

/-- Restrict the canonical projection to the actual element centralizers. -/
@[expose] def centralizerProjection (t : SL(3,F)) :
    centralizer ({t} : Set SL(3,F)) →*
      centralizer ({projection F t} : Set PSL(3,F)) :=
  (projection F).comp (centralizer ({t} : Set SL(3,F))).subtype |>.codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    exact (map_mul (projection F) (x : SL(3,F)) t).symm.trans
      ((congrArg (projection F) (mem_centralizer_singleton_iff.mp x.property)).trans
        (map_mul (projection F) t (x : SL(3,F)))))

theorem centralizerProjection_surjective (t : SL(3,F)) (ht : t ^ 2 = 1) :
    Function.Surjective (centralizerProjection t) := by
  intro y
  obtain ⟨x, hx⟩ := projection_surjective F y.val
  refine ⟨⟨x, mem_centralizer_singleton_iff.mpr ?_⟩, Subtype.ext hx⟩
  apply commutes_of_projective_commutes t x ht
  rw [hx]
  exact mem_centralizer_singleton_iff.mp y.property

/-- The full projective centralizer is a quotient of the actual GL₂ block. -/
theorem exists_gl2_surjective_centralizer (t : PSL(3,F)) (ht : orderOf t = 2)
    (h2 : (2 : F) ≠ 0) :
    ∃ f : GL (Fin 2) F →* centralizer ({t} : Set PSL(3,F)), Function.Surjective f := by
  obtain ⟨x, hx, rfl⟩ := involution_lift t ht
  let e := SL3.involutionCentralizerEquiv F x hx h2
  exact ⟨(centralizerProjection x).comp e.symm.toMonoidHom,
    (centralizerProjection_surjective x (hx ▸ pow_orderOf_eq_one x)).comp e.symm.surjective⟩

/-- Every inner involution has a derived fixed subgroup of three-rank at most one. -/
theorem inner_fixed_derived_three_rank [IsSimpleGroup PSL(3,F)]
    (hns : ¬ Group.IsSolvable PSL(3,F)) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hF : Nat.card F = p)
    (a : MulAut PSL(3,F)) (ha : orderOf a = 2)
    (hi : a ∈ MulAut.innerSubgroup PSL(3,F)) :
    primeRank 3 (commutator a.fixedSubgroup) ≤ 1 := by
  have h2 : (2 : F) ≠ 0 := by
    let := Fintype.ofFinite F
    intro hz
    have hc : ringChar F = 2 := CharP.ringChar_of_prime_eq_zero Nat.prime_two hz
    have he := FiniteField.even_card_iff_char_two.mp hc
    rw [← Nat.card_eq_fintype_card, hF] at he
    have hodd := Nat.odd_iff.mp ho
    omega
  have hc : center PSL(3,F) = ⊥ := by
    rcases (inferInstance : (center PSL(3,F)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hns (Group.isSolvable_of_comm (center_eq_top_iff.mp h).is_comm.comm)).elim
  obtain ⟨t, rfl⟩ := hi
  have ht : orderOf t = 2 :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hc) t).symm.trans ha
  obtain ⟨f, hf⟩ := exists_gl2_surjective_centralizer t ht h2
  rw [MulAut.fixedSubgroup_conj]
  exact derived_rank_of_gl2_surjective hp ho hp3 hF f hf

end Matrix.PSL3.OddInvolutionFixed
