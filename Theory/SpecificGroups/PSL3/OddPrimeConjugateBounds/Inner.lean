module

public import Theory.SpecificGroups.PSL3.OddPrimeConjugateBounds.Defs
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Theory.SpecificGroups.PSL3.OddPrimeConjugateBounds.Inner.Generators

/-!
# Three inner conjugates of an involution generate PSL₃(p)

The explicit three-involution calculation in `Inner.Generators` generates
SL₃ over every odd prime field. All its involutions are conjugate inside
SL₃, so the same generation bound holds for any prescribed involution.
An involution in the projective quotient lifts to an involution upstairs;
mapping the three conjugators down gives actual PSL₃ conjugators. Finally,
the conjugation homomorphism gives the required inner-automorphism cover.
The inherited simplicity and nonsolvability hypotheses are used only to
identify an inner involutory automorphism with a projective involution.

This proves `InnerThreeBound`, the inner model premise consumed by the
odd-prime actor-bound assembly. Source: Guralnick–Malle, *Classification of
2F-modules I*, (2.6) and Proposition 4.2, manuscript pp.4 and 9–10, and
Aschbacher–Smith K.2, p.453. The uniform odd-prime assertion is an auxiliary
extension of the explicit three-conjugate count at p = 3 in GM02.
-/

public section

open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.OddPrimeConjugateBounds
variable {F : Type*} [Field F] [Finite F]

/-- Three conjugates inside SL₃ of any involution generate the whole group. -/
theorem sl_three_conjugates_generate {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p) (h2 : (2 : F) ≠ 0)
    (t : SL(3,F)) (ht : orderOf t = 2) :
    ∃ c : Fin 3 → SL(3,F), closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤ := by
  obtain ⟨s, hs, hg⟩ := InnerGenerators.exists_generating_involutions F hp hF h2
  have hc (i : Fin 3) : ∃ x : SL(3,F), x * t * x⁻¹ = s i :=
    isConj_iff.mp (SL3.involutions_isConj F t (s i) ht (hs i) h2)
  choose c hc using hc
  refine ⟨c, ?_⟩
  simpa only [hc] using hg

/-- The conjugators lie in the literal projective matrix group. -/
theorem psl_three_conjugates_generate {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p) (h2 : (2 : F) ≠ 0)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    ∃ c : Fin 3 → PSL(3,F), closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤ := by
  obtain ⟨x, hx, rfl⟩ := OddInvolutionFixed.involution_lift t ht
  obtain ⟨c, hc⟩ := sl_three_conjugates_generate hp hF h2 x hx
  refine ⟨fun i => projection F (c i), ?_⟩
  have he := congrArg (Subgroup.map (projection F)) hc
  rw [MonoidHom.map_closure, ← Set.range_comp,
    Subgroup.map_top_of_surjective _ (projection_surjective F)] at he
  simpa only [Function.comp_def, map_mul, map_inv] using he

universe u
/-- The inner branch of the uniform odd-prime three-conjugate bound. -/
theorem inner_three_bound : InnerThreeBound.{u} := by
  intro F _ _ _ hns p hp ho hF a ha ha2 hi
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
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hc) t).symm.trans
      (orderOf_eq_prime ha2 ha)
  obtain ⟨c, hgen⟩ := psl_three_conjugates_generate hp hF h2 t ht
  refine ⟨c, ?_⟩
  have he := congrArg (Subgroup.map (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F))) hgen
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map] at he
  simpa only [Function.comp_def, map_mul, map_inv] using he.ge

end Matrix.PSL3.OddPrimeConjugateBounds
