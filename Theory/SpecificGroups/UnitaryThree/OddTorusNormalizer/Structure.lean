module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Frames
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.PermutationAction
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.NormalizerAction
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.InvolutionCalculus

/-!
# Concrete structure of orthogonal-frame tori in SU₃ and PSU₃

The actual frame tori have cyclic product structures `C_(q+1) × C_(q+1)`
and `C_(q+1) × C_((q+1)/gcd(3,q+1))`. The projective scalar kernel is
computed explicitly. The full normalizers are the actual stabilizer of the
three frame lines and its projective image, and their relative quotients by
the tori are S₃.

Since the tori have odd order, every normalizer involution induces a
transposition. The coordinate calculation then gives fixed-subgroup order
`(q+1)/d` and the actual ambient commutator isomorphic to `C_(q+1)`.
The action hypotheses of the separate calculation are discharged here.
All conclusions refer to the same supplied frame and literal matrix groups,
including the full projective scalar kernel.

Source: GLS4, Chapter 4, Lemma 3.11(b,c),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603, and the fixed-subgroup
calculation used in Chapter 2, Lemma 17.4,
`refs/KGroup/GLS4/Chapter2.tex`, lines 3136–3147. Placement of an arbitrary
odd subgroup in a suitable frame, clause (a), remains with the parent theorem.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups

namespace UnitaryThree.OddTorusNormalizer

variable {E : Type*} [Field E] [Finite E]
variable (J : HermitianForm 3 E) (P : OrthogonalFrame J) (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
include hn hcard hfixed

/-- Every involution of the actual special normalizer fixes exactly `q+1`
elements of the frame torus. This discharges the fixed-order premise of
`special_constraints_of_frame_data`. -/
theorem specialFrameTorus_centralizer_card
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htN : t ∈ normalizer (specialFrameTorus J P)) :
    Nat.card ↥(specialFrameTorus J P ⊓ centralizer {t}) = 2 ^ n + 1 := by
  obtain ⟨σ, hσ, ha⟩ := specialFrameNormalizer_involution_action J P n hn hcard hfixed
    ⟨t, htN⟩ (by simpa only [Subgroup.orderOf_mk] using ht)
  exact specialFrameTorus_involution_centralizer_card J P (2 ^ n) hcard hfixed t σ hσ ha

/-- In the literal projective torus the fixed subgroup retains the cubic
scalar quotient. This discharges the fixed-order premise of
`projective_constraints_of_frame_data`. -/
theorem projectiveFrameTorus_centralizer_card
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (htN : t ∈ normalizer (projectiveFrameTorus J P)) :
    Nat.card ↥(projectiveFrameTorus J P ⊓ centralizer {t}) =
      (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) := by
  obtain ⟨σ, hσ, ha⟩ := projectiveFrameNormalizer_involution_action J P n hn hcard hfixed
    ⟨t, htN⟩ (by simpa only [Subgroup.orderOf_mk] using ht)
  exact projectiveFrameTorus_involution_centralizer_card J P (2 ^ n) hcard hfixed t σ hσ ha

/-- The actual subgroup commutator with a special normalizer involution is
cyclic of order `q+1`, as in GLS4, Chapter 4, Lemma 3.11(c). -/
noncomputable def specialFrameTorus_commutatorEquiv
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htN : t ∈ normalizer (specialFrameTorus J P)) :
    ↥⁅specialFrameTorus J P, zpowers t⁆ ≃* Multiplicative (ZMod (2 ^ n + 1)) := by
  let h := specialFrameNormalizer_involution_action J P n hn hcard hfixed
    ⟨t, htN⟩ (by simpa only [Subgroup.orderOf_mk] using ht)
  exact specialFrameTorus_involution_commutatorEquiv J P (2 ^ n) hcard hfixed t ht
    h.choose h.choose_spec.1 h.choose_spec.2

/-- The commutator's anti-diagonal factor embeds through the projective
quotient, so its order remains `q+1`. -/
noncomputable def projectiveFrameTorus_commutatorEquiv
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (htN : t ∈ normalizer (projectiveFrameTorus J P)) :
    ↥⁅projectiveFrameTorus J P, zpowers t⁆ ≃* Multiplicative (ZMod (2 ^ n + 1)) := by
  let h := projectiveFrameNormalizer_involution_action J P n hn hcard hfixed
    ⟨t, htN⟩ (by simpa only [Subgroup.orderOf_mk] using ht)
  exact projectiveFrameTorus_involution_commutatorEquiv J P (2 ^ n) hcard hfixed t ht
    h.choose h.choose_spec.1 h.choose_spec.2

/-- The special commutator order used in GLS4, Chapter 2, Lemma 17.4. -/
theorem specialFrameTorus_commutator_card
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htN : t ∈ normalizer (specialFrameTorus J P)) :
    Nat.card ↥⁅specialFrameTorus J P, zpowers t⁆ = 2 ^ n + 1 := by
  rw [Nat.card_congr
    (specialFrameTorus_commutatorEquiv J P n hn hcard hfixed t ht htN).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- The projective commutator has the same order, without dividing by the
scalar kernel. -/
theorem projectiveFrameTorus_commutator_card
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (htN : t ∈ normalizer (projectiveFrameTorus J P)) :
    Nat.card ↥⁅projectiveFrameTorus J P, zpowers t⁆ = 2 ^ n + 1 := by
  rw [Nat.card_congr
    (projectiveFrameTorus_commutatorEquiv J P n hn hcard hfixed t ht htN).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- All torus structure conclusions for the supplied special frame, with no
action or structural premises. The quotient uses normality in `N(F)`. -/
theorem specialFrameTorus_structure :
    normalizer (specialFrameTorus J P) = specialFrameMonomial J P ∧
    Nonempty (specialFrameTorus J P ≃*
      Multiplicative (ZMod (2 ^ n + 1)) × Multiplicative (ZMod (2 ^ n + 1))) ∧
    Nonempty ((normalizer (specialFrameTorus J P) ⧸
      (specialFrameTorus J P).subgroupOf (normalizer (specialFrameTorus J P))) ≃*
        Equiv.Perm (Fin 3)) ∧
    ∀ t : J.specialSubgroup, orderOf t = 2 →
      t ∈ normalizer (specialFrameTorus J P) →
      Nat.card ↥(specialFrameTorus J P ⊓ centralizer {t}) = 2 ^ n + 1 ∧
      Nonempty (↥⁅specialFrameTorus J P, zpowers t⁆ ≃*
        Multiplicative (ZMod (2 ^ n + 1))) := by
  have hq : 2 ≤ 2 ^ n :=
    (by decide : 2 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by decide) hn)
  refine ⟨specialFrameTorus_normalizer_eq_monomial J P (2 ^ n) hq hcard hfixed,
    ⟨specialFrameTorusEquivCyclic J P (2 ^ n) hcard hfixed⟩,
    ⟨specialFrameNormalizerEquivPerm J P n hn hcard hfixed⟩, ?_⟩
  intro t ht htN
  exact ⟨specialFrameTorus_centralizer_card J P n hn hcard hfixed t ht htN,
    ⟨specialFrameTorus_commutatorEquiv J P n hn hcard hfixed t ht htN⟩⟩

/-- All torus structure conclusions for the literal projective image of the
supplied frame, retaining the exact scalar divisor `gcd(3,q+1)`. -/
theorem projectiveFrameTorus_structure :
    normalizer (projectiveFrameTorus J P) = projectiveFrameMonomial J P ∧
    Nonempty (projectiveFrameTorus J P ≃*
      Multiplicative (ZMod (2 ^ n + 1)) ×
        Multiplicative (ZMod ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)))) ∧
    Nonempty ((normalizer (projectiveFrameTorus J P) ⧸
      (projectiveFrameTorus J P).subgroupOf (normalizer (projectiveFrameTorus J P))) ≃*
        Equiv.Perm (Fin 3)) ∧
    ∀ t : ProjectiveSpecialUnitaryMatrixGroup J, orderOf t = 2 →
      t ∈ normalizer (projectiveFrameTorus J P) →
      Nat.card ↥(projectiveFrameTorus J P ⊓ centralizer {t}) =
        (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) ∧
      Nonempty (↥⁅projectiveFrameTorus J P, zpowers t⁆ ≃*
        Multiplicative (ZMod (2 ^ n + 1))) := by
  have hq : 2 ≤ 2 ^ n :=
    (by decide : 2 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by decide) hn)
  refine ⟨projectiveFrameTorus_normalizer_eq_monomial J P (2 ^ n) hq hcard hfixed,
    ⟨projectiveFrameTorusEquivCyclic J P (2 ^ n) hcard hfixed⟩,
    ⟨projectiveFrameNormalizerEquivPerm J P n hn hcard hfixed⟩, ?_⟩
  intro t ht htN
  exact ⟨projectiveFrameTorus_centralizer_card J P n hn hcard hfixed t ht htN,
    ⟨projectiveFrameTorus_commutatorEquiv J P n hn hcard hfixed t ht htN⟩⟩

end UnitaryThree.OddTorusNormalizer
