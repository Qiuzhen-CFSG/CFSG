module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.Elementary
public import Theory.GroupTheory.NormalGenerationFixedQuotient
public import Mathlib.GroupTheory.Index

/-!
# Elementary steps in the local analysis of §13.8

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed pp.947–953 (13.8.4–18).

The results here establish subgroup consequences used by the local analysis:
noncentrality excludes containment in the generated three-space, the index-two
flag determines its intersection with V, abelian normalizing actors act
quadratically, and a commutator-generated component lies in a conjugate span.
The rank-one deduction uses actual subgroup indices. In particular its strict
inclusion is `D_H < U_H`, correcting the reversed inequality printed in 13.8.10.

These are partial deductions, not proofs of all of Lemmas 13.8.4–18. The
transvection recognition, compatible module identifications, critical-pair
geometry, solvable exclusion and component reduction remain to be established.
Normality is only used in the named local group, never imposed on subgroups of
the ambient simple group.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08

open Subgroup

variable {G : Type*} [Group G]

/-- The noncentral-action input of 13.8.4(5) forces `V` outside `U_H`:
otherwise all its H-conjugates and their commutators remain in `U_H`. -/
theorem seed_not_le_UH_of_noncentral
    (H V V₃ : Subgroup G)
    (h : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃) :
    ¬ V ≤ Source.UH H V₃ := by
  intro hV
  have hn : H ≤ normalizer (Source.UH H V₃ : Set G) :=
    le_normalizer_conjugateSpanBy V₃ H
  have hVH : Source.VH H V ≤ Source.UH H V₃ :=
    conjugateSpanBy_le hV hn
  exact h ((commutator_mono hVH le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hn))

/-- The intersection argument of 13.8.4(5), retaining the actual index two
of the source flag. A proper intermediate subgroup in an index-two interval
must be its lower endpoint. -/
theorem flag_intersection_of_index_two
    (V V₃ U : Subgroup G) (hV₃ : V₃ ≤ V ⊓ U)
    (hindex : V₃.relIndex V = 2) (hV : ¬ V ≤ U) :
    V₃ = V ⊓ U := by
  have hne : (V ⊓ U).relIndex V ≠ 1 := by
    intro heq
    exact hV ((relIndex_eq_one.mp heq).trans inf_le_right)
  have hdiv : (V ⊓ U).relIndex V ∣ 2 := by
    rw [← hindex]
    exact relIndex_dvd_of_le_left V hV₃
  have htwo : (V ⊓ U).relIndex V = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hdiv |>.resolve_left hne
  have hmul := relIndex_mul_relIndex V₃ (V ⊓ U) V hV₃ inf_le_left
  rw [hindex, htwo] at hmul
  have hone : V₃.relIndex (V ⊓ U) = 1 := by omega
  exact le_antisymm hV₃ (relIndex_eq_one.mp hone)

/-- The strict-span argument of 13.8.4(7). The strictness uses
`V₃ < U_H` as well as the intersection identity. -/
theorem seed_lt_UL_of_flag_intersection
    (L H V V₃ : Subgroup G)
    (hV : V = conjugateSpanBy V₃ L)
    (hinter : V₃ = V ⊓ Source.UH H V₃)
    (hproper : V₃ < Source.UH H V₃) :
    V < Source.UL L H V₃ := by
  have hle : V ≤ Source.UL L H V₃ := by
    rw [hV]
    exact conjugateSpanBy_mono (le_conjugateSpanBy V₃ H) le_rfl
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hUV : Source.UH H V₃ ≤ V := by
    rw [heq]
    exact le_conjugateSpanBy _ _
  exact hproper.ne (hinter.trans (inf_eq_right.mpr hUV))

/-- The commutator calculation behind 13.8.4(6). If B is abelian and A
normalizes B, then `[A,B,B] = 1`; this identity descends to the source sections. -/
theorem quadratic_of_normalizes_abelian
    (A B : Subgroup G) (hn : A ≤ normalizer (B : Set G))
    (hab : IsMulCommutative B) : ⁅⁅A, B⁆, B⁆ = ⊥ := by
  apply le_bot_iff.mp
  exact (commutator_mono (le_normalizer_iff_commutator_le_right.mp hn) le_rfl).trans
    (commutator_self_eq_bot_iff.mpr hab).le

/-- The containment step of 13.8.9(2). The comparison input is the lift
of equality of the two commutator images modulo the source line V₁.
Noncentrality is supplied by the proved argument of 13.8.9(1). -/
theorem noncentral_commutator_supported_on_line
    (F Uγ Vγ V₁ : Subgroup G)
    (hn : F ≤ normalizer (Uγ : Set G))
    (hcomparison : ⁅F, Vγ⁆ ≤ ⁅F, Uγ⁆ ⊔ V₁)
    (hnoncentral : ¬ ⁅F, Vγ⁆ ≤ Uγ) :
    ¬ V₁ ≤ Uγ ∧ ⁅F, Vγ⁆ ≤ Uγ ⊔ V₁ := by
  have hcomm := le_normalizer_iff_commutator_le_right.mp hn
  refine ⟨?_, hcomparison.trans (sup_le_sup_right hcomm V₁)⟩
  intro hline
  exact hnoncentral (hcomparison.trans (sup_le hcomm hline))

/-- The index form of the rank-one deduction in corrected 13.8.10(1).
For the elementary abelian source sections index two means dimension one.
This uses the genuine strict inclusion `D_H < U_H`; the printed reverse
inclusion is incompatible with the definition of `D_H`. -/
theorem corrected_13_8_10_index [Finite G]
    (UH Uγ A₁ V₁ : Subgroup G)
    (hproper : Source.DH UH Uγ A₁ < UH)
    (hcomparison : (Source.DH UH Uγ A₁).relIndex UH ≤
      (Source.Dgamma Uγ UH V₁).relIndex Uγ)
    (hγ : (Source.Dgamma Uγ UH V₁).relIndex Uγ = 2) :
    (Source.DH UH Uγ A₁).relIndex UH = 2 := by
  have hne : (Source.DH UH Uγ A₁).relIndex UH ≠ 1 := by
    intro heq
    exact hproper.not_ge (relIndex_eq_one.mp heq)
  have hpos : (Source.DH UH Uγ A₁).relIndex UH ≠ 0 :=
    ((Source.DH UH Uγ A₁).subgroupOf UH).index_ne_zero_of_finite
  omega

/-- The fixed-hyperplane step in corrected 13.8.10(2). If the source line
does not lie in Uγ, its intersection with Uγ is trivial. The commutator
bound modulo that line then identifies Dγ with the actual fixed subgroup.
Together with the index-two hypothesis this is the common-axis statement
for the elementary abelian source module. -/
theorem corrected_13_8_10_fixed_hyperplane [Finite G]
    (UH Uγ A₁ V₁ : Subgroup G)
    (hproper : Source.DH UH Uγ A₁ < UH)
    (hcomparison : (Source.DH UH Uγ A₁).relIndex UH ≤
      (Source.Dgamma Uγ UH V₁).relIndex Uγ)
    (hγ : (Source.Dgamma Uγ UH V₁).relIndex Uγ = 2)
    (hline : Nat.card V₁ = 2)
    (hn : UH ≤ normalizer (Uγ : Set G))
    (hline_norm : Uγ ≤ normalizer (V₁ : Set G)) :
    (Source.DH UH Uγ A₁).relIndex UH = 2 ∧
      (V₁ ≤ Uγ ∨
        (Uγ ⊓ centralizer (UH : Set G) = Source.Dgamma Uγ UH V₁ ∧
          (Uγ ⊓ centralizer (UH : Set G)).relIndex Uγ = 2)) := by
  refine ⟨corrected_13_8_10_index UH Uγ A₁ V₁ hproper hcomparison hγ, ?_⟩
  by_cases hV₁ : V₁ ≤ Uγ
  · exact Or.inl hV₁
  have hdisjoint : V₁ ⊓ Uγ = ⊥ := by
    have hdvd : Nat.card (V₁ ⊓ Uγ : Subgroup G) ∣ 2 := by
      rw [← hline]
      exact card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
    · exact card_eq_one.mp hone
    · have heq : V₁ ⊓ Uγ = V₁ :=
        eq_of_le_of_card_ge inf_le_left (by rw [hline, htwo])
      exact (hV₁ (heq.symm.le.trans inf_le_right)).elim
  have hfixed : Uγ ⊓ centralizer (UH : Set G) = Source.Dgamma Uγ UH V₁ := by
    apply le_antisymm
    · apply le_commutatorPreimage inf_le_left
      exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le
    · refine le_inf (commutatorPreimage_le _ _ _) ?_
      apply commutator_eq_bot_iff_le_centralizer.mp
      apply le_bot_iff.mp
      rw [← hdisjoint]
      refine le_inf (commutator_commutatorPreimage_le Uγ UH V₁ hline_norm) ?_
      exact (commutator_mono (commutatorPreimage_le Uγ UH V₁) le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hn)
  exact Or.inr ⟨hfixed, hfixed ▸ hγ⟩

/-- The generation step in 13.8.18(1). The source component calculation
supplies `K = [K,F]`, and the edge stabilizer E supplements K in J.
The result uses the actual J-conjugate span of F. -/
theorem generation_of_commutator_component
    (J K E F : Subgroup G) (hJ : J = K ⊔ E) (hF : F ≤ J)
    (hK : K = ⁅K, F⁆) : J = conjugateSpanBy F J ⊔ E := by
  have hKJ : K ≤ J := by rw [hJ]; exact le_sup_left
  have hEJ : E ≤ J := by rw [hJ]; exact le_sup_right
  have hnorm : K ≤ normalizer (conjugateSpanBy F J : Set G) :=
    hKJ.trans (le_normalizer_conjugateSpanBy F J)
  have hspan : K ≤ conjugateSpanBy F J := by
    rw [hK]
    exact (commutator_mono le_rfl (le_conjugateSpanBy F J)).trans
      (le_normalizer_iff_commutator_le_right.mp hnorm)
  apply le_antisymm
  · exact hJ.le.trans (sup_le_sup_right hspan E)
  · exact sup_le (conjugateSpanBy_le_self hF) hEJ

end CFSG.Quasithin.Chapter13.Section08

end
