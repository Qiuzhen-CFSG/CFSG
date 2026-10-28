module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# Flag and local generation consequences

The source flag-normalizer bound forces V₃<U_H because H lies outside M.
Together with noncentral generation and the index-two flag, this proves
V₃=V∩U_H and V<U_L. Mutual normalization and abelianness of the endpoint
actor give an actual quadratic conjugation action on each relevant section.
Finally, normal generation across a proper edge forces U_H outside the
endpoint two-core, hence D_H<U_H through the genuine F.9 kernel identity.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemmas
13.8.4(5)–(7) and 13.8.11, printed pp.947 and 950. Permutation-module
recognition, geometric rank comparison and the component calculation
remain separate inputs to the full source assembly.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G]

theorem seed_lt_UH (H G₁ M V₃ : Subgroup G) (hHG : H ≤ G₁)
    (hHM : ¬ H ≤ M) (hflag : G₁ ⊓ normalizer (V₃ : Set G) ≤ M) :
    V₃ < Source.UH H V₃ := by
  refine lt_of_le_of_ne (le_conjugateSpanBy V₃ H) ?_
  intro heq
  apply hHM
  apply le_trans (le_inf hHG ?_) hflag
  rw [heq]
  exact le_normalizer_conjugateSpanBy V₃ H

theorem flag_intersection_and_strict_span
    (L H G₁ M V V₃ : Subgroup G) (hHG : H ≤ G₁)
    (hHM : ¬ H ≤ M) (hflag : G₁ ⊓ normalizer (V₃ : Set G) ≤ M)
    (hV₃V : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hV : V = conjugateSpanBy V₃ L) :
    V₃ = V ⊓ Source.UH H V₃ ∧ V₃ < Source.UH H V₃ ∧ V < Source.UL L H V₃ := by
  have hi := flag_intersection_of_index_two V V₃ (Source.UH H V₃)
    (le_inf hV₃V (le_conjugateSpanBy V₃ H)) hindex
    (seed_not_le_UH_of_noncentral H V V₃ hnoncentral)
  have hp := seed_lt_UH H G₁ M V₃ hHG hHM hflag
  exact ⟨hi, hp, seed_lt_UL_of_flag_intersection L H V V₃ hV hi hp⟩

theorem quadratic_on_section_of_abelian_actor
    (A B Z : Subgroup G) (hAB : A ≤ normalizer (B : Set G))
    (hBA : B ≤ normalizer (A : Set G)) (hBZ : B ≤ normalizer (Z : Set G))
    (hN : (Z.subgroupOf A).Normal) (hB : IsMulCommutative B) :
    let _ := hN
    ∃ action : B →* MulAut (A ⧸ Z.subgroupOf A),
      (∀ b : B, ∀ a : A,
        action b (QuotientGroup.mk' (Z.subgroupOf A) a) =
          QuotientGroup.mk' (Z.subgroupOf A)
            ⟨(b : G) * (a : G) * (b : G)⁻¹,
              (mem_normalizer_iff.mp (hBA b.property) a).mp a.property⟩) ∧
      commutatorAction₂ action.range (A ⧸ Z.subgroupOf A) = ⊥ := by
  let _ := hN
  obtain ⟨action, hact⟩ := exists_quotient_conjugation_action B A Z hBA hBZ hN
  refine ⟨action, hact, ?_⟩
  have hdouble : ⁅⁅A, B⁆, B⁆ ≤ Z :=
    (quadratic_of_normalizes_abelian A B hAB hB).le.trans bot_le
  have hh := quotient_conjugation_quadratic_of_double_commutator_le
    B A Z B hBA le_rfl hN hdouble action hact
  have hactors : (B.subgroupOf B).map action = action.range := by
    rw [subgroupOf_self, ← MonoidHom.range_eq_map]
  exact (congrArg (fun D : Subgroup (MulAut (A ⧸ Z.subgroupOf A)) =>
    commutatorAction₂ D (A ⧸ Z.subgroupOf A)) hactors).symm.trans hh

/-- A generating seed cannot lie in a normal subgroup contained in the proper edge. -/
theorem seed_not_le_normal_of_generation
    (J E Q F : Subgroup G)
    (hJQ : J ≤ normalizer (Q : Set G)) (hQE : Q ≤ E)
    (hEJ : E < J) (hgen : J = conjugateSpanBy F J ⊔ E) : ¬ F ≤ Q := by
  intro hFQ
  have hJE : J ≤ E := by
    rw [hgen]
    exact sup_le ((conjugateSpanBy_le hFQ hJQ).trans hQE) le_rfl
  exact hEJ.not_ge hJE

/-- Generation and the F.9 kernel identity force the strict denominator
required for the rank deductions in 13.8.11. -/
theorem DH_lt_of_generation
    (J E Q UH Uγ A₁ : Subgroup G)
    (hJQ : J ≤ normalizer (Q : Set G)) (hQE : Q ≤ E)
    (hEJ : E < J) (hgen : J = conjugateSpanBy UH J ⊔ E)
    (hD : Source.DH UH Uγ A₁ = UH ⊓ Q) : Source.DH UH Uγ A₁ < UH := by
  have hn := seed_not_le_normal_of_generation J E Q UH hJQ hQE hEJ hgen
  refine lt_of_le_of_ne (commutatorPreimage_le _ _ _) ?_
  intro heq
  apply hn
  exact heq.symm.le.trans (hD.le.trans inf_le_right)

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry

end
