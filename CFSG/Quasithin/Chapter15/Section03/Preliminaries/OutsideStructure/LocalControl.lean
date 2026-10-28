module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.SylowConclusion
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Normalizer and centralizer steps for the two choices of Y₊

A subgroup with nontrivial two-core has its normalizer controlled by a
uniqueness subgroup that normalizes it. This applies to Y₊ in the second
choice; the two definite planes use the direct two-group version. Once
Y₊ is identified with O²(Y ∩ I), its normalization by M ∩ I follows
without the later theta calculation.

In the first choice the span equality V=⟨Z^Y⟩ and N_G(Y)=N_G(V)=M
immediately give (2) and (4). Nontrivial action on a plane persists in
U_I. The action and residual-intersection calculations in the second
choice are still required, and are not asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(2)–(4),(9), pp.1123–1124.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
variable {G : Type*} [Group G] [Finite G]

/-- Normalizer control uses the nontrivial two-core, rather than wrongly
assuming that the normalizer of an arbitrary subgroup is two-local. -/
theorem normalizer_le_of_unique_and_core (J M W : Subgroup G)
    (hu : Chapter4.UniqueMaximalOvergroup J M)
    (hn : J ≤ normalizer (W : Set G)) (hne : W.pCoreIn 2 ≠ ⊥) :
    normalizer (W : Set G) ≤ M := by
  have hnorm : normalizer (W : Set G) ≤ normalizer (W.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image W (pCore 2 W)
  exact hnorm.trans (normalizer_le_of_unique_maximalTwoLocal hu.2.2
    (pCore_isPGroup.map W.subtype) hne (hn.trans hnorm))

/-- The normalizer part of (3), once the natural-action calculation supplies
normalization by YS and the nontrivial core of Y₊. -/
theorem normalizers_of_second_choice (Y S M V₁ V₂ Yplus : Subgroup G)
    (hu : Chapter4.UniqueMaximalOvergroup (Y ⊔ S) M)
    (hp₁ : IsPGroup 2 V₁) (hne₁ : V₁ ≠ ⊥)
    (hp₂ : IsPGroup 2 V₂) (hne₂ : V₂ ≠ ⊥)
    (hn₁ : Y ⊔ S ≤ normalizer (V₁ : Set G))
    (hn₂ : Y ⊔ S ≤ normalizer (V₂ : Set G))
    (hnplus : Y ⊔ S ≤ normalizer (Yplus : Set G))
    (hcore : Yplus.pCoreIn 2 ≠ ⊥) :
    normalizer (V₁ : Set G) ≤ M ∧ normalizer (V₂ : Set G) ≤ M ∧
      normalizer (Yplus : Set G) ≤ M := by
  exact ⟨normalizer_le_of_unique_maximalTwoLocal hu.2.2 hp₁ hne₁ hn₁,
    normalizer_le_of_unique_maximalTwoLocal hu.2.2 hp₂ hne₂ hn₂,
    normalizer_le_of_unique_and_core (Y ⊔ S) M Yplus hu hnplus hcore⟩

/-- Clause (4) in the residual branch, without using the later theta identity. -/
theorem normalizer_in_eq_of_intersection_residual (Yplus Y M I : Subgroup G)
    (hMY : M ≤ normalizer (Y : Set G))
    (hres : Yplus = twoResidualAmbient (Y ⊓ I))
    (hcontrol : normalizer (Yplus : Set G) ≤ M) :
    I ⊓ normalizer (Yplus : Set G) = M ⊓ I := by
  apply le_antisymm (fun _ hx => ⟨hcontrol hx.2, hx.1⟩)
  have hn := intersection_le_normalizer_residual M Y I hMY
  rw [← hres] at hn
  exact le_inf inf_le_right hn

omit [Finite G] in
/-- Clauses (2) and (4) in the first choice of Hypothesis 15.3.10.
The span identity is proved in 15.3.7 and N_G(V)=M is the standing choice. -/
theorem first_choice_centralizer_normalizer (Z Y S M I V : Subgroup G)
    (hI : I ∈ outsideFamily Y S M)
    (hspan : localSpan Z Y = V)
    (hV : normalizer (V : Set G) = M)
    (hY : normalizer (Y : Set G) = M) :
    I ⊓ centralizer (localSpan Z I : Set G) ≤ M ⊓ I ∧
      I ⊓ normalizer (Y : Set G) = M ⊓ I := by
  refine ⟨centralizer_localSpan_le_intersection Z Y I M V
    (le_sup_left.trans hI.1.2) hspan.ge hV.le, ?_⟩
  rw [hY, inf_comm]

omit [Finite G] in
/-- Nontrivial action on the included plane remains nontrivial on U_I. -/
theorem not_centralizing_localSpan (Z Yplus I W : Subgroup G)
    (hYI : Yplus ≤ I) (hspan : W ≤ localSpan Z Yplus)
    (hact : ⁅W, Yplus⁆ ≠ ⊥) :
    ¬ Yplus ≤ centralizer (localSpan Z I : Set G) := by
  intro h
  have hW : W ≤ localSpan Z I := hspan.trans (conjugateSpanBy_mono le_rfl hYI)
  exact hact (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (h.trans (centralizer_le hW))))

/-- Both choices preserve two-perfectness. No assertion about the action
of Y₊ follows from this identity alone. -/
theorem choice_residual_eq (M Y S V₁ Yplus : Subgroup G)
    (hchoice : Hypothesis15310 M Y S V₁ Yplus)
    (hY : twoResidualAmbient Y = Y) : twoResidualAmbient Yplus = Yplus := by
  rcases hchoice with rfl | ⟨_, rfl⟩
  · exact hY
  · exact residual_idempotent _

omit [Finite G] in
/-- The subgroup chosen in 15.3.10 is contained in Y in both cases. -/
theorem choice_le (M Y S V₁ Yplus : Subgroup G)
    (hchoice : Hypothesis15310 M Y S V₁ Yplus) : Yplus ≤ Y := by
  rcases hchoice with rfl | ⟨_, rfl⟩
  · exact le_rfl
  · exact (residual_le _).trans inf_le_left

/-- The actual Y is two-perfect by its construction as a two-residual. -/
theorem residualY_residual_eq (M Mc : Subgroup G) :
    twoResidualAmbient (residualY M Mc) = residualY M Mc := by
  let N : Subgroup M := normalClosure (((M ⊓ Mc).pCoreIn 2).subgroupOf M : Set M)
  change twoResidualAmbient ((twoResidualAmbient N).map M.subtype) =
    (twoResidualAmbient N).map M.subtype
  rw [← map_twoResidualAmbient_of_subgroup_image (twoResidualAmbient N) M.subtype _ rfl,
    residual_idempotent]

/-- Two-perfectness of Y₊ follows for both choices of 15.3.10. -/
theorem chosen_residual_eq (M Mc S V₁ Yplus : Subgroup G)
    (hchoice : Hypothesis15310 M (residualY M Mc) S V₁ Yplus) :
    twoResidualAmbient Yplus = Yplus :=
  choice_residual_eq M (residualY M Mc) S V₁ Yplus hchoice (residualY_residual_eq M Mc)


end CFSG.Quasithin.Chapter15.Section03.OutsideStructure

end
