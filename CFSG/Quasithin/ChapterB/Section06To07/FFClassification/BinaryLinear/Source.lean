module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.BinaryLinear.Ambient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource
/-!
# Original quasisimple B.5.1 binary-linear rows are excluded

The actual generalized Fitting subgroup of the normal offender supplement
embeds as the two-residual. Its literal SL4(2) or SL5(2) marking therefore
contradicts minimal parabolicity by the intrinsic invariant flag pair. Apply
this to the group markings retained by the natural, repeated-natural,
natural-plus-dual and exterior-five rows, on the original moved space and
central quotient. The final theorem applies to the actual offender group and
B.5.1 section; no arbitrary quotient descent or module-centralizer assumption
is inserted.

Source: Aschbacher–Smith B.5.1 and the proof of B.6.9, pp.99–103 and 116.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

theorem source_quasisimple_binary_linear_excluded
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    {n : ℕ} (hn : n=4 ∨ n=5) (e : generalizedFitting Y ≃* SL(n,ZMod 2)) : False := by
  have he := (source_quasisimple_fitting_eq_residual T hP Y hgen hq).1
  let L := (generalizedFitting Y).map Y.subtype
  have hL : L = pResidual 2 G := he
  let : L.Normal := hL ▸ (inferInstance : (pResidual 2 G).Normal)
  let eL : L ≃* SL(n,ZMod 2) :=
    ((generalizedFitting Y).equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e
  have hg : L ⊔ (T : Subgroup G) = ⊤ := by rw [hL]; exact pResidual_sup_sylow_eq_top T
  exact not_minimalParabolic_of_binary_linear_supplement T L hn eL hg hP

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem source_quasisimple_binary_natural_excluded
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    {n : ℕ} (hn : n=4 ∨ n=5)
    (h : IsLinearNatural (s.action.comp (generalizedFitting Y).subtype) BinaryField.two n) : False := by
  obtain ⟨c⟩ := h
  exact source_quasisimple_binary_linear_excluded T hP Y hgen hq hn c.groupEquiv

theorem source_quasisimple_binary_repeated_excluded
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    {n : ℕ} (hn : n=4 ∨ n=5) (r : ℕ)
    (h : IsRepeatedLinearNatural (s.space.toRepresentation.comp (generalizedFitting Y).subtype)
      BinaryField.two n r) : False := by
  obtain ⟨c⟩ := h
  exact source_quasisimple_binary_linear_excluded T hP Y hgen hq hn c.groupEquiv

theorem source_quasisimple_binary_naturalDual_excluded
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (s : MovedSection (ρ.comp Y.subtype) (generalizedFitting Y))
    {n : ℕ} (hn : n=4 ∨ n=5)
    (h : IsNaturalPlusDual (s.space.toRepresentation.comp (generalizedFitting Y).subtype) n) : False := by
  obtain ⟨c⟩ := h
  exact source_quasisimple_binary_linear_excluded T hP Y hgen hq hn c.groupEquiv

/-- The literal exterior-five source row carries this group marking. -/
theorem source_quasisimple_exteriorFive_excluded
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y : Subgroup G) [Y.Normal] (hgen : Y ⊔ (T : Subgroup G) = ⊤)
    (hq : IsQuasisimple (generalizedFitting Y))
    (e : generalizedFitting Y ≃* SL(5,ZMod 2)) : False :=
  source_quasisimple_binary_linear_excluded T hP Y hgen hq (Or.inr rfl) e

/-- Applied to the actual offender supplement, no SL4(2) or SL5(2) actor remains. -/
theorem source_offender_quasisimple_not_binary_linear [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    {n : ℕ} (hn : n=4 ∨ n=5) :
    ¬ Nonempty (generalizedFitting (offenderSubgroup ρ) ≃* SL(n,ZMod 2)) := by
  rintro ⟨e⟩
  let := offenderSubgroup_normal ρ
  exact source_quasisimple_binary_linear_excluded T hP _
    (offender_generation T hP ρ hff hcore).2 hq hn e
/-- All four binary higher-linear rows are excluded on the literal B.5.1 section. -/
theorem source_offender_quasisimple_binary_rows_excluded [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    (∀ n, (n=4 ∨ n=5) → ¬ IsLinearNatural
      (c.sectionData.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype) BinaryField.two n) ∧
    (∀ n r, (n=4 ∨ n=5) → ¬ IsRepeatedLinearNatural
      (c.sectionData.space.toRepresentation.comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      BinaryField.two n r) ∧
    (∀ n, (n=4 ∨ n=5) → ¬ IsNaturalPlusDual
      (c.sectionData.space.toRepresentation.comp (generalizedFitting (offenderSubgroup ρ)).subtype) n) ∧
    ¬ Nonempty (generalizedFitting (offenderSubgroup ρ) ≃* SL(5,ZMod 2)) := by
  have he (n : ℕ) (hn : n=4 ∨ n=5) :=
    source_offender_quasisimple_not_binary_linear ρ T hP hff hcore hq hn
  refine ⟨?_,?_,?_,he 5 (Or.inr rfl)⟩
  · rintro n hn ⟨a⟩
    exact he n hn ⟨a.groupEquiv⟩
  · rintro n r hn ⟨a⟩
    exact he n hn ⟨a.groupEquiv⟩
  · rintro n hn ⟨a⟩
    exact he n hn ⟨a.groupEquiv⟩
end CFSG.Quasithin.ChapterB
