module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.InvariantProjection
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.NaturalSection
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ActionGeneration

/-!
# Model reduction for 15.3.49(k)–(l)

The terminal inner-projection argument proves `Y₀ ≤ ⟨L^T⟩` once the
Borel/outer-automorphism analysis supplies the inner action. The actual
natural-section calculation supplies the projected-seed contradiction
once the larger-field case has been reduced to SL₂ and its natural module.
Both results keep the two-core and quotient conventions explicit.
The cubic element is derived from theta and component generation. Once the
closure is identified with the component, relative normality is derived and
the earlier best offender gives `L = [L,U_γ]`.

Still required are the Borel/outer-automorphism inputs, the normalizer
three-rank reduction and natural-module identification, and the exact
binary component and minimal-parabolic alternatives, including `L₀ = L`.
The present conditional results do not assert the completed source (k)–(l).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1143–1144.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
variable {G : Type*} [Group G]

/-- Component generation forces an order-three element in the actual `Y₀` image. -/
lemma exists_star_cubic_of_component_action
    (H M L Y0 : Subgroup G) (hLH : L ≤ H)
    (hθ : theta (M ⊓ H) = Y0) (hcomm : L = ⁅L, Y0⁆)
    (hne : starImage H L ≠ ⊥) : ∃ y : starImage H Y0, orderOf y = 3 := by
  have hYH : Y0 ≤ H := ((hθ ▸ theta_le (M ⊓ H))).trans inf_le_right
  let f := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hYH)
  have hf : f.range = starImage H Y0 := by
    rw [MonoidHom.range_comp]
    have hi : (inclusion hYH).range = Y0.subgroupOf H := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hi]
    rfl
  have hYθ : theta Y0 = Y0 := by rw [← hθ, theta_idempotent]
  have hθs : theta (starImage H Y0) = starImage H Y0 :=
    hf ▸ theta_range_eq_self Y0 hYθ f
  have hYs : starImage H Y0 ≠ ⊥ := by
    intro hb
    have he : starImage H L = ⁅starImage H L, starImage H Y0⁆ := by
      rw [← starImage_commutator H L Y0 hLH hYH, ← hcomm]
    rw [hb, commutator_bot_right] at he
    exact hne he
  obtain ⟨y, hy, hy3⟩ := exists_cubic_of_theta _ hθs hYs
  exact ⟨⟨y, hy⟩, (Subgroup.orderOf_coe ⟨y, hy⟩).symm.trans hy3⟩

/-- Derive the normality needed by the offender-generation theorem after (k)–(l). -/
lemma commutator_eq_after_closure_identification [Finite G]
    (H L Y0 T ZS Z A : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hgen : H = reducedOvergroup L Y0 T)
    (hcomm : L = ⁅L, Y0⁆) (hTY : T ≤ normalizer (Y0 : Set G))
    (hYL0 : Y0 ≤ localSpan L T) (hclosed : localSpan L T = L)
    (hT : IsPGroup 2 T) (hAH : A ≤ H)
    (hL : (L.subgroupOf H).IsCComponent)
    (hquasi : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hA : IsBestOffender action.representation (starImage H A)) : L = ⁅L, A⁆ := by
  have hLH : L ≤ H := hgen ▸ (le_conjugateSpanBy L T).trans le_sup_left
  have hnorm := componentClosure_normal_in_replacement L Y0 T
    (le_normalizer_iff_commutator_le_left.mpr hcomm.ge) hTY
  rw [← hgen, hclosed] at hnorm
  have hn : H ≤ normalizer (L : Set G) := (normal_subgroupOf_iff_le_normalizer hLH).mp hnorm
  have hgen' : H = L ⊔ (Y0 ⊔ T) := by simpa only [reducedOvergroup, hclosed] using hgen
  exact commutator_eq_of_reduced_bestOffender H L Y0 T ZS Z A action hgen'
    (hclosed ▸ hYL0) hn hT hAH hL hquasi hA

/-- The larger-field terminal contradiction, deriving the cubic actor from (i) and (b). -/
lemma no_natural_section_of_component_action
    {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (H M ZS Z L Y0 : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hZSH : ZS ≤ H) (hLH : L ≤ H) (hHL : H ≤ normalizer (L : Set G))
    (hθ : theta (M ⊓ H) = Y0) (hcomm : L = ⁅L, Y0⁆)
    (hne : starImage H L ≠ ⊥)
    (D : Submodule (ZMod 2) (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H))))
    (hsplit : D ⊔ fixedSpace action.representation ⊤ = ⊤)
    (sectionModel : Representation.SL2CubicFixedSection.NaturalComponentSection
      (F := F) action.representation (starImage H L) D)
    (hYL : Y0 ≤ L)
    (hB : ∀ y : starImage H Y0,
      sectionModel.model ⟨y, (map_mono (comap_mono hYL)) y.property⟩ ∈
        Matrix.SpecialLinearGroup.rankOneBorel F)
    (hcent : Y0 ≤ centralizer (ZS : Set G)) : False :=
  hne (starImage_eq_bot_of_natural_section H ZS Z L Y0 action hZSH hLH hHL D hsplit
    sectionModel hYL (exists_star_cubic_of_component_action H M L Y0 hLH hθ hcomm hne) hB hcent)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
