module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.MarkedScalars
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.Residual
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Centralization of the original line by its perfect residual

The existing scalar-character calculation makes the marked line-stabilizer
residual fix its field line. Under the original projection, the commutator
of L₁ with V₁ therefore lies in C_V(L). This kernel centralizes L₁, and
perfectness removes the second commutator. Thus L₁ centralizes the entire
original V₁, including a possible nonzero central kernel.

The application removes this premise from both literal 11.2.3 conclusions.
The preceding radical-centralization identity remains with the normalizer
source assembly owner qt-d-1222-natural-normalizer-source. Sylow-normalizer
containment remains with qt-d-1222-natural-line-action, and the parent also
supplies the radical-normalizer alternative.

Source: Aschbacher--Smith, the opening of 11.1 and 11.2.3, pp.760--761,768--769.
-/

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped commutatorElement
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c)

/-- The literal first residual centralizes the full first flag subgroup. -/
theorem chosen_first_centralizes_line : f.Li 0 ≤ centralizer (f.Vi 0 : Set G) := by
  let : Group.IsPerfect (f.Li 0) := localResidual_perfect _
  have hAL : f.Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  have hcomm : ⁅f.Li 0,f.Vi 0⁆ ≤ centralizer (L : Set G) := by
    rw [commutator_le]
    intro a ha u hu
    let l : L := ⟨a,hAL ha⟩
    let v : V := ⟨u,D.centralQuotientPreimage_le _ hu⟩
    have hv : (c.projection v).toAdd ∈ f.space 0 := (c.mem_preimage _ v).mp hu
    have hqfix : c.modelAction (c.quotientMap l) (c.projection v).toAdd =
        (c.projection v).toAdd := by
      by_cases hz : (c.projection v).toAdd = 0
      · rw [hz,map_zero]
      have h := Closure.Nonabelian.PointModels.model_residual_fixes_line c (f.space 0)
        (f.dimension 0) (c.projection v).toAdd hv hz (c.residualProjection (f.space 0) ⟨a,ha⟩)
      rw [c.residualProjection_coe] at h
      exact h
    let w := V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹
    have hproj : c.projection (V.normalizerMonoidHom (inclusion D.normalizes l) v) =
        c.projection v :=
      congrArg Multiplicative.ofAdd ((c.projection_component_conjugation l v).trans hqfix)
    have hw : c.projection w = 1 := by
      dsimp only [w]
      rw [map_mul,map_inv,hproj,mul_inv_cancel]
    have hcent := (c.projection_eq_one_iff w).mp hw
    exact hcent
  have hiter : ⁅⁅f.Vi 0,f.Li 0⁆,f.Li 0⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [commutator_comm (f.Vi 0) (f.Li 0)]
    exact hcomm.trans (Subgroup.centralizer_le hAL)
  have hh := commutator_eq_bot_of_iterated_eq_bot (f.Vi 0) (f.Li 0) hiter
  rw [commutator_comm] at hh
  exact commutator_eq_bot_iff_le_centralizer.mp hh

/-- Both original clauses, retaining only radical centralization and the two source normalizer inputs. -/
theorem chosen_source_11_2_3_of_radical_centralization
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hfixR : f.Ri 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :=
  chosen_source_11_2_3_of_marked_line D S f hX
    (chosen_first_centralizes_line f) hfixR hNT hradical
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
