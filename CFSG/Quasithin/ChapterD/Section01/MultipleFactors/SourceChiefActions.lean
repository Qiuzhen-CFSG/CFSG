module
public import CFSG.Quasithin.ChapterD.Section01.SourceElementary
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions

/-!
# Source chief kernels and ratios on the original qrc span

The actual group chief quotients are irreducible binary modules. Each has
ratio at least one when the second group is solvable, and each noncentral
factor has exact kernel A∩O₂(G₂) on every A in the original Sylow group.
The final theorem constructs elementary span and minimal parabolic directly
from the original non-FF qrc hypotheses, discharging both extra chief-action
inputs of the D.1.3 numerical assembly. Quadratic-actor selection and the
conjugate-generator filtration remain its separate source steps.
Source: Aschbacher–Smith D.1.3, printed pp.173–175.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterD.MultipleFactors
open NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H]
  (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]

theorem source_chief_image_ratio_ge_one
    (s : SeriesOn U) (hs : Group.IsSolvable H) (i : Fin s.series.length) :
    1 ≤ quadraticRatio (imageRepresentation (s.factorRepresentation i)) := by
  let := s.factorRepresentation_irreducible i
  exact ChapterB.solvable_irreducible_image_ratio_ge_one (s.factorRepresentation i) hs

theorem source_chief_sylow_kernel
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (s : SeriesOn U) (i : Fin s.series.length) (hi : ¬ s.Central i)
    (A : Subgroup H) (hAT : A ≤ T) :
    A ⊓ (s.factorRepresentation i).ker = A ⊓ pCore 2 H := by
  let := s.factorRepresentation_irreducible i
  apply ChapterB.minimalParabolic_irreducible_sylow_kernel T hP (s.factorRepresentation i) ?_ A hAT
  by_contra! hn
  apply hi
  rw [s.central_iff_action]
  intro h x
  exact congrArg Additive.toMul (hn h (Additive.ofMul x))
end CFSG.Quasithin.ChapterD.MultipleFactors

namespace CFSG.Quasithin.ChapterD.UniqueFactor
open NoncentralChiefRefinement
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}
theorem source_solvable_chief_actions
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn G₂)
    (hnf : letI := d.module_elementary
      ¬ IsFFModule (imageRepresentation G₁ V d.module_normalized))
    (hs : Group.IsSolvable G₂) :
    let U := (conjugateSpan G₂ V).subgroupOf G₂
    letI := source_elementary_span_of_notFF d hV hnf
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le G₂))
    ∀ (S : Sylow 2 G₂), (S : Subgroup G₂).map G₂.subtype = T →
      ∀ (s : SeriesOn U) (i : Fin s.series.length),
        1 ≤ quadraticRatio (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ∧
          (¬ s.Central i → ∀ A : Subgroup G₂, A ≤ S →
            A ⊓ (s.factorRepresentation i).ker = A ⊓ pCore 2 G₂) := by
  let := d.finite_right
  let U := (conjugateSpan G₂ V).subgroupOf G₂
  let := source_elementary_span_of_notFF d hV hnf
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le G₂))
  dsimp only
  intro S hS s i
  exact ⟨MultipleFactors.source_chief_image_ratio_ge_one U s hs i,
    fun hi A hA => MultipleFactors.source_chief_sylow_kernel U S
      (source_intrinsic_minimalParabolic_of_notFF d hne hnf S hS) s i hi A hA⟩
end CFSG.Quasithin.ChapterD.UniqueFactor
