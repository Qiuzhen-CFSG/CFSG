module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Geometry.SourceOperators.Residual

/-!
# The original marked operators on the full line module

The original natural action, relatively normal residual and Pc marking
supply the cubic, involutory and inversion identities on U, before taking
U/E. The chosen residual element is nonidentity in the original core
quotient. Both it and τ retain their original ambient values.

The denominator fixed subgroup has order two and its intrinsic subspace
is the span of a nonzero vector. All module and normality instances below
come from `OriginalData`; no operator, lifting or decomposition premise is
added. `Geometry.FixedImages` supplies the subsequent fixed-image results.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open Representation.NormalElementaryQuotient
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry.OriginalData
variable {G D : Type*} [Group G] [Group D] [Finite G]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]

/-- The three raw marked operator identities, with the actual instances from d. -/
theorem markedOperatorRelations (d : OriginalData Y T V M E Pc)
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E)))
    (y : G) (hy : y ∈ lineY Y E)
    (hne : Descent.QuotientIdentification.quotientMap E
      ⟨y, (lineY_le Y E hy).2⟩ ≠ 1) :
    let := d.module_normal
    let := d.module_elementary
    MarkedOperatorRelations ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))
      f hf hker d.tau (d.residualElement y hy) := by
  let := d.module_normal
  let := d.module_elementary
  exact ⟨d.operator_cubic f hf hker y hy hne,
    d.operator_involutory f hf hker, d.operator_inverts f hf hker y hy⟩

/-- The actual fixed denominator line, using d's elementary module instance. -/
theorem denominator_fixed_line (d : OriginalData Y T V M E Pc) :
    let := d.module_elementary
    ∃ z : Additive ((lineV V E).subgroupOf (temporaryLineNormalizer T V E)), z ≠ 0 ∧
      subspace ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))
        ((E.subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
          ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))) ⊓
      subspace ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))
        ((centralizer ({d.tau} : Set (temporaryLineNormalizer T V E))).subgroupOf
          ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))) =
        Submodule.span (ZMod 2) {z} := by
  let := d.module_elementary
  exact d.exists_denominator_fixed_generator

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry.OriginalData
