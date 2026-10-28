module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Section
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.FixedSpaces

/-!
# Interface between marked geometry and paired coordinates

`MarkedQuotientFactors` retains the marked first factor and the literal
centralizer image. `PairedGeometry` concerns the images of actual fixed
subgroups in `U/E`, together with conjugation between them. Its invariance
and commutation requirements concern only this quotient.

These are contracts for the remaining geometric construction, not assertions
that the source inputs already satisfy them. They allow the linear-coordinate
construction to proceed independently; final assembly must construct all
fields from the original marked local data.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G D : Type*} [Group G] [Group D]

/-- A marked first factor and the actual centralizer image in the core quotient.
For the source application the ambient group is `H`, and `A = ⟨Y_E,τ⟩`. -/
structure MarkedQuotientFactors (A C Q : Subgroup G) [Q.Normal] where
  equiv : (G ⧸ Q) ≃* Equiv.Perm (Fin 3) × (C.map (QuotientGroup.mk' Q))
  first_factor : A.map (equiv.toMonoidHom.comp (QuotientGroup.mk' Q)) =
    (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥
  centralizer_factor : ∀ c : C, equiv (QuotientGroup.mk' Q c) =
    (1, ⟨QuotientGroup.mk' Q c, mem_map_of_mem _ c.property⟩)

/-- Concrete sufficient geometry for constructing the paired projection. This
contract does not assert faithfulness of a representation of the whole `G/Q`. -/
structure PairedGeometry (U E A C Q : Subgroup G)
    [U.Normal] [IsElementaryAbelian 2 U] [E.Normal] [Q.Normal]
    (f : G →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) (τ y : G) where
  line_le : E ≤ U
  factors : MarkedQuotientFactors A C Q
  core_kills : Q ≤ (MarkedSection.action U E f hf hker).ker
  complementary : IsCompl (MarkedSection.fixedImage U E τ)
    (MarkedSection.fixedImage U E (y⁻¹ * τ * y))
  conjugate : MarkedSection.fixedImage U E (y⁻¹ * τ * y) =
    (MarkedSection.fixedImage U E τ).map (MarkedSection.action U E f hf hker y⁻¹)
  first_invariant : ∀ c ∈ C, ∀ w ∈ MarkedSection.fixedImage U E τ,
    MarkedSection.action U E f hf hker c w ∈ MarkedSection.fixedImage U E τ
  commutes : ∀ c ∈ C, Commute (MarkedSection.action U E f hf hker c)
    (MarkedSection.action U E f hf hker y⁻¹)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
