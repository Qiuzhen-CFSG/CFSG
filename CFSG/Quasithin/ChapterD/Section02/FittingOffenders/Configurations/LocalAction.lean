module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations

/-!
# The D.2.14 configurations on the literal local group

Apply the completed reduced classification to the original core and actor
inside `P ⊔ A`, with the given faithful representation on the moved module.
The support factors and all their multiplication, addition, coordinate and
conjugation maps remain in that local group and that representation. Their
plane dimensions and the fixed codimension also give the total and fixed
dimensions: four and one in the two-factor case, six and three in the
three-factor case.

The earlier-source owner must construct `Reduced`, including membership in
the genuine inclusion-minimal global cubic family `ChapterD.QhatStar`.
This application discharges every subsequent configuration premise.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.14(3),(6),(7), printed pp.186--187, after passing to PA on [V,P].
-/

public section
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
open Representation.BinaryOffender
open scoped ENNReal

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The complete reduced configuration on `PA`, with no additional support,
ratio, or hyperplane assumption. The dimensions refer to the original module
and the fixed space of the original actor inside this literal local group. -/
theorem local_generated_configurations (P A : Subgroup G)
    (σ : Representation (ZMod 2) (P ⊔ A : Subgroup G) V) {s : ℕ}
    (h : Reduced σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)) s) :
    ∃ d : SupportFactors σ (P.subgroupOf (P ⊔ A)) s,
      d.Alternatives (A.subgroupOf (P ⊔ A)) ∧
      Module.finrank (ZMod 2) V = 2 * s ∧
      Module.finrank (ZMod 2) (fixedSpace σ (A.subgroupOf (P ⊔ A))) = 2 * s - 3 ∧
      fixedCodim σ (A.subgroupOf (P ⊔ A)) = 3 ∧ cubicRatio σ = 3 / 2 := by
  obtain ⟨d, hd, hc, hr⟩ := h.configurations σ
  have hv := d.finrank_eq σ
  have hf := fixedCodim_add_finrank σ (A.subgroupOf (P ⊔ A))
  exact ⟨d, hd, hv, by omega, hc, hr⟩

end CFSG.Quasithin.ChapterD.FittingConfigurations
