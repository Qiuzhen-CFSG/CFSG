module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Homogeneous.Quotient
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.FixedComplete

/-!
# Homogeneity when the chosen central part is nonzero

The completed fixed-space argument gives V_M = V. The literal quotient
embedding is then an isomorphism, so the full quotient is irreducible and
homogeneous for the original component. This includes nonsplit central covers.

Source: Aschbacher--Smith, 11.0.3(2--3), printed p.760.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
section Stable
variable (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- In the nonzero-central-part branch, the full quotient is irreducible
and hence homogeneous for the original component, with the actual conjugation
formula on every representative. -/
theorem fullModule_homogeneous_of_centralizer_ne_bot
    (hc : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    letI := fullModule_elementary D S
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    ∃ σ : Representation (ZMod 2) M
        (Additive (U ⧸ (centralizer (L : Set G)).subgroupOf U)),
      IsIrreducible (σ.comp (L.subgroupOf M).subtype) ∧
      IsHomogeneousAction (σ.comp (L.subgroupOf M).subtype) ∧
      (∀ (g : M) (v : U),
        σ g (Additive.ofMul (QuotientGroup.mk'
          ((centralizer (L : Set G)).subgroupOf U) v)) =
          Additive.ofMul (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf U)
            ⟨(g : G) * (v : G) * (g : G)⁻¹,
              (mem_normalizer_iff.mp (le_normalizer_componentOrbit V M g.property) v).mp
                v.property⟩)) := by
  let := fullModule_elementary D S
  obtain ⟨σ, _, _, hσ⟩ := fullModule_quotient_semisimple_transitive D S
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let τ := σ.comp (inclusion L.le_normalizer)
  have hi : IsIrreducible τ := quotient_irreducible_of_eq_seed D U
    (le_componentOrbit V M) (L.le_normalizer.trans (le_normalizer_componentOrbit V M)) τ
    (fun l u => hσ (inclusion L.le_normalizer l) u)
    (fullModule_eq_of_centralizer_ne_bot D S hc).le
  have hi' : IsIrreducible (σ.comp (L.subgroupOf M).subtype) :=
    (irreducible_comp_surjective_iff (subgroupOfEquivOfLe L.le_normalizer).symm.toMonoidHom
      (subgroupOfEquivOfLe L.le_normalizer).symm.surjective _).mp hi
  exact ⟨σ, hi', ExtensionConsequences.homogeneous_of_irreducible hi', hσ⟩
end Stable


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
