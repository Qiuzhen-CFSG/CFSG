module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double.ProjectionCodimension

/-!
# The double-S₃ maximum-elementary construction

The native two-factor module clauses give an additive fixed-codimension bound
for the two literal projections. A maximum-elementary image is an offender,
so this bound forces it to contain both its coordinate projections. The full
residual commutator then supplies maximum-elementary images meeting each S₃
factor nontrivially. `minimalSolvable_twoFactor_maxima` exports these witnesses
on the original star quotient, without additional support or splitting premises.

Applying the witnesses to the normal full offender actor proves the literal
preimage Thompson equality in the double-S₃ branch. Normality of each individual
factor in the ambient star group is not needed. The source-theorem owner retains
the other branches and the final normal S₃ decomposition assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.13, printed p.929.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double

variable {G : Type*} [Group G] [Finite G]

/-- The constructed coordinate witnesses give the double-S₃ Thompson equality
on the full preimage under the original star quotient map. -/
theorem minimalSolvable_twoFactor_thompson
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      pResidual 2 (FFFactors.offenderActor (starRepresentation z v))) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    starImage z v (elementaryAbelianMaxJ (starPreimage z v I)) = I := by
  intro I
  obtain ⟨E₁, E₂, hE₁, hE₂, hn₁, hn₂⟩ :=
    minimalSolvable_twoFactor_maxima L T z v hz S hS hX c e₁ e₂ hF
  have hgen : c.first.map I.subtype ⊔ c.second.map I.subtype = I := by
    rw [← Subgroup.map_sup, c.product.sup_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  exact star_thompson_eq_of_two_intersections z v I _ _
    ((c.first.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e₁)
    ((c.second.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e₂)
    hgen E₁ E₂ hE₁ hE₂ hn₁ hn₂

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double

end
