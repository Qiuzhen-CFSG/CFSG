module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.Catalogue
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport

/-!
# Binary endpoints of the appendix component carriers

An actual field of order two is identified with `ZMod 2`. Entrywise field
transport, followed by restriction to commutators, identifies the small
symplectic endpoint with A₆ and the G₂ endpoint with the derived octonion
automorphism group. The linear endpoint uses the trivial scalar center over
the two-element field. No simplicity or order recognition is assumed here.

These comparisons apply to the output predicates of the appendix analysis;
they do not establish that analysis. The exclusion of larger defining fields
then removes every exponent except one, including the PSL₂ alternatives.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.5(1)(iv),
printed p.104, and the model-sieve step of 15.3.49(l), printed p.1144.
The imported ATLAS field transports retain their source attribution and license.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve

open BorelInner

/-- The source larger-field exclusion, retaining all actual carrier equivalences. -/
def NoLargerField (X : Type*) [Group X] : Prop :=
  ∀ e : ℕ, 1 < e → ¬ LieComponentModel X e

/-- The field exclusion depends on the actual group, not its presentation. -/
theorem NoLargerField.of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (h : NoLargerField X) (f : Y ≃* X) : NoLargerField Y := by
  intro e he hm
  apply h e he
  cases hm with
  | linear_two lo F hF model =>
    exact .linear_two lo F hF (model.map (f.symm.trans ·))
  | linear_three lo F hF model =>
    exact .linear_three lo F hF (model.map (f.symm.trans ·))
  | symplectic lo F hF model =>
    exact .symplectic lo F hF (model.map (f.symm.trans ·))
  | g2 lo F hF model =>
    exact .g2 lo F hF (model.map (f.symm.trans ·))
  | binary_linear heq n hn model =>
    exact .binary_linear heq n hn (model.map (f.symm.trans ·))

/-- Restrict a group equivalence to its actual derived subgroups. -/
noncomputable def derivedEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    commutator X ≃* commutator Y := by
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

/-- The derived binary symplectic group, before any central quotient, is A₆. -/
noncomputable def symplecticDerivedEquivSix {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    commutator (Matrix.symplecticGroup (Fin 2) F) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivSp
    (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivZModTwo F hF)
  let f := e.trans Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (derivedEquiv f).trans (MulEquiv.subgroupCongr ?_)
  exact alternatingGroup.commutator_perm_eq (by norm_num)

/-- The SL₃ carrier over any binary field is the catalogue's actual PSL₃(2). -/
noncomputable def linearThreeEquivBinary {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    Matrix.SpecialLinearGroup (Fin 3) F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (Atlas.fieldEquivSL 3
    (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivZModTwo F hF)).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm

/-- Field transport restricts to the actual G₂ derived carrier. -/
noncomputable def g2DerivedEquivBinary {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    commutator (Atlas.G2.Model F) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  derivedEquiv (Atlas.G2.fieldEquiv
    (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivZModTwo F hF))

/-- Each binary Lie alternative gives the exact carrier requested in (l). -/
theorem binary_of_lie_alternative {X : Type*} [Group X] {e : ℕ}
    (h : LieComponentModel X e) (he : ¬ 1 < e) : BinaryComponentModel X := by
  cases h with
  | linear_two lower F hF model => omega
  | linear_three lower F hF model =>
    have heq : e = 1 := by omega
    have hc : Nat.card F = 2 := by simpa only [heq, pow_one] using hF
    exact .linear 3 (by decide) (by decide)
      (model.map (fun f => f.trans (linearThreeEquivBinary hc)))
  | symplectic lower F hF model =>
    have heq : e = 1 := by omega
    have hc : Nat.card F = 2 := by simpa only [heq, pow_one] using hF
    exact .alternating_six
      (model.map (fun f => f.trans (symplecticDerivedEquivSix hc)))
  | g2 lower F hF model =>
    have heq : e = 1 := by omega
    have hc : Nat.card F = 2 := by simpa only [heq, pow_one] using hF
    exact .g2_derived (model.map (fun f => f.trans (g2DerivedEquivBinary hc)))
  | binary_linear heq n hn model =>
    exact .linear n (by omega) (by omega) model

/-- The group-only terminal sieve. Source module information must also be
retained by a consumer invoking the triple-cover alternative. -/
theorem binary_of_component_alternatives {X : Type*} [Group X]
    (h : ComponentModel X) (hfield : NoLargerField X) : BinaryComponentModel X := by
  cases h with
  | lie e model =>
    exact binary_of_lie_alternative model (fun he => hfield e he model)
  | alternating_seven model => exact .alternating_seven model
  | triple_alternating_six model => exact .triple_cover model

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve
