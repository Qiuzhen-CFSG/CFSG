module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Ambient
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Identification

/-!
# Core calculations for the binary linear parabolics

The ambient PSL₃(2) has trivial two-core. Both concrete parabolics have an
elementary two-core of order four, and their quotients are S₃. Conjugation
identifies each quotient with the full automorphism group of its core, and
every invariant subgroup of the core is trivial or the whole core.

The proof applies the symmetric-four core calculations to the actual
isomorphisms constructed from the coordinate stabilizers. The action equations
use the literal core quotient maps and subgroup inclusions into PSL₃(2).
The final isomorphisms transport these results to each conjugate parabolic
through the restriction of ambient conjugation, using `ParabolicCoreModel`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.4 and
I.5.7, printed pp.420–421, the binary projective-plane local model.
-/

public section

namespace Matrix.PSL3Two

/-- The point stabilizer's intrinsic two-core is an elementary four-group. -/
theorem pointParabolic_core_data :
    IsElementaryAbelian 2 (pCore 2 pointParabolic) ∧
      Nat.card (pCore 2 pointParabolic) = 4 :=
  ParabolicCoreModel.core_data pointParabolicEquivS4

/-- The line stabilizer's intrinsic two-core is an elementary four-group. -/
theorem lineParabolic_core_data :
    IsElementaryAbelian 2 (pCore 2 lineParabolic) ∧
      Nat.card (pCore 2 lineParabolic) = 4 :=
  ParabolicCoreModel.core_data lineParabolicEquivS4

theorem pointParabolic_core_selfCentralizing :
    Subgroup.centralizer (pCore 2 pointParabolic : Set pointParabolic) ≤
      pCore 2 pointParabolic :=
  ParabolicCoreModel.core_selfCentralizing pointParabolicEquivS4

theorem lineParabolic_core_selfCentralizing :
    Subgroup.centralizer (pCore 2 lineParabolic : Set lineParabolic) ≤
      pCore 2 lineParabolic :=
  ParabolicCoreModel.core_selfCentralizing lineParabolicEquivS4

/-- Normality is relative to the point parabolic, as in the local source argument. -/
theorem pointParabolic_normal_le_core (N : Subgroup pointParabolic) [N.Normal]
    (hN : N ≤ pCore 2 pointParabolic) :
    N = ⊥ ∨ N = pCore 2 pointParabolic :=
  ParabolicCoreModel.normal_le_core pointParabolicEquivS4 N hN

/-- Normality is relative to the line parabolic, as in the local source argument. -/
theorem lineParabolic_normal_le_core (N : Subgroup lineParabolic) [N.Normal]
    (hN : N ≤ pCore 2 lineParabolic) :
    N = ⊥ ∨ N = pCore 2 lineParabolic :=
  ParabolicCoreModel.normal_le_core lineParabolicEquivS4 N hN

/-- The actual quotient of the point stabilizer by its intrinsic two-core. -/
noncomputable def pointParabolicCoreQuotientEquivS3 :
    pointParabolic ⧸ pCore 2 pointParabolic ≃* Equiv.Perm (Fin 3) :=
  ParabolicCoreModel.coreQuotientEquiv pointParabolicEquivS4

/-- The actual quotient of the line stabilizer by its intrinsic two-core. -/
noncomputable def lineParabolicCoreQuotientEquivS3 :
    lineParabolic ⧸ pCore 2 lineParabolic ≃* Equiv.Perm (Fin 3) :=
  ParabolicCoreModel.coreQuotientEquiv lineParabolicEquivS4

/-- Conjugation realizes the point quotient as every automorphism of its core. -/
noncomputable def pointParabolicCoreQuotientAction :
    pointParabolic ⧸ pCore 2 pointParabolic ≃* MulAut (pCore 2 pointParabolic) :=
  ParabolicCoreModel.coreQuotientAutEquiv pointParabolicEquivS4

/-- Conjugation realizes the line quotient as every automorphism of its core. -/
noncomputable def lineParabolicCoreQuotientAction :
    lineParabolic ⧸ pCore 2 lineParabolic ≃* MulAut (pCore 2 lineParabolic) :=
  ParabolicCoreModel.coreQuotientAutEquiv lineParabolicEquivS4

theorem pointParabolicCoreQuotientAction_mk (g : pointParabolic)
    (x : pCore 2 pointParabolic) :
    ((pointParabolicCoreQuotientAction
      (QuotientGroup.mk' (pCore 2 pointParabolic) g)) x : pointParabolic) =
        g * x * g⁻¹ :=
  ParabolicCoreModel.coreQuotientAutEquiv_mk pointParabolicEquivS4 g x

theorem lineParabolicCoreQuotientAction_mk (g : lineParabolic)
    (x : pCore 2 lineParabolic) :
    ((lineParabolicCoreQuotientAction
      (QuotientGroup.mk' (pCore 2 lineParabolic) g)) x : lineParabolic) =
        g * x * g⁻¹ :=
  ParabolicCoreModel.coreQuotientAutEquiv_mk lineParabolicEquivS4 g x

/-- The quotient action is conjugation through the two actual subgroup inclusions. -/
theorem pointParabolicCoreQuotientAction_mk_coe (g : pointParabolic)
    (x : pCore 2 pointParabolic) :
    (((pointParabolicCoreQuotientAction
      (QuotientGroup.mk' (pCore 2 pointParabolic) g)) x : pointParabolic) : PSL) =
        (g : PSL) * (x : pointParabolic) * (g : PSL)⁻¹ :=
  congrArg pointParabolic.subtype (pointParabolicCoreQuotientAction_mk g x)

/-- The quotient action is conjugation through the two actual subgroup inclusions. -/
theorem lineParabolicCoreQuotientAction_mk_coe (g : lineParabolic)
    (x : pCore 2 lineParabolic) :
    (((lineParabolicCoreQuotientAction
      (QuotientGroup.mk' (pCore 2 lineParabolic) g)) x : lineParabolic) : PSL) =
        (g : PSL) * (x : lineParabolic) * (g : PSL)⁻¹ :=
  congrArg lineParabolic.subtype (lineParabolicCoreQuotientAction_mk g x)

theorem pointParabolicCoreQuotientAction_faithful :
    Function.Injective pointParabolicCoreQuotientAction :=
  pointParabolicCoreQuotientAction.injective

theorem lineParabolicCoreQuotientAction_faithful :
    Function.Injective lineParabolicCoreQuotientAction :=
  lineParabolicCoreQuotientAction.injective

/-- Over F₂, invariant additive subspaces are precisely invariant subgroups. -/
theorem pointParabolicCoreQuotientAction_irreducible
    (W : Subgroup (pCore 2 pointParabolic))
    (hW : ∀ q : pointParabolic ⧸ pCore 2 pointParabolic,
      ∀ x ∈ W, pointParabolicCoreQuotientAction q x ∈ W) :
    W = ⊥ ∨ W = ⊤ :=
  ParabolicCoreModel.core_action_irreducible pointParabolicEquivS4 W hW

/-- Over F₂, invariant additive subspaces are precisely invariant subgroups. -/
theorem lineParabolicCoreQuotientAction_irreducible
    (W : Subgroup (pCore 2 lineParabolic))
    (hW : ∀ q : lineParabolic ⧸ pCore 2 lineParabolic,
      ∀ x ∈ W, lineParabolicCoreQuotientAction q x ∈ W) :
    W = ⊥ ∨ W = ⊤ :=
  ParabolicCoreModel.core_action_irreducible lineParabolicEquivS4 W hW

/-- Apply `ParabolicCoreModel` through ambient conjugation to any point parabolic. -/
noncomputable def conjugatePointParabolicEquivS4 (g : PSL) :
    pointParabolic.map (MulAut.conj g).toMonoidHom ≃* Equiv.Perm (Fin 4) :=
  ((MulAut.conj g).subgroupMap pointParabolic).symm.trans pointParabolicEquivS4

/-- Apply `ParabolicCoreModel` through ambient conjugation to any line parabolic. -/
noncomputable def conjugateLineParabolicEquivS4 (g : PSL) :
    lineParabolic.map (MulAut.conj g).toMonoidHom ≃* Equiv.Perm (Fin 4) :=
  ((MulAut.conj g).subgroupMap lineParabolic).symm.trans lineParabolicEquivS4

theorem conjugatePointParabolic_core_data (g : PSL) :
    IsElementaryAbelian 2 (pCore 2 (pointParabolic.map (MulAut.conj g).toMonoidHom)) ∧
      Nat.card (pCore 2 (pointParabolic.map (MulAut.conj g).toMonoidHom)) = 4 :=
  ParabolicCoreModel.core_data (conjugatePointParabolicEquivS4 g)

theorem conjugateLineParabolic_core_data (g : PSL) :
    IsElementaryAbelian 2 (pCore 2 (lineParabolic.map (MulAut.conj g).toMonoidHom)) ∧
      Nat.card (pCore 2 (lineParabolic.map (MulAut.conj g).toMonoidHom)) = 4 :=
  ParabolicCoreModel.core_data (conjugateLineParabolicEquivS4 g)

end Matrix.PSL3Two
