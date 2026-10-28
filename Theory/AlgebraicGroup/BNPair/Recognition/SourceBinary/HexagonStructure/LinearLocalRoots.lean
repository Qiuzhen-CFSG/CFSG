module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RootCommutators
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.LocalStructure
public import Theory.ElementaryAbelian.Injective

/-!
# Canonical roots inside the actual source PSL2 local group

The canonical simple root embeds faithfully in the permutation group L_i
through the original endpoint panel action. A supplied isomorphism of this
actual L_i with binary PSL2 therefore makes U_i elementary abelian: its
image lies in a Sylow two-subgroup, whose additive field coordinates are
already proved. This argument includes PSL2(2) and uses no perfectness of
an original local factor. Combining it with the radical intersection
calculation gives the initial three-middle-root bound in (6E).

Source: Fong--Seitz I Section 5 and (6E), printed pp.25--28 and44. The
catalogue and its transport to the actual L_i remain earlier source inputs;
they are not inferred from a name or an isomorphism of an original factor.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Embed the canonical simple root in the actual faithful local permutation group. -/
def simpleRootLocalMap (i : Fin 2) : simpleRoot Q split i →* localGroup Q split i :=
  (panelAction Q i (simpleRoot Q split i)
    ((simpleRoot_le Q split i).trans
      (split.U_le.trans (Q.tits.B_le_standardParabolic {Q.simple i})))).codRestrict _ (by
        intro u
        exact ⟨⟨u,(show simpleRoot Q split i ≤ localClosure Q split i from
          (simpleRoot_le Q split i).trans le_sup_left) u.property⟩,by
          rw [localAction_eq_panelAction]
          rfl⟩)

theorem simpleRootLocalMap_injective (i : Fin 2) :
    Function.Injective (simpleRootLocalMap Q split i) := by
  intro a b hab
  exact simpleRoot_panelAction_injective Q split i (congrArg Subtype.val hab)

@[simp] theorem simpleRootLocalMap_apply (i : Fin 2) (u : simpleRoot Q split i) :
    (simpleRootLocalMap Q split i u : Equiv.Perm (Panel Q i)) =
      panelAction Q i (simpleRoot Q split i)
        ((simpleRoot_le Q split i).trans
          (split.U_le.trans (Q.tits.B_le_standardParabolic {Q.simple i}))) u := by rfl

/-- A genuine local PSL2 marking gives elementary abelianness of the canonical
root, including PSL2(2); the original local factor need not be perfect. -/
theorem simpleRoot_elementary_of_linear {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : localGroup Q split i ≃* PSL(2,F)) :
    IsElementaryAbelian 2 (simpleRoot Q split i) := by
  let f := μ.toMonoidHom.comp (simpleRootLocalMap Q split i)
  have hf : Function.Injective f := μ.injective.comp (simpleRootLocalMap_injective Q split i)
  have htwo : IsPGroup 2 (simpleRoot Q split i) :=
    split.isTwo.of_injective (inclusion (simpleRoot_le Q split i)) (inclusion_injective _)
  have hF : IsPGroup 2 f.range := htwo.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨T,hT⟩ := hF.exists_le_sylow
  let g : simpleRoot Q split i →* T := f.codRestrict _ (fun u => hT ⟨u,rfl⟩)
  have hg : Function.Injective g := fun a b hab => hf (congrArg Subtype.val hab)
  let e := BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T
  let : IsElementaryAbelian 2 (Multiplicative F) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Multiplicative.toAdd.injective
        change (x^2).toAdd = 0
        rw [pow_two]
        exact CharTwo.add_self_eq_zero x.toAdd) }
  exact IsElementaryAbelian.of_injective (e.symm.toMonoidHom.comp g) (e.symm.injective.comp hg)

theorem simpleRoot_commutator_eq_bot_of_linear {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : localGroup Q split i ≃* PSL(2,F)) :
    ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥ := by
  let := simpleRoot_elementary_of_linear Q split i μ
  exact commutator_self_eq_bot_iff.mpr inferInstance

/-- The source linear local marking discharges the abelian-root premise of
6E's initial three-middle-root bound on the same quotient. -/
theorem radical_commutator_le_middle_of_linear {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ≤ middleRoots Q split i j :=
  radical_commutator_le_middle Q split hm i j hij hK
    (simpleRoot_commutator_eq_bot_of_linear Q split i μ)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
