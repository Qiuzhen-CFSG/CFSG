module
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.SupportExclusion.Linear
public import CFSG.Quasithin.ChapterG.Section08.ThetaFaithfulness
public import Theory.GroupTheory.Fitting.PrimeSubgroups
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration

/-!
# The canonical cubic family in D.2.25

The order-three subgroups of O₃ with two-dimensional binary support are
exactly the canonical family from D.2.12. Normality makes their fixed space
an actual G-subrepresentation. Odd averaging shows that the original full
Fitting-moved hypothesis passes to this fixed complement; it is not inferred
from the cubic ratio. These are the original support and residual-action
inputs in Aschbacher–Smith D.2.25, printed p.190.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem x1_eq_canonical :
    let := BinaryGroupAction.action ρ
    {X : Subgroup G | X ≤ pCore 3 G ∧ Nat.card X = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 2} =
      smallSupportFactors G (Multiplicative V) 1 := by
  let := BinaryGroupAction.action ρ
  ext X
  constructor
  · rintro ⟨hXP,hcard,hdim⟩
    refine ⟨hXP.trans (pCore_le_fitting G 3),hcard,?_⟩
    rw [BinaryGroupAction.commutator_card,hdim]
  · intro hX
    have hcard : Nat.card X = 3 := hX.2.1
    have hp : IsPGroup 3 X := by
      exact IsPGroup.of_card (n := 1) (by simpa using hcard)
    refine ⟨hp.le_pCore_of_le_fitting hX.1,hcard,?_⟩
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 2 ^ 2
    rw [← BinaryGroupAction.commutator_card]
    exact hX.2.2

/-- The fixed space of the actual normal subgroup, as a representation of G. -/
noncomputable def normalFixed (Y : Subgroup G) [Y.Normal] : Subrepresentation ρ where
  toSubmodule := fixedSpace ρ Y
  apply_mem_toSubmodule g v hv :=
    (fixedSpace_invariant_normalizer ρ (X := Y) (A := ⊤)
      le_normalizer_of_normal (mem_top g) v).2 hv

omit [FiniteDimensional (ZMod 2) V] in
/-- Full movement by an odd subgroup passes to every invariant subspace. -/
theorem subrepresentation_moved_of_odd (W : Subrepresentation ρ)
    (F : Subgroup G) (hodd : Odd (Nat.card F))
    (hm : subspaceCommutator ρ ⊤ F = ⊤) :
    subspaceCommutator W.toRepresentation ⊤ F = ⊤ := by
  have hfix : fixedSpace ρ F = ⊥ := by
    simpa only [hm,inf_top_eq] using
      (ElementaryCore.SupportExclusion.moved_split ρ F hodd).disjoint.eq_bot
  have hz : fixedSpace W.toRepresentation F = ⊥ := by
    apply le_bot_iff.mp
    intro w hw
    have hv : (w : V) ∈ fixedSpace ρ F := fun f => congrArg Subtype.val (hw f)
    rw [hfix,Submodule.mem_bot] at hv
    exact Subtype.ext hv
  simpa only [hz,bot_sup_eq] using
    (ElementaryCore.SupportExclusion.moved_split W.toRepresentation F hodd).sup_eq_top

omit [FiniteDimensional (ZMod 2) V] in
/-- The original Fitting-moved hypothesis is inherited by C_V(Y). -/
theorem normalFixed_fitting_moved (Y : Subgroup G) [Y.Normal]
    (hcore : pCore 2 G = ⊥)
    (hm : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) :
    subspaceCommutator (normalFixed ρ Y).toRepresentation ⊤ (fittingSubgroup G) = ⊤ :=
  subrepresentation_moved_of_odd ρ (normalFixed ρ Y) (fittingSubgroup G)
    (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot hcore) hm
end CFSG.Quasithin.ChapterD.CyclicSource
