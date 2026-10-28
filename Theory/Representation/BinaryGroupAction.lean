module

public import Theory.GroupAction.SupportTransport
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness

/-!
# Binary representations as elementary abelian group actions

The additive binary module is the elementary abelian group `Multiplicative V`.
Its action is exactly the given representation. The order isomorphism between
binary submodules and subgroups identifies the spans of linear displacements
with the group-action commutators, and fixed subspaces with fixed subgroups.
Thus independence, generation and cardinality statements for action supports
transport along the actual inclusions.

The construction is used to apply the small-support decomposition of
Aschbacher–Smith D.2.12 to the representation in B.1.9.
-/

@[expose] public section

open Representation.BinaryOffender
namespace Representation.BinaryGroupAction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The multiplicative notation for the original linear action. -/
@[instance_reducible] def action : MulDistribMulAction G (Multiplicative V) where
  smul g v := Multiplicative.ofAdd (ρ g v.toAdd)
  one_smul v := congrArg Multiplicative.ofAdd (congrArg (fun f => f v.toAdd) ρ.map_one)
  mul_smul g h v := congrArg Multiplicative.ofAdd (congrArg (fun f => f v.toAdd) (ρ.map_mul g h))
  smul_mul g v w := congrArg Multiplicative.ofAdd ((ρ g).map_add v.toAdd w.toAdd)
  smul_one g := congrArg Multiplicative.ofAdd ((ρ g).map_zero)

/-- Submodules and additive subgroups coincide over the prime field. -/
def submoduleEquivSubgroup : Submodule (ZMod 2) V ≃o Subgroup (Multiplicative V) :=
  (AddSubgroup.toZModSubmodule 2).symm.trans AddSubgroup.toSubgroup

/-- The underlying additive group has exponent dividing two. -/
theorem elementary : IsElementaryAbelian 2 (Multiplicative V) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro v
    change (2 : ℕ) • v.toAdd = 0
    calc
      (2 : ℕ) • v.toAdd = (2 : ZMod 2) • v.toAdd :=
        (Nat.cast_smul_eq_nsmul (ZMod 2) 2 v.toAdd).symm
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]

/-- Injectivity of the representation gives a faithful group action. -/
theorem faithful (hf : Function.Injective ρ) :
    let := action ρ
    FaithfulSMul G (Multiplicative V) := by
  let := action ρ
  constructor
  intro g h he
  apply hf
  ext v
  exact congrArg Multiplicative.toAdd (he (Multiplicative.ofAdd v))

/-- The two definitions of the moved space agree on the original vectors. -/
theorem commutator_eq (A : Subgroup G) :
    let := action ρ
    commutatorAction A (Multiplicative V) =
      submoduleEquivSubgroup (subspaceCommutator ρ ⊤ A) := by
  let := action ρ
  apply le_antisymm
  · rw [commutatorAction_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, v, rfl⟩
    change -v.toAdd + ρ a v.toAdd ∈ subspaceCommutator ρ ⊤ A
    rw [add_comm, ← sub_eq_add_neg]
    exact Submodule.subset_span ⟨a, a.property, v.toAdd, Submodule.mem_top, rfl⟩
  · apply (submoduleEquivSubgroup (V := V)).symm.le_iff_le.mp
    change subspaceCommutator ρ ⊤ A ≤
      (submoduleEquivSubgroup (V := V)).symm (commutatorAction A (Multiplicative V))
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    change Multiplicative.ofAdd (ρ a v - v) ∈ commutatorAction A (Multiplicative V)
    rw [commutatorAction_eq_closure]
    apply Subgroup.subset_closure
    refine ⟨⟨a, ha⟩, Multiplicative.ofAdd v, ?_⟩
    change Multiplicative.ofAdd (ρ a v - v) = Multiplicative.ofAdd (-v + ρ a v)
    congr 1
    exact sub_eq_neg_add _ _

/-- The subgroup conversion preserves the underlying finite cardinality. -/
theorem card_submoduleEquivSubgroup (U : Submodule (ZMod 2) V) :
    Nat.card (submoduleEquivSubgroup U) = Nat.card U := by
  exact Nat.card_congr
    { toFun := fun x => ⟨x.val.toAdd, x.property⟩
      invFun := fun x => ⟨Multiplicative.ofAdd x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Group-action support cardinality is the binary dimension power. -/
theorem commutator_card [FiniteDimensional (ZMod 2) V] (A : Subgroup G) :
    letI := action ρ
    Nat.card (commutatorAction A (Multiplicative V)) =
      2 ^ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  let := action ρ
  rw [commutator_eq, card_submoduleEquivSubgroup,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- The fixed subgroup is the actual fixed subspace in multiplicative notation. -/
theorem fixedPoints_eq (A : Subgroup G) :
    letI := action ρ
    FixedPoints.subgroup A (Multiplicative V) =
      submoduleEquivSubgroup (fixedSpace ρ A) := by
  let := action ρ
  rfl

/-- Taking moved spaces commutes with generation by any family of actors. -/
theorem moved_iSup {ι : Sort*} (A : ι → Subgroup G) :
    subspaceCommutator ρ ⊤ (⨆ i, A i) = ⨆ i, subspaceCommutator ρ ⊤ (A i) := by
  let := action ρ
  apply (submoduleEquivSubgroup (V := V)).injective
  rw [OrderIso.map_iSup]
  simp only [← commutator_eq]
  exact ActionSupport.commutatorAction_eq_iSup_of_eq_iSup A rfl

end Representation.BinaryGroupAction
