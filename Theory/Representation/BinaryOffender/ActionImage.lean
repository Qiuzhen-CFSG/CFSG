module

public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Faithful images of binary representations

The image inside the invertible linear maps carries a tautological faithful
action. Fixed spaces are unchanged under passage to this image. The first
isomorphism theorem identifies each subgroup image with its quotient by its
actual relative action kernel; faithful subgroups preserve binary rank.

These constructions apply to the invariant-section actions of Aschbacher–Smith,
*The Classification of Quasithin Groups*, B.1.5(8), printed pp. 69–70.
-/

@[expose] public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The actual image of a representation in the group of invertible linear maps. -/
def actionImage : Subgroup (Module.End (ZMod 2) V)ˣ := ρ.asGroupHom.range

def actionHom : G →* actionImage ρ := ρ.asGroupHom.rangeRestrict

def imageRepresentation : Representation (ZMod 2) (actionImage ρ) V :=
  (Units.coeHom _).comp (actionImage ρ).subtype

def actionSubgroup (A : Subgroup G) : Subgroup (actionImage ρ) := A.map (actionHom ρ)

theorem imageRepresentation_injective : Function.Injective (imageRepresentation ρ) := by
  intro x y h
  apply Subtype.ext
  exact Units.ext h

@[simp] theorem imageRepresentation_actionHom (g : G) :
    imageRepresentation ρ (actionHom ρ g) = ρ g := rfl

@[simp] theorem actionHom_eq_one_iff (g : G) :
    actionHom ρ g = 1 ↔ ∀ v, ρ g v = v := by
  constructor
  · intro h v
    have he := congrArg (fun a => imageRepresentation ρ a v) h
    simpa using he
  · intro h
    apply imageRepresentation_injective ρ
    ext v
    exact h v

@[simp] theorem fixedSpace_actionSubgroup (A : Subgroup G) :
    fixedSpace (imageRepresentation ρ) (actionSubgroup ρ A) = fixedSpace ρ A := by
  ext v
  constructor
  · intro hv a
    exact hv ⟨actionHom ρ a, Subgroup.mem_map_of_mem _ a.property⟩
  · intro hv ⟨a, b, hb, hba⟩
    subst a
    exact hv ⟨b, hb⟩

@[simp] theorem fixedCodim_actionSubgroup (A : Subgroup G) :
    fixedCodim (imageRepresentation ρ) (actionSubgroup ρ A) = fixedCodim ρ A := by
  unfold fixedCodim
  rw [fixedSpace_actionSubgroup ρ A]

instance [Finite G] : Finite (actionImage ρ) :=
  Finite.of_surjective (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective

theorem actionHom_subgroup_injective (A : Subgroup G)
    (hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1) :
    Function.Injective ((actionHom ρ).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro a ha
  apply Subtype.ext
  exact hfaith a a.property ((actionHom_eq_one_iff ρ a).mp ha)

theorem actionHom_subgroup_range (A : Subgroup G) :
    ((actionHom ρ).comp A.subtype).range = actionSubgroup ρ A := by
  ext a
  simp [actionSubgroup, MonoidHom.mem_range, Subgroup.mem_map]

/-- The actual relative action kernel consists of the elements fixing every vector. -/
theorem mem_actionHom_subgroup_ker (A : Subgroup G) (a : A) :
    a ∈ ((actionHom ρ).comp A.subtype).ker ↔ ∀ v, ρ a v = v :=
  actionHom_eq_one_iff ρ a

/-- First isomorphism theorem for the actual action of `A`. -/
noncomputable def actionQuotientEquiv (A : Subgroup G) :
    A ⧸ ((actionHom ρ).comp A.subtype).ker ≃* actionSubgroup ρ A :=
  (QuotientGroup.quotientKerEquivRange _).trans
    (MulEquiv.subgroupCongr (actionHom_subgroup_range ρ A))

/-- A faithful subgroup is isomorphic to its actual action image. -/
noncomputable def faithfulActionEquiv (A : Subgroup G)
    (hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1) : A ≃* actionSubgroup ρ A :=
  (MonoidHom.ofInjective (actionHom_subgroup_injective ρ A hfaith)).trans
    (MulEquiv.subgroupCongr (actionHom_subgroup_range ρ A))

@[simp] theorem faithfulActionEquiv_apply (A : Subgroup G)
    (hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1) (a : A) :
    (faithfulActionEquiv ρ A hfaith a : actionImage ρ) = actionHom ρ a := rfl

theorem actionSubgroup_rank (A : Subgroup G)
    (hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1) :
    rank (actionSubgroup ρ A) = rank A :=
  congrArg (Nat.log 2) (Nat.card_congr (faithfulActionEquiv ρ A hfaith).toEquiv).symm

theorem IsElementaryTwo.actionSubgroup {A : Subgroup G} (hA : IsElementaryTwo A)
    (hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1) :
    IsElementaryTwo (actionSubgroup ρ A) := by
  let _ : IsElementaryAbelian 2 A := hA.2
  refine ⟨?_, IsElementaryAbelian.map _⟩
  intro hbot
  apply hA.1
  apply le_antisymm _ bot_le
  intro a ha
  have him : actionHom ρ a ∈ BinaryOffender.actionSubgroup ρ A := Subgroup.mem_map_of_mem _ ha
  rw [hbot, Subgroup.mem_bot] at him
  exact hfaith a ha ((actionHom_eq_one_iff ρ a).mp him)


/-- If a normal action kernel contains `A`, it also contains `[L,A]`.
Thus generation `L = [L,A]` promotes trivial action by `A` to trivial action by `AL`. -/
theorem trivial_sup_of_commutator_eq (L A : Subgroup G) (hL : ⁅L, A⁆ = L)
    (hA : ∀ a ∈ A, ∀ v, ρ a v = v) :
    ∀ g ∈ A ⊔ L, ∀ v, ρ g v = v := by
  have hker : A ≤ (actionHom ρ).ker := fun a ha => (actionHom_eq_one_iff ρ a).mpr (hA a ha)
  have hLker : L ≤ (actionHom ρ).ker := by
    rw [← hL]
    exact (Subgroup.commutator_mono le_rfl hker).trans (Subgroup.commutator_le_right _ _)
  intro g hg
  exact (actionHom_eq_one_iff ρ g).mp ((sup_le hker hLker) hg)

end Representation.BinaryOffender
