module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Products
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.NaturalConstituents
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity

/-!
# The original B.5.1 moved space is in Irr⁺ under a plane bound

An offender whose entire moved space has dimension at most two excludes the
doubled and natural-dual rows. In the repeated row it forces one natural copy,
which is itself irreducible and faithful. Thus every genuine B.5.1 source row
gives Irr⁺ on the original moved space, before passing to a central quotient.
The remaining actor catalogue is exactly the irreducible B.4.2 list together
with binary SL4 and SL5, preserving all literal source representations.

Source: Aschbacher–Smith 13.7.15(1–2), printed pp.943–944.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
open SourceInduction.ProjectiveLine
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private noncomputable def repeatedOneEquiv
    {D X : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) D X) : ActionEquiv (repeated σ 1) σ where
  groupEquiv := MulEquiv.refl _
  linearEquiv :=
    { toFun := fun v => v 0
      invFun := fun x _ => x
      left_inv := fun v => funext fun _ => congrArg v (Subsingleton.elim _ _)
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  intertwines _ _ := rfl

/-- The exact B.5.1 row reduction on the original moved section. -/
theorem source_irreducible_or_binary_of_plane
    {A L : Subgroup G} (hA : IsOffender ρ A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2)
    (s : MovedSection ρ L) (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) :
    (IsIrrPlus ρ L s.space.toSubmodule ∧
      Function.Injective (s.central.quotientRepresentation) ∧
      IsIrreducible (s.central.quotientRepresentation.comp L.subtype) ∧
      SourceInduction.ProjectiveLine.IrreducibleActionCase s.central.quotientRepresentation L
        (offenderSubgroup s.central.quotientRepresentation)) ∨
    ∃ n, (n = 4 ∨ n = 5) ∧
      IsLinearNatural (s.space.toRepresentation.comp L.subtype) BinaryField.two n := by
  cases hc with
  | irreducible hi hf hr hs _ => exact Or.inl ⟨hi,hf,hr,hs⟩
  | doubleThree F whole e _ _ =>
    have hh := repeated_multiplicity_le_one ρ (linearNatural F 3)
      (linearNatural_faithful F 3) s.space (actionOfWhole (repeated (linearNatural F 3) 2) whole e) hA hd
    omega
  | naturalDual n _ whole he =>
    obtain ⟨e⟩ := he
    have hf := linearNatural_faithful BinaryField.two n
    exact (not_product_section ρ (linearNatural BinaryField.two n)
      (linearNatural BinaryField.two n).dual hf (faithful_dual _ hf) s.space
      (actionOfWhole (naturalPlusDual n) whole e) hA hd).elim
  | repeatedNatural n r hn hr _ whole he =>
    obtain ⟨e⟩ := he
    have hh := repeated_multiplicity_le_one ρ (linearNatural BinaryField.two n)
      (linearNatural_faithful BinaryField.two n) s.space
      (actionOfWhole (repeated (linearNatural BinaryField.two n) r) whole e) hA hd
    have hr1 : r = 1 := by omega
    subst r
    let e₁ := repeatedOneEquiv (linearNatural BinaryField.two n)
    exact Or.inr ⟨n,hn,⟨⟨e.groupEquiv,e.linearEquiv.trans e₁.linearEquiv,
      fun g v => (congrArg e₁.linearEquiv (e.intertwines g v)).trans
        (e₁.intertwines (e.groupEquiv g) (e.linearEquiv v))⟩⟩⟩

/-- This discharges the non-Irr⁺ alternatives in 13.7.15(2), including the
multiplicity-one endpoint retained by the complete B.5.1 contract. -/
theorem source_irrPlus_of_plane
    {A L : Subgroup G} [IsQuasisimple L] (hA : IsOffender ρ A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2)
    (s : MovedSection ρ L) (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) :
    IsIrrPlus ρ L (moved ρ L) := by
  rw [← s.space_eq]
  rcases source_irreducible_or_binary_of_plane ρ hA hd s hc with hi | ⟨n,hn,⟨e⟩⟩
  · exact hi.1
  · let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    let W : Subrepresentation (ρ.comp L.subtype) :=
      ⟨s.space.toSubmodule, fun l v hv => s.space.apply_mem_toSubmodule l hv⟩
    have hir : IsIrreducible W.toRepresentation :=
      ExtensionConsequences.irreducible_of_equiv e
        (ExtensionConsequences.linearNatural_irreducible BinaryField.two
          (by rcases hn with rfl | rfl <;> decide))
    have hf : Function.Injective W.toRepresentation := by
      intro a b hab
      apply e.groupEquiv.injective
      apply linearNatural_faithful BinaryField.two n
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
      rw [← e.intertwines, ← e.intertwines]
      exact congrArg e.linearEquiv (LinearMap.congr_fun hab w)
    exact SourceCompletion.constituent_isIrrPlus ρ L W hir hf
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
