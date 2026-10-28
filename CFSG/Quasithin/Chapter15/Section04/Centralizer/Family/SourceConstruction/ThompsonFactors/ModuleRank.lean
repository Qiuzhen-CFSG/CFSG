module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.Basic
public import Theory.Representation.BinaryOffender.CubicMovedRank
public import Theory.Representation.BinaryGroupAction

/-!
# The literal binary modules moved by the Thompson cubics

The supplied representation is faithful because it is the conjugation action
of the actual centralizer quotient. Each cubic factor therefore moves at least
two binary dimensions. Its moved space is contained in its original natural
plane, so equality follows. The internal B.2.16 module sum makes distinct
planes disjoint. A selected product of one or two cubics consequently moves
exactly the corresponding internal sum, of dimension twice the factor count.

Source: Aschbacher–Smith B.2.16 and 15.4.12(3), printed pp.79 and1160–1161.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
open Chapter1.RadicalNormalizers.ThompsonSource
variable {H : Type*} [Group H] {S : Sylow 2 H}
  [IsElementaryAbelian 2 (closure S)]

/-- The literal centralizer quotient acts faithfully by the supplied conjugation action. -/
theorem representation_injective (d : Exceptional S) : Function.Injective d.representation := by
  apply (MonoidHom.ker_eq_bot_iff d.representation).mp
  apply bot_unique
  intro x hx
  obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (closure S : Set H)) x
  apply (QuotientGroup.eq_one_iff h).mpr
  intro v hv
  have hh := d.conjugation h ⟨v,hv⟩
  change d.representation (starMap (closure S) h) = 1 at hx
  rw [hx] at hh
  change v = h*v*h⁻¹ at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm

@[expose] def plane (d : Exceptional S) (i : Fin d.count) :
    Submodule (ZMod 2) (Additive (closure S)) :=
  subspaceCommutator d.representation ⊤ (d.factor i)

theorem plane_finrank (d : Exceptional S) (i : Fin d.count) :
    Module.finrank (ZMod 2) (plane d i) = 2 := by
  change Module.finrank (ZMod 2) (subspaceCommutator d.representation ⊤ (d.factor i)) = _
  rw [(d.naturalEquiv i).finrank_eq]
  simp

theorem planes_disjoint (d : Exceptional S) {i j : Fin d.count} (hij : i ≠ j) :
    Disjoint (plane d i) (plane d j) := by
  classical
  apply Submodule.disjoint_def.mpr
  intro v hi hj
  have he : d.moduleSum (0,Pi.single i ⟨v,hi⟩) =
      d.moduleSum (0,Pi.single j ⟨v,hj⟩) := by
    exact (d.moduleSum_single i ⟨v,hi⟩).trans (d.moduleSum_single j ⟨v,hj⟩).symm
  have hh := congrFun (congrArg Prod.snd (d.moduleSum.injective he)) i
  have hv : (⟨v,hi⟩ : subspaceCommutator d.representation ⊤ (d.factor i)) = 0 := by
    simpa only [Pi.single_eq_same, Pi.single_eq_of_ne hij] using hh
  exact congrArg Subtype.val hv

private theorem moved_sup (d : Exceptional S) (A B : Subgroup (Star (S := S))) :
    subspaceCommutator d.representation ⊤ (A ⊔ B) =
      subspaceCommutator d.representation ⊤ A ⊔ subspaceCommutator d.representation ⊤ B := by
  simpa only [iSup_bool_eq, Bool.false_eq_true, ↓reduceIte] using
    BinaryGroupAction.moved_iSup d.representation (fun b : Bool => if b then A else B)

private theorem moved_bot (d : Exceptional S) : subspaceCommutator d.representation ⊤ ⊥ = ⊥ := by
  apply (subspaceCommutator_eq_bot_iff _ _ _).mpr
  rw [fixedSpace_bot]

variable [Finite H]

/-- Each actual cubic moves precisely its original natural plane. -/
theorem cubic_moved_eq_plane (d : Exceptional S) (i : Fin d.count) :
    subspaceCommutator d.representation ⊤ (cubicFactor d i) = plane d i := by
  let : FiniteDimensional (ZMod 2) (Additive (closure S)) := Module.Finite.of_finite
  have hle : subspaceCommutator d.representation ⊤ (cubicFactor d i) ≤ plane d i := by
    apply Submodule.span_mono
    rintro _ ⟨a,ha,v,hv,rfl⟩
    exact ⟨a,cubicFactor_le d i ha,v,hv,rfl⟩
  apply Submodule.eq_of_le_of_finrank_eq hle
  apply le_antisymm (Submodule.finrank_mono hle)
  rw [plane_finrank]
  exact two_le_finrank_subspaceCommutator_of_card_three d.representation _
    (representation_injective d) (cubicFactor_card d i)

/-- The selected cubic product moves the internal sum of the selected natural planes. -/
theorem cubicProduct_moved (d : Exceptional S) (I : Finset (Fin d.count)) :
    subspaceCommutator d.representation ⊤ (cubicProduct d I) = I.sup (plane d) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact moved_bot d
  | @insert i I hi ih =>
    simp only [cubicProduct, Finset.sup_insert] at ih ⊢
    rw [moved_sup, cubic_moved_eq_plane, ih]

/-- The literal one- or two-factor moved module has binary dimension twice its factor count. -/
theorem cubicProduct_moved_finrank (d : Exceptional S) (I : Finset (Fin d.count))
    (hI : I.card = 1 ∨ I.card = 2) :
    Module.finrank (ZMod 2) (subspaceCommutator d.representation ⊤ (cubicProduct d I)) =
      2 * I.card := by
  classical
  let : FiniteDimensional (ZMod 2) (Additive (closure S)) := Module.Finite.of_finite
  rw [cubicProduct_moved]
  rcases hI with hI | hI
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hI
    rw [Finset.card_singleton, mul_one]
    have hs : ({i} : Finset (Fin d.count)).sup (plane d) = plane d i := Finset.sup_singleton
    exact (congrArg (fun U : Submodule (ZMod 2) (Additive (closure S)) =>
      Module.finrank (ZMod 2) U) hs).trans (plane_finrank d i)
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hI
    rw [Finset.sup_insert, Finset.sup_singleton]
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (plane d i) (plane d j)
    rw [(planes_disjoint d hij).eq_bot, finrank_bot, add_zero, plane_finrank, plane_finrank] at hdim
    rw [hdim, Finset.card_pair hij]

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
