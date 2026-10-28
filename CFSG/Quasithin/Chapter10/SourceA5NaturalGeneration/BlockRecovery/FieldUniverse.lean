module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BlockRecovery.Original
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Data.Fintype.Shrink
/-!
# Natural block recovery from a field in any universe

The intrinsic block-type predicate stores its finite field in Type. A
literal source section may use a larger universe. Transport the field to
its small copy, the special-linear quotient by the induced matrix map,
and the module coordinates coefficient by coefficient. Equivariance is
exactly preservation of matrix-vector multiplication. The original moved
section and central kernel are retained, so the intrinsic block recovery
applies without restricting the source theorem's field parameter.
Source: Aschbacher--Smith C.1.27 and 10.2.3(4), printed pp.133,746--747.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
variable {G : Type*} [Group G]
variable {F : Type*} [Field F] [CharP F 2]
local instance fieldUniverseNaturalBlockAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Finite-field shrinking preserves the literal marked natural section. -/
theorem source_natural_block_of_identified_moved_section_any_universe
    (K U : Subgroup G) (hK : ChapterC.IsShort K)
    (hmoved : (ChapterC.blockU K).map K.subtype = ⁅U,K⁆)
    (e : (K ⧸ pCore 2 K) ≃* SL(2,F)) (hF : Nat.card F = 4)
    (c : BinaryConjugationSection K ⁅U,K⁆ (⁅U,K⁆ ⊓ centralizer (K : Set G))
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) :
    ChapterC.IsL2EvenBlock K 2 := by
  let : Finite F := Nat.finite_of_card_ne_zero (hF ▸ (by decide : 4 ≠ 0))
  let k : F ≃+* Shrink.{0} F := (Shrink.ringEquiv.{0,_} F).symm
  let : CharP (Shrink.{0} F) 2 := (k.toRingHom.charP_iff_charP 2).mp inferInstance
  let : Algebra (ZMod 2) (Shrink.{0} F) := ZMod.algebra _ 2
  let : Module (ZMod 2) (Shrink.{0} F) := Algebra.toModule
  let j := Atlas.fieldEquivSL 2 k
  let v : (Fin 2 → F) ≃+ (Fin 2 → Shrink.{0} F) :=
    AddEquiv.piCongrRight (fun _ => k.toAddEquiv)
  let vm := v.toMultiplicative
  let d : BinaryConjugationSection K ⁅U,K⁆ (⁅U,K⁆ ⊓ centralizer (K : Set G))
      (SL2.BinarySmall.natural.comp
        ((e.trans j).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) := {
    section_le := c.section_le
    kernel_le := c.kernel_le
    normalized := c.normalized
    coordinates := vm.toMonoidHom.comp c.coordinates
    onto := vm.surjective.comp c.onto
    kernel_eq := by
      ext x
      change vm (c.coordinates x) = 1 ↔ _
      rw [vm.map_eq_one_iff]
      exact show x ∈ c.coordinates.ker ↔ _ from by rw [c.kernel_eq]
    equivariant := by
      intro g a
      apply funext
      intro i
      have he := congrFun (c.equivariant g a) i
      change k ((c.coordinates _).toAdd i) = _
      rw [he]
      change k (Matrix.mulVec (e (QuotientGroup.mk' (pCore 2 K) g)).val
          (c.coordinates a).toAdd i) =
        Matrix.mulVec ((e (QuotientGroup.mk' (pCore 2 K) g)).val.map k)
          (fun z => k ((c.coordinates a).toAdd z)) i
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply] }
  exact source_natural_block_of_identified_moved_section K U hK hmoved (e.trans j)
    ((Nat.card_congr k.toEquiv).symm.trans hF) d
end CFSG.Quasithin.Chapter10
