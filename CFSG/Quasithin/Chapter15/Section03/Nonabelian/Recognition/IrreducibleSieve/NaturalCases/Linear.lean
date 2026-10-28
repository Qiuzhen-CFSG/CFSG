module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases.Defs
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases.Quadratic
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# Excluding the natural SL₂ and SL₃ modules

Both actual matrix groups are transitive on nonzero columns. Scalar restriction
preserves this orbit statement, while the source invariant nonsingular binary
quadratic form rules it out. Thus every valid field parameter is excluded
directly, without a bound on the marked involution's field automorphism.

Source: Aschbacher--Smith, G.9.3(6),(8) and 15.3.58, printed pp.354,1149.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

open Representation
open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
attribute [local instance] ZMod.algebra

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X : Subgroup H} {T : Sylow 2 H} {v : H} {s : ℕ}
  {F : Type*} [Field F] [CharP F 2]

/-- G.9.3(6) is incompatible with the source quadratic form. -/
theorem SourceData.not_natural_rankOne (h : SourceData ρ X T v s) (K : Subgroup H) :
    ¬ Quasiequivalent (ρ.comp K.subtype) (SL2.BinarySmall.natural (K := F)) :=
  h.not_nonzero_transitive_model K _ (fun x y hx hy =>
    Matrix.SL2.exists_mulVec_eq F x y hx hy)

/-- G.9.3(8) is excluded for SL₃ itself, including its central covers. -/
theorem SourceData.not_natural_linearThree (h : SourceData ρ X T v s) (K : Subgroup H) :
    ¬ Quasiequivalent (ρ.comp K.subtype) (LinearThreeRecognition.naturalBinary F) :=
  h.not_nonzero_transitive_model K _ (fun x y hx hy =>
    Matrix.SpecialLinearGroup.exists_mulVec_eq_three x y hx hy)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
