module

public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers
public import Theory.Mathieu.M24.LocalGeometry.SextetCore

/-!
# The native sextet-core input for H.14

The native calculation identifies the intrinsic two-core of the literal
standard sextet stabilizer with the transported Sylow elementary candidate.
It supplies the previously explicit `NativeSextetCoreData` contract and the
order-64 elementary structure of the chapter's actual `sextetKernel`.

Source: Aschbacher–Smith H.14.1, printed pp.396–397. The remaining stabilizer
classification and common-four assertions retain their own source obligations.
-/

public section
namespace CFSG.Quasithin.ChapterH.Section13To16
open Sporadic.Mathieu.M24LocalGeometry

/-- Unconditional native sextet-core data, with all structural fields proved. -/
noncomputable def nativeSextetCoreData : NativeSextetCoreData where
  kernel := SextetCore.core
  kernel_le_stabilizer := SextetCore.core_le_stabilizer
  kernel_elementary := SextetCore.core_ambient_elementary
  kernel_card := SextetCore.core_ambient_card
  kernel_eq_pCore := rfl

/-- The chapter's literal sextet kernel is elementary abelian of order 64. -/
theorem standardSextet_kernel_structure :
    IsElementaryAbelian 2 (sextetKernel standardSextet) ∧
      Nat.card (sextetKernel standardSextet) = 64 :=
  ⟨SextetCore.core_ambient_elementary, SextetCore.core_ambient_card⟩

end CFSG.Quasithin.ChapterH.Section13To16
