module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.ParabolicCover
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups

/-!
# E-generation from the actual G₂ parabolic overgroups

The two transported parabolics joined with T generate the ambient group.
Apply the proved restriction and inheritance of E-members to each overgroup;
their intrinsic E-generation puts both in the ambient generation target.
Thus the local generation calculations suffice even in an outer extension.

This is the concrete G₂ application of Aschbacher--Smith E.1.12, printed
p.214. The local generation premise is discharged for the binary case in
`BinaryUpper`; its nonbinary discharge remains a separate calculation.
-/

public section
open Subgroup Atlas.G2
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

theorem isEGenerated_of_parabolicOvergroups {n : ℕ}
    (L : Subgroup G) (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (hLT : L ⊔ (T : Subgroup G) = ⊤)
    (hlocal : ∀ i : Fin 2, IsEGenerated n (parabolicOvergroup L T e i)) :
    IsEGenerated n G := by
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget n T Ω
  rw [← parabolicOvergroups_generate L (T : Subgroup G) e hLT]
  apply sSup_le
  rintro H ⟨i, rfl⟩
  exact ChiefOrbit.overgroup_le_generationTarget T _ (le_parabolicOvergroup L T e i)
    hΩ (hlocal i)

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2
