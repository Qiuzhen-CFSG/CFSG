module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.ParabolicGeometry
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility

/-!
# End-parabolic irreducibility from the binary Curtis input

The actual opposite-parabolic geometry discharges all four subgroup and
quotient premises of the Smith–Timmesfeld application. Only the unique
opposite fixed line and upper-unipotent cyclicity of the dual module remain
as the mathematical input, over the original binary field.

Source: GLS, Volume 3, Theorem 2.8.11, `refs/KGroup/GLS3/chapter2.tex`,
printed pp.95–96; Guralnick–Malle, Classification of 2F-modules II,
Theorem 3.1 and Proposition 4.7(2).
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi
open Representation Irreducibility

/-- The literal end-node quotient action is irreducible once Curtis's binary
fixed-line and cyclicity theorem is supplied for the dual representation. -/
theorem action_irreducible_of_curtis
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (e : Fin 2) (hc : CurtisInput σ.dual) : IsIrreducible (action σ e) :=
  action_irreducible_of_unipotent_inputs σ e hc
    (radicalImage_le_upper e) (upper_le_radicalImage_sup_leviSubgroup e)
    (lower_le_oppositeRadical_sup_leviSubgroup e) (leviToQuotient_surjective e)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi
