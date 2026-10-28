module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Contracts

/-!
# Restriction of the dihedral degree theorem

An injectively embedded direct product acts faithfully on any faithful
ambient module. Hence the uniform degree theorem applies directly, with
the same vector space and dimensions. This bridge is used by the G.9.2
assembly and leaves the uniform representation theorem explicit.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

universe u v

variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem dihedralLowerBounds_of_uniform (bounds : DihedralDegreeTheorem.{v})
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ) :
    HasDihedralLowerBounds ρ := by
  intro r D
  exact bounds V r D.prime D.prime_isPrime D.prime_odd (ρ.comp D.embedding)
    (hfaith.comp D.injective)

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
