module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import GorensteinWalter.PGL2DihedralSylow

/-!
# The maximal-overgroup alternatives needed in prime PGL₂

The placement argument needs only maximal subgroups containing a Sylow
two-subgroup. The expected alternatives are S₄ and full torus normalizers,
dihedral of order `2*(q-1)` or `2*(q+1)`. This definition retains actual group
isomorphisms; it does not assert that maximal subgroups have these shapes.
The prime-field maximal-subgroup calculation must supply that theorem.

Source: the Dickson subgroup classification, applied to the canonical PSL₂
intersection in the local calculation for Aschbacher--Smith E.1.14(6).
-/

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal

/-- The actual model alternatives used by the placement calculation. -/
@[expose] public def SylowOvergroupModel (F : Type*) [Field F]
    (M : Subgroup (GorensteinWalter.PGL2 F)) : Prop :=
  Nonempty (M ≃* Equiv.Perm (Fin 4)) ∨
    ∃ n : ℕ, (n = Nat.card F - 1 ∨ n = Nat.card F + 1) ∧
      Nonempty (M ≃* DihedralGroup n)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal
