module

public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Theory.SpecificGroups.DihedralSolvable
/-!
# Solvability of involution centralizers in odd PSL₂

The actual reflected cyclic torus presents the centralizer as a dihedral
group. This is the local solvability input in the odd-field source branch
of Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2
/-- The reflected torus makes every involution centralizer solvable. -/
theorem involution_centralizer_isSolvable
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (t : PSL2 F) (ht : IsInvolution t) :
    Group.IsSolvable (centralizer ({t} : Set (PSL2 F))) := by
  obtain ⟨R, s, hR, _, hs, hsR, hi, hc, _⟩ := psl2_reflected_torus_card hF ht
  obtain ⟨d⟩ := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted R s hR hs.2 hsR hi
  rw [hc]
  let := GLS3.Chapter5.dihedralGroup_isSolvable (Nat.card R)
  exact Group.isSolvable_of_isSolvable_injective (f := d.toMonoidHom) d.injective
end Theory.PSL2
