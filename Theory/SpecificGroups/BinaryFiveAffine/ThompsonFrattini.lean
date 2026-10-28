module
public import Theory.SpecificGroups.BinaryFiveAffine.SylowInvolutions
public import Theory.Frattini.BinarySquares
/-!
# The marked pair involution lies in the Thompson Frattini subgroup

The pair involution is the square of an element in the standard Thompson
subgroup. The power criterion for finite two-groups places it in the
Frattini subgroup, retaining the literal affine mark.

Source: Aschbacher--Smith, 2.4.29, printed p.545.
-/
public section
open Subgroup Stellmacher
namespace BinaryFiveAffine

theorem t_mem_frattini_base : t∈(frattini sylowBase).map sylowBase.subtype := by
  have hle : sylowBase≤(standardSylow:Subgroup W) := by
    rw [←thompson_standardSylow]
    exact sSup_le fun _ h=>h.1
  let : Fact (IsPGroup 2 sylowBase) := ⟨standardSylow.isPGroup'.to_le hle⟩
  let x : sylowBase := ⟨sylowEmbedding pairSquareRoot,⟨pairSquareRoot,rfl,rfl⟩⟩
  have hx := pth_power_mem_frattini_of_isPGroup (p:=2) x
  exact ⟨x^2,hx,pairSquareRoot_square⟩
end BinaryFiveAffine
