module

public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# The literal carriers in the diagonal endgame

These are J=KL₊T, W=R₂(J), and W_K=[W,K] from the paragraph between
reductions (f) and (g) in Lemma 13.3.14. R₂ is the join of reduced normal
elementary abelian subgroups, not a rank-two condition.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.892.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The original local group J. -/
def localGroup (K A T : Subgroup G) : Subgroup G := (K ⊔ A) ⊔ T

/-- W=R₂(J), embedded through the actual subtype. -/
def reducedModule (K A T : Subgroup G) : Subgroup G :=
  (reducedTwoSubgroup (localGroup K A T)).map (localGroup K A T).subtype

/-- The original module W_K=[R₂(J),K]. -/
def movedModule (K A T : Subgroup G) : Subgroup G := ⁅reducedModule K A T, K⁆

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
