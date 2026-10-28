module
public import Theory.GroupAction.MaximalCosetOrbit
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Two generators of the image of a hyperplane pair

A homomorphism killing an index-two subgroup is generated on the original
module by the image of any element outside that subgroup. Applying this to
the two modules keeps the pair range literal, without a replacement model.
-/
public section
namespace Subgroup
variable {G K : Type*} [Group G] [Group K]

/-- An index-two seed killed by an action leaves a single original generator. -/
theorem image_eq_zpowers_of_index_two (V W : Subgroup G) (f : G →* K)
    (hWV : W ≤ V) (hi : W.relIndex V = 2) (hk : W ≤ f.ker)
    (v : G) (hv : v ∈ V) (hvw : v ∉ W) : V.map f = zpowers (f v) := by
  have hs := sup_zpowers_eq_of_relIndex_prime hWV Nat.prime_two hi hv hvw
  have hh := congrArg (fun A : Subgroup G => A.map f) hs
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,
    (Subgroup.map_eq_bot_iff (f := f) W).mpr hk,bot_sup_eq] at hh
  exact hh.symm

/-- Equal kernels give a canonical equivalence between the literal images. -/
noncomputable def rangeEquivOfKerEq {J : Type*} [Group J]
    (f : G →* K) (g : G →* J) (hk : f.ker = g.ker) : f.range ≃* g.range :=
  (QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivRange g))
end Subgroup
