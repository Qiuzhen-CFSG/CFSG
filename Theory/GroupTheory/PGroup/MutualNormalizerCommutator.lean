module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Commutators with a mutually normalizing p-subgroup

If X and a p-subgroup R normalize one another, [X,R] is a normal
p-subgroup of X, hence lies in O_p(X). Normalization supplies the two
containments, and the intrinsic normal subgroup is mapped back into the
ambient group. This is the final step of Aschbacher–Smith A.4.2(3),
*The Classification of Quasithin Groups*, printed p. 57.
-/

namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ}
/-- Mutual normalization puts the commutator in the embedded p-core of X. -/
public theorem commutator_le_pCore_of_mutual_normalization (X R : Subgroup G)
    (hR : IsPGroup p R)
    (hXR : X ≤ normalizer (R : Set G))
    (hRX : R ≤ normalizer (X : Set G)) :
    ⁅X, R⁆ ≤ (pCore p X).map X.subtype := by
  have hleft : ⁅X, R⁆ ≤ X := le_normalizer_iff_commutator_le_left.mp hRX
  have hright : ⁅X, R⁆ ≤ R := le_normalizer_iff_commutator_le_right.mp hXR
  have hn : (⁅X, R⁆.subgroupOf X).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left X R)
  have hp : IsPGroup p (⁅X, R⁆.subgroupOf X) := by
    let f : (⁅X, R⁆.subgroupOf X) →* R :=
      { toFun := fun x => ⟨x.val.val, hright x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hR.of_injective f (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun r : R => (r : G)) h)))
  have hc : ⁅X, R⁆.subgroupOf X ≤ pCore p X := le_sSup ⟨hn, hp⟩
  have := map_mono (f := X.subtype) hc
  rwa [map_subgroupOf_eq_of_le hleft] at this
end Subgroup
