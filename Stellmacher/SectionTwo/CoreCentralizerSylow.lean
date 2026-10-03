module

public import Theory.GroupTheory.PGroup.NormalCoreSylow
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Core-centralizer equality gives relative Sylow control

Suppose `V` and `E` are normal in a finite group and
`O₂(G) = S ∩ C_G(V)` for an ambient Sylow two-subgroup `S`.
Then `O₂(E)` is a Sylow two-subgroup of the relative centralizer
`C_G(V).subgroupOf E`. No containment `V ≤ E` is required.

The centralizer of the normal subgroup `V` is normal, so its intersection
with `S` is Sylow there. The displayed equality identifies this Sylow's
ambient image with `O₂(G)`. The normal-core Sylow restriction theorem then
transfers this control to `E`. This is the centralizer Sylow input to the
noncentralizing case of Stellmacher (2.3), journal p.20, following
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionTwo

public theorem twoCore_sylow_centralizer_of_core_equality
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (V E : Subgroup G)
    [V.Normal] [E.Normal]
    (hcore : pCore 2 G = (S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) :
    ∃ T : Sylow 2 ((Subgroup.centralizer (V : Set G)).subgroupOf E),
      (T : Subgroup ((Subgroup.centralizer (V : Set G)).subgroupOf E)).map
        ((Subgroup.centralizer (V : Set G)).subgroupOf E).subtype = pCore 2 E := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply pCore_sylow_restrict_normal 2 E (Subgroup.centralizer (V : Set G))
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal (Subgroup.centralizer (V : Set G))
  refine ⟨T, ?_⟩
  rw [hT, hcore]
  exact Subgroup.subgroupOf_map_subtype _ _

end Stellmacher.SectionTwo
