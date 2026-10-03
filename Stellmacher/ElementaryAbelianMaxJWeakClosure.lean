module

public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# Weak closure of the elementary Thompson subgroup

If an ambient automorphism sends J(S) into S, it sends J(S) onto itself.
In particular J(S) is weakly closed in S under ambient conjugation. This
is the subgroup-control input for the Frattini argument in Stellmacher
(2.2), Journal of Algebra 190 (1997), p.20, in
`refs/latex/stellmacher-n-group.tex`.

The maximum elementary-abelian order is unchanged by automorphisms.
The proved comparison from containment of J(e(S)) in S therefore gives
J(e(S)) ≤ J(S). Automorphism transport of J and equality of finite subgroup
orders turn this containment into equality. No Sylow hypothesis is needed.
-/

namespace Stellmacher
universe u

public theorem elementaryAbelianMaxJ_map_eq_of_le
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (e : G ≃* G)
    (hle : (elementaryAbelianMaxJ S).map e.toMonoidHom ≤ S) :
    (elementaryAbelianMaxJ S).map e.toMonoidHom = elementaryAbelianMaxJ S := by
  have hJle : elementaryAbelianMaxJ (S.map e.toMonoidHom) ≤ S := by
    rwa [elementaryAbelianMaxJ_map_equiv]
  have hinc := (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le
    (S.map e.toMonoidHom) S hJle).2 (elementaryAbelianMaxOrder_map_equiv e S)
  rw [elementaryAbelianMaxJ_map_equiv] at hinc
  apply Subgroup.eq_of_le_of_card_ge hinc
  rw [Subgroup.card_map_of_injective e.injective]

end Stellmacher
