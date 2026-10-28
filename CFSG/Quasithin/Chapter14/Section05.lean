module

public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Elementary closure reduction in the abelian case of §14.5

In Hypothesis 14.5.1, `V` is elementary abelian and its normal closure in `G₁`
is abelian. Consequently the same holds for the normal closure inside each
subgroup `H` containing `V`, as required in Lemma 14.5.15(2).

Here the ambient type represents `G₁`. The local closure is formed in the
actual subgroup `H` and mapped back by its inclusion. It is contained in the
ambient normal closure by the universal property, so it inherits elementary
abelianness. The statement also applies to `V ∩ H` when `V` is not contained
in `H`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §14.5, printed pp.1013 and 1017.
-/

namespace CFSG.Quasithin.Chapter14.Section05

/-- The elementary abelianness assertion used for `U_H` in Lemma 14.5.15(2),
with the local normal closure expressed as an actual ambient subgroup. -/
public theorem elementaryAbelian_localClosure {G : Type*} [Group G] (V H : Subgroup G)
    [IsElementaryAbelian 2 V]
    [IsMulCommutative (Subgroup.normalClosure (V : Set G))] :
    IsElementaryAbelian 2
      ((Subgroup.normalClosure (V.subgroupOf H : Set H)).map H.subtype) := by
  let := IsElementaryAbelian.normalClosure_of_isMulCommutative (p := 2) V
  apply IsElementaryAbelian.of_le (B := Subgroup.normalClosure (V : Set G))
  apply Subgroup.map_le_iff_le_comap.mpr
  apply Subgroup.normalClosure_le_normal
  intro x hx
  exact Subgroup.le_normalClosure hx

end CFSG.Quasithin.Chapter14.Section05
