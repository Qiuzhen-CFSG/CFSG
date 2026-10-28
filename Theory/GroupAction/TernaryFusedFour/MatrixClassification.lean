module

public import Theory.GroupAction.TernaryFusedFour.MatrixClassification.Sieve
public import Theory.GroupAction.TernaryFusedFour.MatrixClassification.Twelve
public import Theory.SpecificGroups.PSL3Three.NodeExtensions

/-!
# Fused elementary Sylow two-subgroups in SL₃(3)

Every subgroup is conjugate to a node of the already certified exhaustive
extension enumeration. Exact small orders, explicit elements of order four,
and line-action characters eliminate every node except node 16. Its checked
list has twelve elements, and its square-one elements form a normal subgroup;
Sylow maximality then gives the required normality.

The input assumptions are exactly divisibility of the subgroup order by four,
elementary Sylow two-subgroups, and internal conjugacy of all involutions.
The transport lemmas use abstract isomorphisms so elaboration does not repeatedly
expand the concrete conjugation equivalence.

Source application: Bender, *Finite groups with large subgroups* (1974),
(4.1), printed p.225 (PDF page 3 of `refs/original/bender-large.pdf`), citing
Janko (1966), Lemma 3.1. The determinant and vector-space reduction is in
`TernaryFusedFour.Reduction`; transport back to automizers is owned by the parent
`TernaryFusedFour` module, which can import this theorem without a cycle.
-/

namespace TernaryFusedFour
open Matrix.PSL3Three Matrix.PSL3Three.CertifiedEnumeration
open MatrixClassification

private theorem local_conditions_of_equiv
    {G K : Type*} [Group G] [Finite G] [Group K] [Finite K] (e : G ≃* K)
    (hfour : 4 ∣ Nat.card G)
    (hel : ∀ P : Sylow 2 G, IsElementaryAbelian 2 P)
    (hfuse : ∀ t u : G, orderOf t = 2 → orderOf u = 2 → IsConj t u) :
    4 ∣ Nat.card K ∧ (∀ P : Sylow 2 K, IsElementaryAbelian 2 P) ∧
    (∀ t u : K, orderOf t = 2 → orderOf u = 2 → IsConj t u) := by
  refine ⟨(Nat.card_congr e.toEquiv) ▸ hfour, ?_, ?_⟩
  · intro Q
    obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective (f := e.toMonoidHom) e.surjective 2 Q
    let := hel P
    exact IsElementaryAbelian.map e.toMonoidHom
  · intro t u ht hu
    have hh := e.toMonoidHom.map_isConj (hfuse (e.symm t) (e.symm u)
      ((e.symm.orderOf_eq t).trans ht) ((e.symm.orderOf_eq u).trans hu))
    change IsConj (e (e.symm t)) (e (e.symm u)) at hh
    simpa only [MulEquiv.apply_symm_apply] using hh

private theorem result_of_equiv
    {G K : Type*} [Group G] [Finite G] [Group K] [Finite K] (e : G ≃* K)
    (h : Nat.card K = 12 ∧ ∀ P : Sylow 2 K, (P : Subgroup K).Normal) :
    Nat.card G = 12 ∧ ∀ P : Sylow 2 G, (P : Subgroup G).Normal := by
  refine ⟨(Nat.card_congr e.toEquiv).trans h.1, ?_⟩
  intro P
  exact MulEquiv.normal_map_iff.mp (h.2 (P.mapSurjective (f := e.toMonoidHom) e.surjective))

private theorem node_result (i : Fin 51)
    (hfour : 4 ∣ Nat.card (node i))
    (hel : ∀ P : Sylow 2 (node i), IsElementaryAbelian 2 P)
    (hfuse : ∀ t u : node i, orderOf t = 2 → orderOf u = 2 → IsConj t u) :
    Nat.card (node i) = 12 ∧ ∀ P : Sylow 2 (node i), (P : Subgroup (node i)).Normal := by
  have hi : i = 16 := eligible_node_eq_sixteen i hfour
    (no_order_four_of_elementary_sylow hel) hfuse
  subst i
  exact ⟨card_properNode16, normal_sylow_properNode16 hel⟩

/-- A ternary special linear subgroup with elementary Sylow two-subgroups,
order divisible by four, and one internal involution class has order twelve
and normal Sylow two-subgroups. -/
public theorem specialLinear_card_and_normal_sylow
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)))
    (hfour : 4 ∣ Nat.card H)
    (hel : ∀ P : Sylow 2 H, IsElementaryAbelian 2 P)
    (hfuse : ∀ t u : H, orderOf t = 2 → orderOf u = 2 → IsConj t u) :
    Nat.card H = 12 ∧ ∀ P : Sylow 2 H, (P : Subgroup H).Normal := by
  obtain ⟨i, g, hg⟩ := node_extensionClosed.complete node H
  let e : H ≃* node i :=
    (H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hg)
  obtain ⟨hfour', hel', hfuse'⟩ := local_conditions_of_equiv e hfour hel hfuse
  exact result_of_equiv e (node_result i hfour' hel' hfuse')

end TernaryFusedFour
