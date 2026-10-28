module

public import Theory.GroupTheory.ElementFusionTransport

/-!
# Commuting conjugates from intersection fusion

Suppose the normalizer of `V` controls the fusion of `z` into `V`, and
`⟨V^{C_G(z)}⟩` is abelian. If a nontrivial intersection of `V` with a
conjugate lies in the normalizer orbit of `z`, the two subgroups commute.
We move a nonidentity intersection element to `z`, use the existing
centralizer-conjugator correction, and conjugate the commutator back.

This is the group-theoretic step in Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript (1 March 2004), Lemma 15.3.62(2),
printed p.1151. For a conjugator outside `M`, Lemma 15.3.46(2) makes the
intersection totally singular, the orthogonal action gives its orbit
condition, and Theorem 15.3.50 gives the abelian closure. The case of a
conjugator normalizing `V` uses the abelianness of `V` directly.
-/

namespace Subgroup

/-- Fusion control and abelian centralizer generation force intersecting
conjugates to commute, provided the intersection belongs to the specified orbit. -/
public theorem commutator_conjugate_eq_bot_of_intersection_fusion
    {G : Type*} [Group G] (V : Subgroup G) (z g : G)
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n z = MulAut.conj a z)
    [IsMulCommutative (centralizerConjugateClosure V z)]
    (hinter : V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥)
    (horbit : ∀ x ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom, x ≠ 1 →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x = z) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨x, hx⟩ := ne_bot_iff_exists_ne_one.mp hinter
  obtain ⟨n, hn, hnz⟩ := horbit x x.property (fun h => hx (Subtype.ext h))
  have hz : z ∈ V.map (MulAut.conj (n * g)).toMonoidHom := by
    obtain ⟨v, hv, hvg⟩ := x.property.2
    change MulAut.conj g v = (x : G) at hvg
    refine mem_map.mpr ⟨v, hv, ?_⟩
    change MulAut.conj (n * g) v = z
    calc
      MulAut.conj (n * g) v = MulAut.conj n (MulAut.conj g v) := by
        simp [MulAut.conj_apply, mul_assoc]
      _ = z := by rw [hvg, hnz]
  have hcomm := commutator_eq_bot_of_element_fusion_of_abelian_closure hfusion hz
  have hnV : V.map (MulAut.conj n).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have hcomp : (MulAut.conj (n * g)).toMonoidHom =
      (MulAut.conj n).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext a
    simp [MulAut.conj_apply, mul_assoc]
  have hmap : (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map
      (MulAut.conj n).toMonoidHom = ⊥ := by
    rw [map_commutator, hnV, map_map, ← hcomp]
    exact hcomm
  exact (map_eq_bot_iff_of_injective _ (MulAut.conj n).injective).mp hmap

end Subgroup
