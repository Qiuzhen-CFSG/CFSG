module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.ElementaryAbelian.Basic

/-!
# Transport of a residual action moving a marked point

An isomorphism of acting groups preserves residual membership, subgroup
normalizers, elementary eights, and the actual conjugation action. These
lemmas apply to an isomorphism of either parabolic itself; they require no
extension of that isomorphism to an ambient group.

Application: Aschbacher–Smith, Lemma 14.2.21, printed p.988.
-/

namespace Subgroup
variable {G G' : Type*} [Group G] [Group G']

public theorem map_residual_moving_point (e : G ≃* G') (E : Subgroup G)
    (z : G) (hz : z ∈ E) (y : G) (hy : y ∈ pResidual 2 G)
    (hn : y ∈ Subgroup.normalizer (E : Set G)) (hm : y * z * y⁻¹ ≠ z) :
    e z ∈ E.map e.toMonoidHom ∧ e y ∈ pResidual 2 G' ∧
      e y ∈ Subgroup.normalizer (E.map e.toMonoidHom : Set G') ∧
      e y * e z * (e y)⁻¹ ≠ e z := by
  refine ⟨⟨z, hz, rfl⟩, ?_, ?_, ?_⟩
  · rw [← map_pResidual 2 e]
    exact ⟨y, hy, rfl⟩
  · exact le_normalizer_map e.toMonoidHom ⟨y, hn, rfl⟩
  · intro h
    apply hm
    apply e.injective
    simpa only [map_mul, map_inv] using h

public theorem map_conjugation_equivariant (e : G ≃* G') (E : Subgroup G)
    (y : Subgroup.normalizer (E : Set G)) (x : E) :
    (e.subgroupMap E) (E.normalizerMonoidHom y x) =
      (E.map e.toMonoidHom).normalizerMonoidHom
        ⟨e y, le_normalizer_map e.toMonoidHom ⟨y, y.property, rfl⟩⟩
        (e.subgroupMap E x) := by
  apply Subtype.ext
  change e ((y : G) * (x : G) * (y : G)⁻¹) =
    e (y : G) * e (x : G) * (e (y : G))⁻¹
  simp only [map_mul, map_inv]

public theorem map_elementary_eight (e : G ≃* G') (E : Subgroup G)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) :
    IsElementaryAbelian 2 (E.map e.toMonoidHom) ∧
      Nat.card (E.map e.toMonoidHom) = 8 := by
  refine ⟨IsElementaryAbelian.map e.toMonoidHom, ?_⟩
  exact (Nat.card_congr (e.subgroupMap E).toEquiv).symm.trans hE

/-- Compatible isomorphisms of the two parabolics give the same ambient image
of every marked subgroup of their common subgroup. In particular, a core,
elementary subgroup, or distinguished line lying in that common subgroup can
be transported using either parabolic without changing its embedding. -/
public theorem pair_map_eq_of_compatible (H A T : Subgroup G) (H' A' : Subgroup G')
    (hTH : T ≤ H) (hTA : T ≤ A) (eH : H ≃* H') (eA : A ≃* A')
    (hcompat : ∀ t : T,
      (eH ⟨t, hTH t.property⟩ : G') = (eA ⟨t, hTA t.property⟩ : G'))
    (E : Subgroup G) (hET : E ≤ T) :
    ((E.subgroupOf H).map eH.toMonoidHom).map H'.subtype =
      ((E.subgroupOf A).map eA.toMonoidHom).map A'.subtype := by
  ext x
  constructor
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨eA ⟨v, hTA (hET hv)⟩, ⟨⟨v, hTA (hET hv)⟩, hv, rfl⟩, ?_⟩
    exact (hcompat ⟨v, hET hv⟩).symm
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨eH ⟨v, hTH (hET hv)⟩, ⟨⟨v, hTH (hET hv)⟩, hv, rfl⟩, ?_⟩
    exact hcompat ⟨v, hET hv⟩

end Subgroup
