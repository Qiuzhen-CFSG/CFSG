module
public import Theory.SpecificGroups.AffineEight.TransferGeometry
public import Theory.GroupTheory.SylowTransferVanishing

/-!
# A self-normalizing affine-eight Sylow prevents perfectness

If a finite group has a self-normalizing Sylow two-subgroup actually
isomorphic to the affine group of the cyclic group of order eight, its
derived subgroup is proper. The supplied isomorphism transports the
coefficient-five involution and the translation-four line, including every
index-two subgroup and its commutator subgroup, into the actual Sylow.
The maximal-transfer-vanishing theorem then places this involution outside
the ambient derived group.

This is the group-language transfer obstruction from Andersen–Oliver–Ventura,
Fusion systems and amalgams, Math. Z.274 (2013), Proposition2.3(b), applied
to the proved explicit affine model. It does not assume that the fusion
system of a simple group is reduced and does not use a global classification.
-/

namespace AffineEight
open scoped commutatorElement

public theorem not_perfect_of_sylow
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hN : Subgroup.normalizer (S : Set G) = (S : Subgroup G))
    (e : S ≃* AffineEight.Model) : commutator G ≠ ⊤ := by
  classical
  let t₀ : AffineEight.Model := SemidirectProduct.inr AffineEight.five
  let z₀ : AffineEight.Model :=
    SemidirectProduct.inl (Multiplicative.ofAdd (4 : ZMod 8))
  let U₀ : Subgroup AffineEight.Model := Subgroup.zpowers z₀
  let t : S := e.symm t₀
  let U : Subgroup S := U₀.comap e.toMonoidHom
  obtain ⟨hnot, hsquare, hcomm, hmax⟩ := AffineEight.transfer_obstruction_data
  have ht : t ∉ commutator S := by
    intro h
    apply hnot
    have hm : e t ∈ (commutator S).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem _ h
    rw [map_commutator_eq, e.toMonoidHom.range_eq_top_of_surjective e.surjective,
      ← commutator_def] at hm
    simpa only [t, MulEquiv.apply_symm_apply] using hm
  have hsq : t ^ 2 ∈ U := by
    change e (t ^ 2) ∈ U₀
    simpa only [map_pow, t, MulEquiv.apply_symm_apply] using hsquare
  have hc (v : S) : ⁅t, v⁆ ∈ U := by
    change e ⁅t, v⁆ ∈ U₀
    simpa only [map_commutatorElement, t, MulEquiv.apply_symm_apply] using hcomm (e v)
  have hm (M : Subgroup S) (hM : M.index = 2) : U ≤ ⁅M, M⁆ := by
    intro x hx
    have hindex : (M.map e.toMonoidHom).index = 2 := by
      exact (Subgroup.index_map_of_bijective
        (f := e.toMonoidHom) e.bijective M).trans hM
    have he : e x ∈ ⁅M.map e.toMonoidHom, M.map e.toMonoidHom⁆ :=
      hmax _ hindex hx
    rw [← Subgroup.map_commutator] at he
    obtain ⟨y, hy, hxy⟩ := he
    exact (e.injective hxy) ▸ hy
  intro hperfect
  apply S.not_mem_commutator_of_maximal_transfer_vanishing hN t U ht hsq hc hm
  rw [hperfect]
  trivial

end AffineEight
