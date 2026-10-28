module
public import Stellmacher.SectionFiveToSeven.Defs

/-!
# Transport of the ambient two-residual

For an ambient group automorphism, the two-residual of the image subgroup
is the image of the original two-residual. This supplies the residual
covariance needed when Stellmacher (8.4), journal p.39, transports the
residual-core noncontainment of (8.3) to a terminal edge.

The subgroup equivalence preserves normality and subgroup index. Its lattice
isomorphism therefore carries the defining infimum of normal subgroups of
two-power index to the corresponding infimum in the image subgroup. Composing
with the ambient subtype maps gives the stated equality. This argument uses
the existing residual definition and does not require the group to be finite.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

/-- Ambient two-residuals commute with transport by a group automorphism. -/
public theorem twoResidualIn_map_equiv
    {H : Type u} [Group H] (f : H ≃* H) (P : Subgroup H) :
    twoResidualIn (P.map f.toMonoidHom) = (twoResidualIn P).map f.toMonoidHom := by
  let e := P.equivMapOfInjective f.toMonoidHom f.injective
  have hsets : e.mapSubgroup '' {N : Subgroup P | N.Normal ∧ ∃ k : ℕ, N.index = 2 ^ k} =
      {N : Subgroup (P.map f.toMonoidHom) | N.Normal ∧ ∃ k : ℕ, N.index = 2 ^ k} := by
    apply Set.ext
    intro N
    constructor
    · rintro ⟨M, hM, rfl⟩
      change (M.map e.toMonoidHom).Normal ∧ ∃ k : ℕ, (M.map e.toMonoidHom).index = 2 ^ k
      obtain ⟨hMn, k, hk⟩ := hM
      exact ⟨hMn.map _ e.surjective, k, (M.index_map_of_bijective e.bijective).trans hk⟩
    · rintro ⟨hN, k, hk⟩
      refine ⟨N.comap e.toMonoidHom, ⟨hN.comap _, k, ?_⟩, ?_⟩
      · exact (N.index_comap_of_surjective e.surjective).trans hk
      · exact Subgroup.map_comap_eq_self_of_surjective e.surjective N
  have hr : (twoResidualSubgroup P).map e.toMonoidHom =
      twoResidualSubgroup (P.map f.toMonoidHom) := by
    change e.mapSubgroup (sInf {N : Subgroup P | N.Normal ∧ ∃ k : ℕ, N.index = 2 ^ k}) =
      sInf {N : Subgroup (P.map f.toMonoidHom) | N.Normal ∧ ∃ k : ℕ, N.index = 2 ^ k}
    rw [e.mapSubgroup.map_sInf, ← sInf_image, hsets]
  unfold twoResidualIn twoResidualAmbient
  rw [← hr, Subgroup.map_map, Subgroup.map_map]
  rfl

end Stellmacher.SectionsFiveToSeven
