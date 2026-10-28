module
public import Theory.SpecificGroups.AffineEight.SylowTransfer
public import Theory.SpecificGroups.AffineEight.AutomorphismOrbit
public import Theory.GroupTheory.SylowTransferInvariant
public import Mathlib.GroupTheory.Solvable

/-!
# Exclusion of the affine-eight Sylow group in nonsolvable simple groups

The multiplier-five involution has a nontrivial abelianization image fixed
by all automorphisms of the Sylow group. Its square and commutators satisfy
the maximal-subgroup transfer-vanishing criterion. Consequently its ambient
transfer is that image raised to the odd Sylow index, and is nontrivial.
This contradicts perfectness of a nonsolvable simple group.

No self-normalizer hypothesis is needed. The intrinsic two-element
characteristic class proved in `AutomorphismOrbit` replaces any computation
of the full automorphism group.

Source: Janko--Thompson (1970), printed p.393, citing Fong's exclusion;
the transfer argument is Andersen--Oliver--Ventura, *Fusion systems and
amalgams*, Proposition 2.3(b).
-/

namespace AffineEight
open scoped commutatorElement

public theorem not_perfect_of_sylow_equiv
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
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
  have ht2 : t ^ 2 = 1 := by
    apply e.injective
    simpa only [map_pow, map_one, t, MulEquiv.apply_symm_apply] using
      (show t₀ ^ 2 = 1 by decide)
  have hinvariant (f : MulAut S) :
      Abelianization.of (f t) = Abelianization.of t := by
    let φ : Model →* Abelianization S := Abelianization.of.comp e.symm.toMonoidHom
    let f₀ : MulAut Model := (e.symm.trans f).trans e
    have h := map_automorphism_five φ f₀
    change Abelianization.of (e.symm (e (f (e.symm t₀)))) =
      Abelianization.of (e.symm t₀) at h
    simpa only [MulEquiv.symm_apply_apply] using h
  intro hperfect
  apply S.not_mem_commutator_of_invariant_maximal_transfer_vanishing
    t U ht ht2 hinvariant hsq hc hm
  rw [hperfect]
  trivial

/-- A nonsolvable finite simple group cannot have the affine-eight Sylow group. -/
public theorem false_of_simple_sylow
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (e : S ≃* Model) : False := by
  have hproper := not_perfect_of_sylow_equiv S e
  have hbot : commutator G = ⊥ :=
    (inferInstance : (commutator G).Normal).eq_bot_or_eq_top.resolve_right hproper
  apply hns
  apply Group.isSolvable_of_comm
  intro x y
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have hmem : ⁅x, y⁆ ∈ commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  rwa [hbot, Subgroup.mem_bot] at hmem

end AffineEight
