module

public import Theory.Representation.BinaryOffender.ComponentSeedNormality

/-!
# The actor normalizer preserves the moved component

The displacement of a minimal best plane offender lies in the full moved
space of its component. A distinct conjugate component centralizes that
space because the latter is Irr⁺. The actor normalizer preserves the
original displacement, so conjugating back would make the original
component fix that displacement, contradicting its full commutator.
No irreducible seed or quotient rank monotonicity is assumed.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The normalizer of the whole actor preserves its Irr⁺ moved component. -/
theorem component_normalized_by_actor_normalizer_of_minimal_plane
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    {K A : Subgroup G} (hK : IsComponent G K)
    (hi : IsIrrPlus ρ K (subspaceCommutator ρ ⊤ K))
    (hA : IsMinimalBestOffender ρ A) (hc : ⁅K,A⁆=K)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A)≤2) :
    normalizer (A:Set G)≤normalizer (K:Set G) := by
  let : IsQuasisimple K := hK.2
  have hKn : K≠⊥ := by
    intro he
    apply hi.not_le_fixedSpace ρ
    rw [he]
    simp
  have hm : subspaceCommutator ρ ⊤ A≤subspaceCommutator ρ ⊤ K :=
    hA.moved_le_moved_perfect ρ hf hKn hd hc
  have hstable : normalizer (A:Set G)≤subspaceStabilizer ρ (subspaceCommutator ρ ⊤ A) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_rfl
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  let J := K.map (MulAut.conj t).toMonoidHom
  have hJ : IsComponent G J := hK.map_conj t
  let : IsQuasisimple J := hJ.2
  have hJK : J≤centralizer (K:Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hJ.commutator_eq_bot_of_ne hK hne)
  have hfixed : subspaceCommutator ρ ⊤ K≤fixedSpace ρ J :=
    hi.le_fixedSpace_of_perfect_centralizes ρ hJK
      (subspaceCommutator_invariant_normalizer ρ
        (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
        (hJK.trans (Subgroup.centralizer_le_normalizer _)))
  have hback : subspaceCommutator ρ ⊤ A≤fixedSpace ρ K := by
    intro v hv k
    have htv : ρ t v∈subspaceCommutator ρ ⊤ A := (hstable ht v).2 hv
    have he := hfixed (hm htv)
      ⟨t*k.val*t⁻¹,mem_map_of_mem (MulAut.conj t).toMonoidHom k.property⟩
    change ρ (t*k.val*t⁻¹) (ρ t v)=ρ t v at he
    have hh := congrArg (ρ t⁻¹) he
    change ρ k.val v=v
    simpa only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel_left,
      inv_mul_cancel,mul_one,map_one,Module.End.one_apply] using hh
  exact moved_not_fixed_of_perfect_commutator ρ hf hKn hc hback

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
