module

public import Theory.Representation.BinaryNaturalDual.ModelOrbits.MarkedComparison

/-!
# Transport of the marked natural-plus-dual comparison

A compatible isomorphism of acting groups transports the constructed comparison
without changing the specified natural marking or the complementary summand.
For a group identified with Aut(G), an actual isomorphism G ≃ GLₙ(2) identifies
the inner actions and preserves the outer-image condition. The final theorem
specializes this to the checked projective binary matrix comparison
PSLₙ(2) ≃ GLₙ(2).

The representation is pulled back along the group isomorphism, the marked
comparison is constructed, and its equivariance is pushed forward. Identifying
the source layer with the preimage of the inner subgroup remains a source-group
obligation; no layer or quotient convention is silently substituted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9 setup and
H.9.1(1–2), printed pp.389–390.
-/

public section

open scoped MatrixGroups
open BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.ModelOrbits.MarkedComparison
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {M : Type*} [Group M]

/-- Transfer the comparison to any acting group isomorphic to the actual automorphism group. -/
theorem exists_equiv_of_groupEquiv (hn : n = 4 ∨ n = 5) (A : CoordinateAction n)
    (ρ : Representation (ZMod 2) M V) (eM : M ≃* MulAut (LinearGroup n))
    {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (eU : U ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n)
    (hU : ∀ (g : LinearGroup n) (x : BinaryLinear.OuterCyclic.Space n),
      ρ (eM.symm (MulAut.conj g)) (eU.symm x : V) = (eU.symm (g x) : V))
    (hout : ∃ t : M, eM t ∉ MulAut.innerSubgroup (LinearGroup n) ∧ U.map (ρ t) = W) :
    ∃ (eW : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
      (eV : V ≃ₗ[ZMod 2] CoordinateSpace n),
      (∀ u : U, eV u = (eU u, 0)) ∧
      (∀ w : W, eV w = (0, eW w)) ∧
      (∀ m v, eV (ρ m v) = A.representation (eM m) (eV v)) := by
  let σ : Representation (ZMod 2) (MulAut (LinearGroup n)) V :=
    ρ.comp eM.symm.toMonoidHom
  have hout' : ∃ t : MulAut (LinearGroup n), t ∉ MulAut.innerSubgroup (LinearGroup n) ∧
      U.map (σ t) = W := by
    obtain ⟨t, ht, hmap⟩ := hout
    exact ⟨eM t, ht, by simpa [σ] using hmap⟩
  obtain ⟨eW, eV, hnat, hdual, he⟩ := exists_equiv σ eU hn A hUW hU hout'
  refine ⟨eW, eV, hnat, hdual, ?_⟩
  intro m v
  simpa [σ] using he (eM m) v

/-- An actual group-model equivalence transports both the natural marking and the outer condition. -/
theorem exists_equiv_of_automorphismEquiv {G : Type*} [Group G]
    (hn : n = 4 ∨ n = 5) (A : CoordinateAction n)
    (ρ : Representation (ZMod 2) M V) (eM : M ≃* MulAut G)
    (eG : G ≃* LinearGroup n)
    {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (eU : U ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n)
    (hU : ∀ (g : G) (x : BinaryLinear.OuterCyclic.Space n),
      ρ (eM.symm (MulAut.conj g)) (eU.symm x : V) = (eU.symm (eG g x) : V))
    (hout : ∃ t : M, eM t ∉ MulAut.innerSubgroup G ∧ U.map (ρ t) = W) :
    ∃ (eW : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
      (eV : V ≃ₗ[ZMod 2] CoordinateSpace n),
      (∀ u : U, eV u = (eU u, 0)) ∧
      (∀ w : W, eV w = (0, eW w)) ∧
      (∀ m v, eV (ρ m v) = A.representation (MulAut.congr eG (eM m)) (eV v)) := by
  let e : M ≃* MulAut (LinearGroup n) := eM.trans (MulAut.congr eG)
  have hconj (g : LinearGroup n) : e.symm (MulAut.conj g) =
      eM.symm (MulAut.conj (eG.symm g)) := by
    apply e.injective
    change e (e.symm (MulAut.conj g)) =
      MulAut.congr eG (eM (eM.symm (MulAut.conj (eG.symm g))))
    rw [e.apply_symm_apply, eM.apply_symm_apply, MulAut.congr_conj, eG.apply_symm_apply]
  have hnat (g : LinearGroup n) (x : BinaryLinear.OuterCyclic.Space n) :
      ρ (e.symm (MulAut.conj g)) (eU.symm x : V) = (eU.symm (g x) : V) := by
    rw [hconj, hU, eG.apply_symm_apply]
  have hout' : ∃ t : M, e t ∉ MulAut.innerSubgroup (LinearGroup n) ∧ U.map (ρ t) = W := by
    obtain ⟨t, ht, hmap⟩ := hout
    refine ⟨t, ?_, hmap⟩
    intro hi
    have hi' : MulAut.congr eG (eM t) ∈
        (MulAut.innerSubgroup G).map (MulAut.congr eG).toMonoidHom := by
      rw [MulAut.map_innerSubgroup_congr]
      exact hi
    obtain ⟨a, ha, he⟩ := hi'
    exact ht ((MulAut.congr eG).injective he ▸ ha)
  exact exists_equiv_of_groupEquiv hn A ρ e hUW eU hnat hout'

/-- The marked comparison for an arbitrary source group isomorphic to Aut(PSLₙ(2)),
using the actual projective-to-linear equivalence on its natural module. -/
theorem exists_equiv_of_projectiveEquiv (hn : n = 4 ∨ n = 5) (A : CoordinateAction n)
    (ρ : Representation (ZMod 2) M V) (eM : M ≃* MulAut PSL(n, ZMod 2))
    {U W : Submodule (ZMod 2) V} (hUW : IsCompl U W)
    (eU : U ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n)
    (hU : ∀ (g : PSL(n, ZMod 2)) (x : BinaryLinear.OuterCyclic.Space n),
      ρ (eM.symm (MulAut.conj g)) (eU.symm x : V) =
        (eU.symm (projectiveEquivLinear (by omega : 0 < n) g x) : V))
    (hout : ∃ t : M, eM t ∉ MulAut.innerSubgroup PSL(n, ZMod 2) ∧ U.map (ρ t) = W) :
    ∃ (eW : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
      (eV : V ≃ₗ[ZMod 2] CoordinateSpace n),
      (∀ u : U, eV u = (eU u, 0)) ∧
      (∀ w : W, eV w = (0, eW w)) ∧
      (∀ m v, eV (ρ m v) = A.representation
        (MulAut.congr (projectiveEquivLinear (by omega : 0 < n)) (eM m)) (eV v)) :=
  exists_equiv_of_automorphismEquiv hn A ρ eM (projectiveEquivLinear (by omega)) hUW eU hU hout

end BinaryNaturalDual.ModelOrbits.MarkedComparison
