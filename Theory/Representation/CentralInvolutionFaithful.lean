module

public import Theory.Representation.SubrepresentationLattice

/-!
# Faithful irreducible submodules detected by a central involution

Suppose a central involution `z` lies in every nontrivial normal subgroup of
`G`. Over a field where two is nonzero, every finite-dimensional faithful
representation of `G` contains a faithful irreducible subrepresentation.
Its dimension is at most that of the original representation.

The minus eigenspace of `z` is invariant because `z` is central. It is nonzero:
faithfulness gives a vector moved by `z`, and its difference with its image
lies in that eigenspace. Take a minimal nonzero invariant subspace there.
The element `z` acts as minus identity on this subspace and hence is absent
from its kernel; the normal-subgroup hypothesis makes the kernel trivial.
No semisimplicity assumption on the original representation is needed.

This supplies the representation-theoretic reduction implicit in
Alperin--Brauer--Gorenstein II.4, Lemma 18 (article p.45), before the use of
Fong--Wong (1E). The SL2 application proves the normal-subgroup hypothesis
separately, including the field of three elements.
-/

namespace Representation

variable {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private def minusSpace (rho : Representation F G V) (z : G)
    (hz : z ∈ Subgroup.center G) : Subrepresentation rho where
  toSubmodule := (rho z + 1).ker
  apply_mem_toSubmodule g := by
    intro v hv
    change rho z v + v = 0 at hv
    change rho z (rho g v) + rho g v = 0
    have hzg : z * g = g * z := (Subgroup.mem_center_iff.mp hz g).symm
    have heq : rho z (rho g v) = rho g (rho z v) := by
      change (rho z * rho g) v = (rho g * rho z) v
      rw [← map_mul, ← map_mul, hzg]
    rw [heq, ← map_add, hv, map_zero]

/-- A central involution belonging to every nontrivial normal subgroup detects
a faithful irreducible subrepresentation of any faithful representation. -/
public theorem exists_faithful_irreducible_subrepresentation
    (hF : (2 : F) ≠ 0) (rho : Representation F G V)
    (hrho : Function.Injective rho) (z : G)
    (hz : z ∈ Subgroup.center G) (hzsq : z ^ 2 = 1) (hzne : z ≠ 1)
    (hmono : ∀ (N : Subgroup G), N.Normal → z ∉ N → N = ⊥) :
    ∃ W : Subrepresentation rho, IsIrreducible W.toRepresentation ∧
      Function.Injective W.toRepresentation ∧
      Module.finrank F W.toSubmodule ≤ Module.finrank F V := by
  classical
  have hrz : rho z ≠ 1 := fun heq => hzne (hrho (heq.trans rho.map_one.symm))
  have hex : ∃ v : V, rho z v ≠ v := by
    by_contra! h
    exact hrz (LinearMap.ext h)
  obtain ⟨v, hv⟩ := hex
  have hzv : rho z (rho z v) = v := by
    change (rho z * rho z) v = v
    rw [← map_mul, ← pow_two, hzsq, map_one]
    rfl
  have hnonzero : minusSpace rho z hz ≠ ⊥ := by
    intro hbot
    have hmem : rho z v - v ∈ minusSpace rho z hz := by
      change rho z (rho z v - v) + (rho z v - v) = 0
      rw [map_sub, hzv]
      abel
    rw [hbot] at hmem
    exact hv (sub_eq_zero.mp hmem)
  obtain ⟨W, hWatom, hWle⟩ :=
    (eq_bot_or_exists_atom_le (minusSpace rho z hz)).resolve_left hnonzero
  have hW : IsIrreducible W.toRepresentation :=
    (Subrepresentation.irreducible_iff_isAtom W).mpr hWatom
  let : IsIrreducible W.toRepresentation := hW
  let : Nontrivial W.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial W.toRepresentation
  have hzker : z ∉ W.toRepresentation.ker := by
    intro hzker
    have heq : W.toRepresentation z = 1 := hzker
    obtain ⟨w, hw⟩ := exists_ne (0 : W.toSubmodule)
    have hzw : rho z w.val = w.val := by
      have hh := congrArg (fun f : Module.End F W.toSubmodule => (f w).val) heq
      exact hh
    have hminus := hWle w.property
    change rho z w.val + w.val = 0 at hminus
    rw [hzw] at hminus
    have htwo : (2 : F) • w.val = 0 := by simpa [two_smul] using hminus
    have hwzero : w.val = 0 := (smul_eq_zero.mp htwo).resolve_left hF
    exact hw (Subtype.ext hwzero)
  refine ⟨W, hW, ?_, Submodule.finrank_le W.toSubmodule⟩
  exact W.toRepresentation.ker_eq_bot_iff.mp
    (hmono W.toRepresentation.ker inferInstance hzker)

end Representation
