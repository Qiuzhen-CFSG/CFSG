module

public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.IrreducibleMaximals.Data
public import Theory.GroupTheory.SubgroupEnumeration

/-!
# Enumerating overgroups of a seed subgroup in PSL₄(3)

A family closed under adjoining one element represents every overgroup of
any seed it represents. Induction on the finite set of elements of an
overgroup proves this without requiring the family to contain the trivial
subgroup. This allows separate enumerations starting at elements of order
five and thirteen.

Every extension and every terminal containment remains a proof obligation;
external search can supply witnesses but cannot establish coverage.

Source: the finite adjunction argument of `SubgroupEnumeration`, restricted
to a subgroup interval. Application: Aschbacher–Smith, Theorem 0.1.2(4) and
condition K, printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals

open Theory.GroupTheory.SubgroupEnumeration

variable {ι : Type*}

private theorem map_conj_map (H : Subgroup PSL) (g h : PSL) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      H.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem represented_seed_sup_closure
    (K : ι → Subgroup PSL) (S : Subgroup PSL) (hseed : Represented K S)
    (step : ∀ i x, Represented K (K i ⊔ Subgroup.zpowers x))
    {s : Set PSL} (hs : s.Finite) :
    Represented K (S ⊔ Subgroup.closure s) := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty => simpa only [Subgroup.closure_empty, sup_bot_eq] using hseed
  | @insert x s hx hs ih =>
      obtain ⟨i, g, hg⟩ := ih
      obtain ⟨j, h, hh⟩ := step i ((MulAut.conj g) x)
      refine ⟨j, h * g, ?_⟩
      rw [← map_conj_map, ← Set.singleton_union, Subgroup.closure_union,
        ← Subgroup.zpowers_eq_closure,
        show S ⊔ (Subgroup.zpowers x ⊔ Subgroup.closure s) =
          (S ⊔ Subgroup.closure s) ⊔ Subgroup.zpowers x by ac_rfl,
        Subgroup.map_sup, MonoidHom.map_zpowers, hg]
      exact hh

/-- Extension closure propagates representation from a seed to each overgroup. -/
public theorem represented_of_seed_le
    (K : ι → Subgroup PSL) (S : Subgroup PSL) (hseed : Represented K S)
    (step : ∀ i x, Represented K (K i ⊔ Subgroup.zpowers x))
    (H : Subgroup PSL) (hSH : S ≤ H) : Represented K H := by
  simpa only [Subgroup.closure_eq, sup_eq_right.mpr hSH] using
    represented_seed_sup_closure K S hseed step (Set.toFinite (H : Set PSL))

/-- Terminal bounds for a seeded enumeration cover every proper overgroup
of its seed. Both the seed and all extensions must be represented exactly. -/
public theorem seeded_proper_le_conjugate {κ : Type*}
    (K : ι → Subgroup PSL) (S : Subgroup PSL) (hseed : Represented K S)
    (step : ∀ i x, Represented K (K i ⊔ Subgroup.zpowers x))
    (C : κ → Subgroup PSL) (bound : ∀ i, K i = ⊤ ∨ ∃ j, K i ≤ C j)
    (H : Subgroup PSL) (hSH : S ≤ H) (hH : H ≠ ⊤) :
    ∃ j g, H ≤ (C j).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨i, g, hg⟩ := represented_of_seed_le K S hseed step H hSH
  rcases bound i with hi | ⟨j, hj⟩
  · exfalso
    apply hH
    apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective
    rw [hg, hi, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]
  · refine ⟨j, g⁻¹, ?_⟩
    intro x hx
    have hmem : (MulAut.conj g) x ∈ K i := by
      rw [← hg]
      exact Subgroup.mem_map_of_mem _ hx
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj g) x, hj hmem, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
end Matrix.PSL4Three.ProperOvergroups.IrreducibleMaximals
