module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.SetLike.Fintype

/-!
# Centralizers of uniqueness subgroups

In an automorphism-invariant finite family of subgroups, suppose `H` has a
unique maximal overgroup `M`, and `M` is self-normalizing. If `Z` centralizes
`H` and every nonidentity element of `Z` has its centralizer covered by the
family, then `Z` meets each conjugate by an element outside `M` trivially.

A common nonidentity element puts `H` and its conjugate inside one centralizer.
Extend a covering subgroup to a maximal member of the family. Uniqueness,
applied before and after conjugation, forces the conjugating element into
`N_G(M) = M`.

Source: the argument in Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined 1 March 2004 manuscript, Theorem 1.2.7(4), printed p. 506.
-/

namespace Theory.GroupTheory

variable {G : Type*} [Group G]

private theorem maximal_map_of_invariant
    {F : Set (Subgroup G)}
    (hF : ∀ (e : MulAut G) (K : Subgroup G), K ∈ F → K.map e.toMonoidHom ∈ F)
    {M : Subgroup G} (hM : Maximal (· ∈ F) M) (e : MulAut G) :
    Maximal (· ∈ F) (M.map e.toMonoidHom) := by
  refine ⟨hF e M hM.prop, ?_⟩
  intro K hK hle
  let f := e.mapSubgroup
  have hle' : f M ≤ K := hle
  have hpre : M ≤ f.symm K := by
    simpa only [OrderIso.symm_apply_apply] using f.symm.monotone hle'
  have hback : f.symm K ≤ M := hM.2 (hF e.symm K hK) hpre
  have h := f.monotone hback
  rw [f.apply_symm_apply] at h
  simpa only [f, MulEquiv.coe_mapSubgroup] using h

/-- A subgroup centralized by a uniqueness group has disjoint outside conjugates.
The family may be the two-local subgroups, so maximality need not be maximality
among all proper subgroups. -/
public theorem inf_conjugate_eq_bot_of_unique_maximal [Finite G]
    {F : Set (Subgroup G)} {H M Z : Subgroup G}
    (hF : ∀ (e : MulAut G) (K : Subgroup G), K ∈ F → K.map e.toMonoidHom ∈ F)
    (hM : Maximal (· ∈ F) M)
    (hunique : ∀ K : Subgroup G, Maximal (· ∈ F) K → H ≤ K → K = M)
    (hself : Subgroup.normalizer (M : Set G) ≤ M)
    (hHZ : H ≤ Subgroup.centralizer (Z : Set G))
    (hcentralizers : ∀ z ∈ Z, z ≠ 1 → ∃ K ∈ F,
      Subgroup.centralizer ({z} : Set G) ≤ K)
    {g : G} (hg : g ∉ M) :
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  apply Subgroup.mem_bot.mpr
  by_contra hz1
  obtain ⟨K, hK, hCK⟩ := hcentralizers z hz.1 hz1
  obtain ⟨P, hKP, hP⟩ := Finite.exists_le_maximal hK
  have hHP : H ≤ P := by
    intro x hx
    apply hKP (hCK ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((hHZ hx z hz.1).symm)
  have hPM : P = M := hunique P hP hHP
  let e : MulAut G := MulAut.conj g
  have hconj : H.map e.toMonoidHom ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hPM]
    apply hKP (hCK ?_)
    obtain ⟨y, hy, hye⟩ := hz.2
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change e y = z at hye
    rw [← hye]
    change e x * e y = e y * e x
    simpa only [map_mul] using congrArg e ((hHZ hx y hy).symm)
  have hconj' : e.mapSubgroup H ≤ M := hconj
  have hback : H ≤ e.symm.mapSubgroup M := by
    have h := e.mapSubgroup.symm.monotone hconj'
    rw [e.mapSubgroup.symm_apply_apply] at h
    simpa only [MulEquiv.symm_mapSubgroup] using h
  have heq : M.map e.symm.toMonoidHom = M :=
    hunique _ (maximal_map_of_invariant hF hM e.symm) hback
  have hmap : M.map e.toMonoidHom = M :=
    (Subgroup.map_symm_eq_iff_map_eq M (e := e)).mp heq
  exact hg (hself (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap))

end Theory.GroupTheory
