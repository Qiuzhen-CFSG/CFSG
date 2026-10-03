module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Coprime decomposition of a normalized subgroup

If `S` normalizes a finite solvable subgroup `K` and their orders are
coprime, then `K=[K,S] C_K(S)`. Apply the existing coprime-action
decomposition to the conjugation action on `K`, then map its two factors
through the subtype homomorphism. The conclusion is a subgroup join, avoiding
unnecessary choices of individual factors.

This supplies the local-centralizer decomposition used in Stellmacher
(1.6), journal p.18, for `K=C_W(X)`; see
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Subgroup

public theorem eq_commutator_sup_centralizer_of_solvable_coprime
    {G : Type*} [Group G] [Finite G]
    (K S : Subgroup G) (hnorm : S ≤ normalizer (K : Set G))
    (hsolv : Group.IsSolvable K) (hcop : Nat.Coprime (Nat.card S) (Nat.card K)) :
    K = ⁅K, S⁆ ⊔ (K ⊓ centralizer (S : Set G)) := by
  let _ : Normalizes S K := ⟨hnorm⟩
  have hdecomp := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := K) (A := S) hsolv hcop
  have hfix : (FixedPoints.subgroup S K).map K.subtype =
      K ⊓ centralizer (S : Set G) := by
    ext k
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.property, ?_⟩
      change (x : G) ∈ centralizer (S : Set G)
      rw [mem_centralizer_iff]
      intro s hs
      have h := congrArg Subtype.val (hx ⟨s, hs⟩)
      change s * (x : G) * s⁻¹ = x at h
      have hh := congrArg (fun z : G => z * s) h
      simpa [mul_assoc] using hh
    · rintro ⟨hk, hc⟩
      refine ⟨⟨k, hk⟩, ?_, rfl⟩
      intro s
      apply Subtype.ext
      change (s : G) * k * (s : G)⁻¹ = k
      change k ∈ centralizer (S : Set G) at hc
      rw [mem_centralizer_iff] at hc
      rw [hc s s.property, mul_assoc, mul_inv_cancel, mul_one]
  have hmapped := congrArg (fun H : Subgroup K => H.map K.subtype) hdecomp
  rw [Subgroup.map_sup, hfix,
    commutatorAction_subgroup_conj_map_eq_commutator K S hnorm,
    ← MonoidHom.range_eq_map, K.range_subtype, sup_comm] at hmapped
  exact hmapped.symm

end Subgroup

