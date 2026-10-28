module

public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Restricting a prime core to a subgroup

For H ≤ D, the intersection H ∩ O_p(D) is a normal p-subgroup of H,
so lies in O_p(H). Consequently a subgroup of H escaping O_p(H) also
escapes O_p(D). No normality of H in D is required.

This is the transfer needed for the local centralizer calculation in
Aschbacher--Smith, Theorem 4.2.13(4), combined manuscript of 1 March 2004,
printed p.611: use H = C_K(z) and D = C_G(z).
-/

namespace Subgroup

/-- Restricting an ambient p-core to a subgroup lands in its intrinsic p-core. -/
public theorem inf_pCoreIn_le_of_le {G : Type*} [Group G]
    (p : ℕ) {H D : Subgroup G} (hHD : H ≤ D) :
    H ⊓ D.pCoreIn p ≤ H.pCoreIn p := by
  let f : H →* D := inclusion hHD
  have hp : IsPGroup p ((pCore p D).comap f) :=
    pCore_isPGroup.comap_of_injective f (inclusion_injective hHD)
  have hc : (pCore p D).comap f ≤ pCore p H := le_sSup ⟨inferInstance, hp⟩
  rintro x ⟨hxH, y, hy, hyx⟩
  refine ⟨⟨x, hxH⟩, hc ?_, rfl⟩
  change f ⟨x, hxH⟩ ∈ pCore p D
  have heq : f ⟨x, hxH⟩ = y := Subtype.ext hyx.symm
  rwa [heq]

/-- A subgroup witnessing failure of p-core containment in H also witnesses
failure in every overgroup of H. -/
public theorem not_le_pCoreIn_of_subgroup {G : Type*} [Group G]
    (p : ℕ) {V H D : Subgroup G} (hVH : V ≤ H) (hHD : H ≤ D)
    (hne : ¬ V ≤ H.pCoreIn p) : ¬ V ≤ D.pCoreIn p := by
  intro hVD
  exact hne ((le_inf hVH hVD).trans (inf_pCoreIn_le_of_le p hHD))

end Subgroup
