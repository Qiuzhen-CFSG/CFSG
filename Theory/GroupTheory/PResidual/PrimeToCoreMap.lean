module

public import Theory.GroupTheory.FiniteParabolicTransfer
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The p-core of the prime-to-p residual

Every p-subgroup belongs to O^{p′}(G), in particular O_p(G). Conversely the
intrinsic p-core of O^{p′}(G) is characteristic in a normal subgroup of G,
so its image is a normal p-subgroup of G. Thus their embedded p-cores agree.
This is the core comparison in the local parabolic calculations of GLS3 §2.6.
-/

public section
namespace Subgroup

/-- Taking the prime-to-p residual preserves the p-core, with its embedding. -/
theorem map_pCore_primeToResidual {G : Type*} [Group G] (p : ℕ) :
    (pCore p (primeToResidual p G)).map (primeToResidual p G).subtype = pCore p G := by
  apply le_antisymm
  · exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,
      pCore_isPGroup.map _⟩
  · have h : pCore p G ≤ primeToResidual p G :=
      le_primeToResidual_of_isPGroup pCore_isPGroup
    have hr : (pCore p G).subgroupOf (primeToResidual p G) ≤
        pCore p (primeToResidual p G) :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    simpa only [map_subgroupOf_eq_of_le h] using
      map_mono (f := (primeToResidual p G).subtype) hr

end Subgroup
