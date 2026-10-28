module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.AmbientInput
public import Theory.Mathieu.M12.A5Fixer.Automorphisms.OuterIndex

/-!
# Inner automorphisms and odd-order elements in the ambient M₁₂ action

For any actual ambient extension, its marking maps the solvable residual onto
the full inner automorphism subgroup. Injectivity recovers the residual as
its exact preimage. The proved outer-index bound then puts every element of
odd prime order in this residual. No classification of the given ambient group
or of its representation is assumed.

Source: the ambient reduction for Aschbacher–Smith H.11.1, printed pp.392–393
(1 March 2004 manuscript).
-/

public section

namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
open Sporadic.Mathieu
namespace AmbientExtension
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V} {h : M12ModuleInput ρ}
variable (E : AmbientExtension ρ h)

/-- The residual maps onto all inner automorphisms, with its original marking. -/
theorem map_residual : (Subgroup.solvableResidual G).map E.embedding =
    MulAut.innerSubgroup M12 := by
  ext a
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨h.residualEquiv ⟨t, ht⟩, (E.embedding_residual ⟨t, ht⟩).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨h.residualEquiv.symm t, (h.residualEquiv.symm t).property, ?_⟩
    rw [E.embedding_residual, h.residualEquiv.apply_symm_apply]

/-- The preimage of the inner automorphisms is exactly the solvable residual. -/
theorem comap_inner : (MulAut.innerSubgroup M12).comap E.embedding =
    Subgroup.solvableResidual G := by
  rw [← E.map_residual, Subgroup.comap_map_eq_self_of_injective E.embedding_injective]

include E in
/-- Every odd-prime-order ambient element lies in the solvable residual. -/
theorem mem_residual_of_odd_prime_order (g : G)
    (hp : (orderOf g).Prime) (hodd : orderOf g ≠ 2) :
    g ∈ Subgroup.solvableResidual G := by
  rw [← E.comap_inner]
  change E.embedding g ∈ MulAut.innerSubgroup M12
  apply (QuotientGroup.eq_one_iff (N := MulAut.innerSubgroup M12) _).mp
  let q := (QuotientGroup.mk' (MulAut.innerSubgroup M12)).comp E.embedding
  change q g = 1
  apply orderOf_eq_one_iff.mp
  have hd : orderOf (q g) ∣ orderOf g := orderOf_map_dvd q g
  rcases (Nat.dvd_prime hp).mp hd with hone | heq
  · exact hone
  · have hb : orderOf (q g) ≤ 2 := calc
      _ ≤ Nat.card (MulAut.Outer M12) := orderOf_le_card
      _ ≤ 2 := M12A5Fixer.Automorphisms.outerIndexBound
    have hp2 := hp.two_le
    omega

end AmbientExtension
end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
