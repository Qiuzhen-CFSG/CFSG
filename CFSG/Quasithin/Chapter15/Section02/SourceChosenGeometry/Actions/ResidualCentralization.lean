module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Inputs
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Omega.CommonImage

/-!
# Direct residual-centralization wrappers

The source residual calculation gives
`threePrimeResidual Mc ≤ centralizer (centralInvolutions T)` before the
partner-span equality is known.  The cyclic and Omega action wrappers
historically stored the stronger equality and rewrote through it.  These
parallel declarations expose the same cubic exclusions directly from the
centralization bound, so downstream model calculations can proceed while the
remaining equality/order-nine argument is assembled.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

namespace Cyclic
open ChosenGeometry

/-- The cyclic cubic exclusion with the literal residual bound. -/
theorem Preceding.three_centralizer_eq_bot_of_threePrimeResidual
    {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hres : threePrimeResidual Mc ≤ centralizer (centralInvolutions T : Set G))
    (hB : B ∈ sigmaOutside (T : Subgroup G) H)
    (C : Subgroup (internalActionImage M V h.prepared.normalized))
    (hp : IsPGroup 3 C)
    (hC : C ≤ centralizer (actor M V B h.prepared.normalized : Set _)) : C = ⊥ := by
  let := h.prepared.elementary
  let A := actor M V B h.prepared.normalized
  have hAc := (quadratic_fixed_eq_moved h A (d.planes B hB).1 (d.planes B hB).2.1).1
  let : IsCyclic A := isCyclic_of_prime_card hAc
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hAt : zpowers t = A := ht
  have htA : t ∈ A := ht ▸ mem_zpowers t
  have ht2 : t ^ 2 = 1 := congrArg Subtype.val
    (hAc ▸ pow_card_eq_one' (x := (⟨t,htA⟩ : A)))
  have hpE := (d.planes B hB).2.2
  apply three_image_centralizer_eq_bot h hpE.1 hpE.2.1 hpE.2.2.2.1 hpE.2.2.2.2.1
    hres t ht2 _ C hp
    (hC.trans (centralizer_le (Set.singleton_subset_iff.mpr htA)))
  rw [hAt, ambientSpace_fixed _ ((d.actor_le_sylow hB).trans h.maximal.1.2)]
  exact ambient_fixed_eq_commutator h ((d.actor_le_sylow hB).trans h.maximal.1.2)
    (d.planes B hB).1 (d.planes B hB).2.1

end Cyclic

namespace Omega
open Cyclic

/-- The Omega cubic exclusion with the literal residual bound. -/
theorem Preceding.three_centralizer_eq_bot_of_threePrimeResidual
    {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hres : threePrimeResidual Mc ≤ centralizer (centralInvolutions T : Set G))
    (hB : B ∈ sigmaOutside (T : Subgroup G) H)
    (C : Subgroup (internalActionImage M V h.prepared.normalized))
    (hp : IsPGroup 3 C)
    (hC : C ≤ centralizer (actor M V B h.prepared.normalized : Set _)) : C = ⊥ := by
  let := h.prepared.elementary
  let A := actor M V B h.prepared.normalized
  have hAc := (quadratic_fixed_eq_moved h A (d.planes B hB).1 (d.planes B hB).2.1).1
  let : IsCyclic A := isCyclic_of_prime_card hAc
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hAt : zpowers t = A := ht
  have htA : t ∈ A := ht ▸ mem_zpowers t
  have ht2 : t ^ 2 = 1 := congrArg Subtype.val
    (hAc ▸ pow_card_eq_one' (x := (⟨t,htA⟩ : A)))
  have hpE := (d.planes B hB).2.2
  apply three_image_centralizer_eq_bot h hpE.1 hpE.2.1 hpE.2.2.2.1 hpE.2.2.2.2.1
    hres t ht2 _ C hp
    (hC.trans (centralizer_le (Set.singleton_subset_iff.mpr htA)))
  rw [hAt, ambientSpace_fixed _ ((d.actor_le_sylow hB).trans h.maximal.1.2)]
  exact ambient_fixed_eq_commutator h ((d.actor_le_sylow hB).trans h.maximal.1.2)
    (d.planes B hB).1 (d.planes B hB).2.1

end Omega
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
