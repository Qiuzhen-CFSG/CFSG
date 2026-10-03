module

public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Independence of centerless commuting factors

A family of centerless subgroups that commute at distinct indices is
independent: the intersection of one factor with the join of all other
factors lies in its center. This proves independence from the whole other
join, rather than merely pairwise disjointness. No finiteness is required
for this assertion.

For a finite independent commuting family in a finite group, the natural
product homomorphism is injective and has range the generated subgroup.
Its cardinality is therefore the product of the factor cardinalities.
These general facts supply the direct-product counting used in
Stellmacher (1.7), `refs/latex/stellmacher-n-group.tex`, journal page 19.
-/

namespace Subgroup

/-- Centerless subgroups commuting at distinct indices form an independent family. -/
public theorem iSupIndep_of_centerless_of_pairwise_commute
    {G I : Type*} [Group G] (H : I → Subgroup G)
    (hcenter : ∀ i, Subgroup.center (H i) = ⊥)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y) :
    iSupIndep H := by
  rw [iSupIndep_def]
  intro i
  have hle : (⨆ j, ⨆ (_ : j ≠ i), H j) ≤ Subgroup.centralizer (H i : Set G) := by
    refine iSup_le fun j => iSup_le fun hji => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm hji x y hx hy).symm.eq
  rw [disjoint_iff_inf_le]
  intro x hx
  have hc : (⟨x, hx.1⟩ : H i) ∈ Subgroup.center (H i) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hle hx.2) y y.property
  rw [hcenter i] at hc
  exact congrArg Subtype.val hc

/-- Cardinality of the join of a finite independent commuting family. -/
public theorem natCard_iSup_of_iSupIndep
    {G I : Type*} [Group G] [Finite G] [Fintype I] (H : I → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H) :
    Nat.card (↥(⨆ i, H i)) = ∏ i, Nat.card (H i) := by
  let f : (∀ i, H i) →* G := Subgroup.noncommPiCoprod hcomm
  have hf : Function.Injective f := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hr : f.range = ⨆ i, H i := Subgroup.noncommPiCoprod_range
  rw [← hr]
  calc
    Nat.card f.range = Nat.card (∀ i, H i) :=
      (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
    _ = ∏ i, Nat.card (H i) := Nat.card_pi

end Subgroup
