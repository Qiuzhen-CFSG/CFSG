module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic outer automorphisms and central centralizers

For a normal subgroup N, the kernel of the actual outer action of G/N is
precisely the image of C_G(N). If this centralizer lies in Z(G), the kernel
is central. A cyclic outer group therefore makes G/N abelian. In particular,
a centralizer of order two suffices, since it is normal and hence central.
No splitting of the extension by inner automorphisms is needed.

Source: GLS IV, Chapter 2, the quotient argument after Lemma 15.7.
-/

noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace Subgroup

/-- A central centralizer and cyclic outer group make the original quotient abelian. -/
public theorem quotient_commutative_of_centralizer_central
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [IsCyclic (MulAut.Outer N)]
    (hc : centralizer (N : Set G) ≤ center G) :
    IsMulCommutative (G ⧸ N) := by
  apply (MulAut.outerAction N).isMulCommutative_of_isCyclic_of_ker_le_center
  have hk : (MulAut.outerAction N).ker =
      (centralizer (N : Set G)).map (QuotientGroup.mk' N) := by
    rw [MulAut.outerAction, QuotientGroup.ker_map,
      MulAut.conjNormal_comap_innerSubgroup, map_sup,
      QuotientGroup.map_mk'_self, bot_sup_eq]
  rw [hk]
  rintro x ⟨c, hcC, rfl⟩
  apply mem_center_iff.mpr
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
  rw [← map_mul, ← map_mul, (mem_center_iff.mp (hc hcC) g)]

/-- The order-two centralizer case needs no splitting of the automorphism extension. -/
public theorem quotient_commutative_of_centralizer_two
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [IsCyclic (MulAut.Outer N)] (hc : Nat.card (centralizer (N : Set G)) = 2) :
    IsMulCommutative (G ⧸ N) :=
  quotient_commutative_of_centralizer_central N
    (central_of_normal_card_two _ hc)

end Subgroup
