module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.Contracts

/-!
# The literal quotient in the second cubic centralizer calculation

We retain the cyclic subgroup, centralizer, quotient projection and root
four-group in Aschbacher, *Sporadic Groups* (1994), 47.3, printed p.262.
The kernel is the actual subgroup ⟨y⟩ inside C_G(⟨y⟩), and its centrality
and order are proved without the first cubic centralizer calculation.

These definitions are shared by the geometric recognition of the quotient
and the lifting of its normal and alternating-five branches.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer

variable {G : Type*} [Group G]

/-- The actual cyclic kernel inside the cubic centralizer. -/
def cubicKernel (y : G) : Subgroup (cubicCentralizer y) :=
  (zpowers y).subgroupOf (cubicCentralizer y)

theorem zpowers_le_cubicCentralizer (y : G) : zpowers y ≤ cubicCentralizer y :=
  le_centralizer _

theorem cubicKernel_le_center (y : G) : cubicKernel y ≤ center (cubicCentralizer y) := by
  intro x hx
  apply mem_center_iff.mpr
  intro a
  exact Subtype.ext (a.property x hx).symm

instance cubicKernel_normal (y : G) : (cubicKernel y).Normal := by
  constructor
  intro x hx g
  rw [mem_center_iff.mp (cubicKernel_le_center y hx) g, mul_assoc,
    mul_inv_cancel, mul_one]
  exact hx

/-- The quotient M/Y from printed p.262, with M = C_G(⟨y⟩). -/
abbrev CubicQuotient (y : G) := cubicCentralizer y ⧸ cubicKernel y

/-- Its specified quotient projection. -/
def cubicQuotientMap (y : G) : cubicCentralizer y →* CubicQuotient y :=
  QuotientGroup.mk' (cubicKernel y)

theorem cubicQuotientMap_surjective (y : G) : Function.Surjective (cubicQuotientMap y) :=
  QuotientGroup.mk'_surjective _

theorem cubicQuotientMap_ker (y : G) : (cubicQuotientMap y).ker = cubicKernel y :=
  QuotientGroup.ker_mk' _

theorem cubicKernel_card {y : G} (hyo : orderOf y = 3) : Nat.card (cubicKernel y) = 3 := by
  rw [cubicKernel, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le_cubicCentralizer y)).toEquiv,
    Nat.card_zpowers, hyo]

variable [Finite G] {D : Seed G}

/-- The literal root four-group regarded as a subgroup of M. -/
def centralizerRoot (S : InvolutionGeometry.SelectedGeometry D) (y : G) :
    Subgroup (cubicCentralizer y) :=
  (InvolutionGeometry.rootCore S.t).subgroupOf (cubicCentralizer y)

/-- Its image under the specified quotient projection. -/
def quotientRoot (S : InvolutionGeometry.SelectedGeometry D) (y : G) :
    Subgroup (CubicQuotient y) :=
  (centralizerRoot S y).map (cubicQuotientMap y)

theorem centralizerRoot_card (S : InvolutionGeometry.SelectedGeometry D)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent S.t) :
    Nat.card (centralizerRoot S y) = 4 := by
  rw [centralizerRoot,
    Nat.card_congr (subgroupOfEquivOfLe (rootCore_le_cubicCentralizer S hy)).toEquiv,
    S.model.rootCore_card]

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer
