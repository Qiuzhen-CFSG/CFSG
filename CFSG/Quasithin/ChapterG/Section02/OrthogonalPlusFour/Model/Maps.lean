module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Source
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.Generation
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PCoreRestriction
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The marked determinant action and the generation lift in G.2.6

The normality of LU in LT identifies its intrinsic two-core with the
kernel of the original star map. Equality of starred images then lifts
through the normalizing two-core supplement, using L=O²(L), to I=LU.
The quotient comparisons retain the original projection and intertwine
conjugation with the determinant action. The singular-point calculation
which supplies starred generation is a separate input to this module.

Source: Aschbacher–Smith, G.2.6, printed p.336, using the proof of
G.2.3(2), printed p.333. The orthogonal comparison uses the actual
Siegel-generated group, and the symmetric-group comparison uses the
projective action of SL₂(2) on its three-point projective line.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G]

private theorem core_eq_inf_of_normalizes {D : Setup G} {A : Subgroup G}
    (hA : A ≤ D.LT) (hN : D.LT ≤ normalizer (A : Set G)) :
    A.pCoreIn 2 = A ⊓ D.LT.pCoreIn 2 := by
  apply le_antisymm _ (inf_pCoreIn_le_of_le 2 hA)
  exact le_inf (pCoreIn_le 2 A)
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A) ((pCoreIn_le 2 A).trans hA)
      (hN.trans (normalizer_le_normalizer_characteristic_image _ _)))

private theorem starProjection_ker_of_normalizes {D : Setup G} {A : Subgroup G}
    (hA : A ≤ D.LT) (hN : D.LT ≤ normalizer (A : Set G)) :
    (starProjection D A hA).ker = pCore 2 A := by
  have hs := core_eq_inf_of_normalizes hA hN
  ext a
  have hiff : a ∈ (starProjection D A hA).ker ↔ (a : G) ∈ D.LT.pCoreIn 2 := by
    change starProjection D A hA a = 1 ↔ _
    rw [Subtype.ext_iff]
    change (QuotientGroup.mk (inclusion hA a) : D.Star) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro ha
      exact ⟨_, ha, rfl⟩
    · rintro ⟨b, hb, he⟩
      exact (show b = inclusion hA a from Subtype.ext he) ▸ hb
  rw [hiff]
  constructor
  · intro ha
    have haS : (a : G) ∈ A.pCoreIn 2 := hs.symm ▸ ⟨a.property, ha⟩
    obtain ⟨b, hb, he⟩ := haS
    exact (show b = a from Subtype.ext he) ▸ hb
  · intro ha
    have haS : (a : G) ∈ A.pCoreIn 2 := ⟨a, ha, rfl⟩
    exact (hs ▸ haS).2

namespace Hypothesis
variable [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

theorem LU_le_LT : D.L ⊔ D.U ≤ D.LT := binary_join_le_LT d.closure.normal.1

theorem I_le_LT : D.I g ≤ D.LT := d.I_le_LU.trans d.LU_le_LT

/-- Relative normality of LU, before the two marked subgroups are known to generate it. -/
theorem LT_normalizes_LU : D.LT ≤ normalizer (D.L ⊔ D.U : Subgroup G) :=
  sup_le (le_sup_left.trans (D.L ⊔ D.U).le_normalizer)
    ((le_inf d.base.T_normalizes_L d.base.binary_T_normalizes_U).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))

/-- The same original star map, now with the concrete determinant group as target. -/
def matrixProjection : (D.L ⊔ D.U : Subgroup G) →* PairSL (F := ZMod 2) :=
  d.model.toMonoidHom.comp (starProjection D (D.L ⊔ D.U) d.LU_le_LT)

theorem matrixProjection_surjective : Function.Surjective d.matrixProjection :=
  d.model.surjective.comp (starProjection_surjective D _ _)

/-- The actual image of any marked subgroup in the determinant model. -/
def modelImage (A : Subgroup G) : Subgroup (PairSL (F := ZMod 2)) :=
  (A.subgroupOf (D.L ⊔ D.U)).map d.matrixProjection

theorem modelImage_L_sup_U : d.modelImage D.L ⊔ d.modelImage D.U = ⊤ := by
  rw [modelImage, modelImage, ← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right]
  rw [subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr d.matrixProjection_surjective]

/-- This equality identifies the intrinsic core without any generation assumption. -/
theorem LU_core_eq_star_kernel :
    (D.L ⊔ D.U : Subgroup G).pCoreIn 2 = (D.L ⊔ D.U) ⊓ D.LT.pCoreIn 2 :=
  core_eq_inf_of_normalizes d.LU_le_LT d.LT_normalizes_LU

theorem LU_starProjection_ker :
    (starProjection D (D.L ⊔ D.U) d.LU_le_LT).ker = pCore 2 (D.L ⊔ D.U : Subgroup G) :=
  starProjection_ker_of_normalizes d.LU_le_LT d.LT_normalizes_LU

/-- The full starred LU is compared with the actual orthogonal carrier. -/
def starOrthogonalEquiv : D.star (D.L ⊔ D.U) ≃* ClassicalOrthogonal.POmegaPlus 2 (ZMod 2) :=
  d.model.trans projectiveEquiv

/-- The ordered SL₂ factors give actual ordered S₃ factors. -/
def pairPermEquiv : PairSL (F := ZMod 2) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  MulEquiv.prodCongr (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)

/-- The starred quotient has two concrete symmetric factors, not just an order or tag. -/
def starSymmetricEquiv : D.star (D.L ⊔ D.U) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  d.model.trans pairPermEquiv

/-- Lift star generation through O₂(LT), applying the actual O²(L)=L hypothesis. -/
theorem I_eq_LU_of_star (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    D.I g = D.L ⊔ D.U :=
  binary_I_eq_join_of_star_eq d.base d.closure.normal.1 g d.g_mem hstar

theorem I_product_of_star (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    (D.I g : Set G) = (D.L : Set G) * (D.U : Set G) :=
  binary_I_product_of_star_eq d.base d.closure.normal.1 g d.g_mem hstar

theorem g_mem_I_of_star (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) : g ∈ D.I g := by
  rw [d.I_eq_LU_of_star hstar]
  exact mem_sup_left d.g_mem

theorem LT_normalizes_I_of_star (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    D.LT ≤ normalizer (D.I g : Set G) := by
  rw [d.I_eq_LU_of_star hstar]
  exact d.LT_normalizes_LU

theorem S_eq_star_kernel_of_star (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    D.S g = D.I g ⊓ D.LT.pCoreIn 2 :=
  core_eq_inf_of_normalizes d.I_le_LT (d.LT_normalizes_I_of_star hstar)

/-- The core of I lies in the original Sylow, which normalizes U. -/
theorem S_le_T_of_star (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) : D.S g ≤ D.T := by
  rw [d.S_eq_star_kernel_of_star hstar]
  exact inf_le_right.trans d.base.binary_core_le_T

theorem S_normalizes_U_of_star (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    D.S g ≤ normalizer (D.U : Set G) :=
  (d.S_le_T_of_star hstar).trans d.base.binary_T_normalizes_U

/-- Restrict the original LU star projection to I, with no chosen inverse or new quotient. -/
def IStarProjection : D.I g →* D.star (D.L ⊔ D.U) :=
  (starProjection D (D.L ⊔ D.U) d.LU_le_LT).comp (inclusion d.I_le_LU)

theorem IStarProjection_surjective (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    Function.Surjective d.IStarProjection := by
  intro q
  have hq : (q : D.Star) ∈ D.star (D.I g) := hstar.symm ▸ q.property
  obtain ⟨a, ha, he⟩ := hq
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

theorem IStarProjection_ker (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    d.IStarProjection.ker = pCore 2 (D.I g) := by
  have he : d.IStarProjection.ker = (starProjection D (D.I g) d.I_le_LT).ker := by
    ext i
    change d.IStarProjection i = 1 ↔ starProjection D (D.I g) d.I_le_LT i = 1
    simp only [Subtype.ext_iff]
    rfl
  rw [he]
  exact starProjection_ker_of_normalizes d.I_le_LT (d.LT_normalizes_I_of_star hstar)

/-- The intrinsic quotient of I is the actual starred LU, by the original projection. -/
def coreQuotientStarEquiv (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    (D.I g ⧸ pCore 2 (D.I g)) ≃* D.star (D.L ⊔ D.U) :=
  (QuotientGroup.quotientMulEquivOfEq (d.IStarProjection_ker hstar).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.IStarProjection
      (d.IStarProjection_surjective hstar))

theorem coreQuotientStarEquiv_mk (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) (i : D.I g) :
    d.coreQuotientStarEquiv hstar (QuotientGroup.mk' (pCore 2 (D.I g)) i) =
      d.IStarProjection i := rfl

/-- The quotient model carries the same ordered factors as the given natural action. -/
def coreQuotientEquiv (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    (D.I g ⧸ pCore 2 (D.I g)) ≃* PairSL (F := ZMod 2) :=
  (d.coreQuotientStarEquiv hstar).trans d.model

theorem coreQuotientEquiv_mk (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) (i : D.I g) :
    d.coreQuotientEquiv hstar (QuotientGroup.mk' (pCore 2 (D.I g)) i) =
      d.matrixProjection (inclusion d.I_le_LU i) := rfl

/-- Equivariance in these comparisons is the supplied literal conjugation identity. -/
theorem coreQuotientEquiv_equivariant (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U))
    (i : D.I g) (v : D.VL) :
    (d.coordinates.symm (Multiplicative.ofAdd
      (matrixAction (d.coreQuotientEquiv hstar (QuotientGroup.mk' (pCore 2 (D.I g)) i))
        (d.coordinates v).toAdd)) : G) = (i : G) * v * (i : G)⁻¹ :=
  d.equivariant (inclusion d.I_le_LU i) v

/-- The literal quotient also identifies with the actual orthogonal group. -/
def coreOrthogonalEquiv (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    (D.I g ⧸ pCore 2 (D.I g)) ≃* ClassicalOrthogonal.POmegaPlus 2 (ZMod 2) :=
  (d.coreQuotientEquiv hstar).trans projectiveEquiv

def coreSymmetricEquiv (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    (D.I g ⧸ pCore 2 (D.I g)) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  (d.coreQuotientEquiv hstar).trans pairPermEquiv

/-- The source index is the order of the original starred U. -/
theorem W_index_of_star (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    (D.W g).relIndex D.U = Nat.card (D.star D.U) := by
  have hk : (D.binaryStarRestriction (D.I g) d.I_le_LT).ker = pCore 2 (D.I g) := by
    rw [← d.IStarProjection_ker hstar]
    ext i
    change _ = 1 ↔ d.IStarProjection i = 1
    rw [Subtype.ext_iff]
    rfl
  have hUI : D.U ≤ D.I g := le_sup_left
  calc
    (D.W g).relIndex D.U = (D.S g).relIndex D.U := inf_relIndex_left _ _
    _ = (pCore 2 (D.I g)).relIndex (D.U.subgroupOf (D.I g)) := by
      rw [← relIndex_map_map_of_injective _ _ (D.I g).subtype_injective,
        map_subgroupOf_eq_of_le hUI]
      rfl
    _ = (D.binaryStarRestriction (D.I g) d.I_le_LT).ker.relIndex
        (D.U.subgroupOf (D.I g)) := by rw [hk]
    _ = Nat.card ((D.U.subgroupOf (D.I g)).map
        (D.binaryStarRestriction (D.I g) d.I_le_LT)) := relIndex_ker _ _
    _ = Nat.card (D.star D.U) := by rw [binaryStarRestriction_map _ _ _ hUI]

/-- The already proved normal-layer argument now needs only starred generation. -/
theorem layers_of_star (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    D.VL ≤ S₂ D g ∧ S₂ D g ≤ D.S g ∧
      (D.VL.subgroupOf (D.I g)).Normal ∧ ((S₂ D g).subgroupOf (D.I g)).Normal ∧
      ⁅S₂ D g, D.I g⁆ ≤ D.VL :=
  d.layers (d.I_eq_LU_of_star hstar)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
