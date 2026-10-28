module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Layers
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.Generation
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PCoreImage

/-!
# Star maps and the core-product reduction in G.2.4

Starred generation lifts through the normalizing two-core supplement using
L=O²(L), retaining the original conjugator. Relative normality in LT then
identifies O₂(I) with I∩O₂(LT). All quotient comparisons below use the actual
star projection. For P=WWᵍ, normalization proves the literal product and
centrality of S/P in I/P. The A₅ Borel and generation calculations remain
explicit inputs; these reductions do not assert the complete source theorem.

The generation and centrality arguments are the same group-theoretic steps
as in the higher-field G.2.3 reduction; they do not require its natural module.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(1–3), printed pp.334–335, using G.2.3 on pp.333–334.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {g : G} (d : Hypothesis D g)

/-- The two-factor product before eliminating the central kernel. -/
def WProduct (D : Setup G) (g : G) : Subgroup G := D.W g ⊔ conjugate (D.W g) g

omit [Finite G] in
private theorem normalizes_conjugate {K A : Subgroup G} (x : G)
    (hx : x ∈ normalizer (K : Set G)) (hKA : K ≤ normalizer (A : Set G)) :
    K ≤ normalizer (conjugate A x : Set G) := by
  have he : K.map (MulAut.conj x⁻¹).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (K : Set G)).inv_mem hx)
  have hm := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hKA).trans
    (A.le_normalizer_map (MulAut.conj x⁻¹).toMonoidHom)
  rwa [he] at hm

namespace Hypothesis
include d

theorem I_le_LT : D.I g ≤ D.LT := binary_I_le_LT d.setup.U_normal_in_T.1 d.g_mem

/-- The residual-generation proof already available in the binary development
has no field-size assumption, and applies to this literal orthogonal A₅ setup. -/
theorem I_eq_LU_of_star (hstar : D.star D.L ≤ D.star (D.I g)) : D.I g = D.L ⊔ D.U := by
  apply binary_I_eq_join_of_star_eq d.setup.toBaseHypothesis d.setup.U_normal_in_T.1 g d.g_mem
  apply le_antisymm (binary_star_mono (binary_I_le_join d.g_mem))
  rw [binary_star_sup _ _ le_sup_left (d.setup.U_normal_in_T.1.trans le_sup_right)]
  exact sup_le hstar (binary_star_mono le_sup_left)

theorem L_le_I_of_star (hstar : D.star D.L ≤ D.star (D.I g)) : D.L ≤ D.I g := by
  rw [d.I_eq_LU_of_star hstar]
  exact le_sup_left

/-- The original g, rather than a replacement, lies in I after generation. -/
theorem g_mem_I_of_star (hstar : D.star D.L ≤ D.star (D.I g)) : g ∈ D.I g :=
  d.L_le_I_of_star hstar d.g_mem

theorem I_product_of_star (hstar : D.star D.L ≤ D.star (D.I g)) :
    (D.I g : Set G) = (D.L : Set G) * (D.U : Set G) := by
  rw [d.I_eq_LU_of_star hstar]
  exact coe_mul_of_right_le_normalizer_left _ _ (d.setup.U_normal_in_T.1.trans d.setup.T_normalizes_L)

theorem LT_normalizes_I_of_star (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.LT ≤ normalizer (D.I g : Set G) := by
  apply sup_le ((d.L_le_I_of_star hstar).trans (D.I g).le_normalizer)
  rw [d.I_eq_LU_of_star hstar]
  exact (le_inf d.setup.T_normalizes_L d.setup.toBaseHypothesis.binary_T_normalizes_U).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit d [Finite G] in
theorem I_normalizes_core : D.I g ≤ normalizer (D.S g : Set G) :=
  (D.I g).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)

omit d [Finite G] in
theorem conjugate_W (hg : g ∈ D.I g) :
    conjugate (D.W g) g = conjugate D.U g ⊓ D.S g := by
  have hS : conjugate (D.S g) g = D.S g :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D.S g : Set G)).inv_mem (I_normalizes_core hg))
  change (D.U ⊓ D.S g).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective]
  exact congrArg (conjugate D.U g ⊓ ·) hS

theorem S_le_LT_core_of_star (hstar : D.star D.L ≤ D.star (D.I g)) : D.S g ≤ D.LT.pCoreIn 2 :=
  le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (D.I g))
    ((pCoreIn_le 2 (D.I g)).trans (d.I_le_LT))
    ((d.LT_normalizes_I_of_star hstar).trans
      (normalizer_le_normalizer_characteristic_image _ _))

theorem S_normalizes_U_of_star (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.S g ≤ normalizer (D.U : Set G) :=
  (d.S_le_LT_core_of_star hstar).trans
    (d.setup.toBaseHypothesis.binary_core_le_T.trans
      d.setup.toBaseHypothesis.binary_T_normalizes_U)

theorem S_normalizes_marked_of_star (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.S g ≤ normalizer (conjugate D.U g : Set G) :=
  normalizes_conjugate g (I_normalizes_core (d.g_mem_I_of_star hstar))
    (d.S_normalizes_U_of_star hstar)

/-- Relative normality in LT proves the comparison of the two cores. -/
theorem S_eq_star_kernel_of_star (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.S g = D.I g ⊓ D.LT.pCoreIn 2 := by
  apply le_antisymm (le_inf (pCoreIn_le 2 _) (d.S_le_LT_core_of_star hstar))
  apply le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 D.LT).of_injective (inclusion inf_le_right) (inclusion_injective _))
    inf_le_left
  have hnorm : D.LT ≤ normalizer (D.LT.pCoreIn 2 : Set G) :=
    D.LT.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)
  exact (le_inf (D.I g).le_normalizer ((d.I_le_LT).trans hnorm)).trans
    inf_normalizer_le_normalizer_inf

/-- The restriction of the original star map, with target the original L*.
The equality of starred images is the remaining matrix-generation input. -/
def IStarProjection (hstar : D.star (D.I g) = D.star D.L) : D.I g →* D.star D.L :=
  ((QuotientGroup.mk' (pCore 2 D.LT)).comp (inclusion (d.I_le_LT))).codRestrict _
    (fun i => hstar ▸ (show QuotientGroup.mk' (pCore 2 D.LT)
      (inclusion (d.I_le_LT) i) ∈ D.star (D.I g) from
        ⟨inclusion (d.I_le_LT) i, i.property, rfl⟩))

theorem IStarProjection_surjective (hstar : D.star (D.I g) = D.star D.L) :
    Function.Surjective (d.IStarProjection hstar) := by
  intro q
  have hq : (q : D.Star) ∈ D.star (D.I g) := by rw [hstar]; exact q.property
  obtain ⟨i, hi, he⟩ := hq
  exact ⟨⟨i, hi⟩, Subtype.ext he⟩

theorem IStarProjection_ker (hstar : D.star (D.I g) = D.star D.L) :
    (d.IStarProjection hstar).ker = pCore 2 (D.I g) := by
  ext i
  have hs := d.S_eq_star_kernel_of_star hstar.ge
  have hiff : i ∈ (d.IStarProjection hstar).ker ↔ (i : G) ∈ D.LT.pCoreIn 2 := by
    change (d.IStarProjection hstar) i = 1 ↔ _
    rw [Subtype.ext_iff]
    change QuotientGroup.mk' (pCore 2 D.LT) (inclusion (d.I_le_LT) i) = 1 ↔ _
    change (QuotientGroup.mk (inclusion (d.I_le_LT) i) : D.Star) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hi
      exact ⟨_, hi, rfl⟩
    · rintro ⟨j, hj, he⟩
      exact (show j = inclusion (d.I_le_LT) i from Subtype.ext he) ▸ hj
  rw [hiff]
  constructor
  · intro hi
    have hiS : (i : G) ∈ D.S g := hs.symm ▸ ⟨i.property, hi⟩
    obtain ⟨j, hj, he⟩ := hiS
    exact (show j = i from Subtype.ext he) ▸ hj
  · intro hi
    have hiS : (i : G) ∈ D.S g := ⟨i, hi, rfl⟩
    exact (hs ▸ hiS).2

/-- The quotient comparison is induced by the source's actual star map. -/
noncomputable def coreQuotientEquiv (hstar : D.star (D.I g) = D.star D.L) :
    (D.I g ⧸ pCore 2 (D.I g)) ≃* alternatingGroup (Fin 5) :=
  ((QuotientGroup.quotientMulEquivOfEq (d.IStarProjection_ker hstar).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (d.IStarProjection hstar)
      (d.IStarProjection_surjective hstar))).trans d.model

theorem coreQuotientEquiv_mk (hstar : D.star (D.I g) = D.star D.L) (i : D.I g) :
    d.coreQuotientEquiv hstar (QuotientGroup.mk' (pCore 2 (D.I g)) i) =
      d.model (d.IStarProjection hstar i) := rfl

theorem coreQuotientEquiv_on_L (hstar : D.star (D.I g) = D.star D.L) (l : D.L) :
    d.coreQuotientEquiv hstar (QuotientGroup.mk' (pCore 2 (D.I g))
      (inclusion (d.L_le_I_of_star hstar.ge) l)) = d.model (starProjection D l) := rfl
/-- The source relative index is the order of the literal starred U-image. -/
theorem W_index_of_star (hstar : D.star (D.I g) = D.star D.L) :
    (D.W g).relIndex D.U = Nat.card (D.star D.U) := by
  let q := D.binaryStarRestriction (D.I g) (d.I_le_LT)
  have hker : q.ker = pCore 2 (D.I g) := by
    rw [← d.IStarProjection_ker hstar]
    ext i
    constructor
    · intro hi; exact Subtype.ext hi
    · intro hi; exact congrArg Subtype.val hi
  have hUI : D.U ≤ D.I g := le_sup_left
  have hU : (D.U.subgroupOf (D.I g)).map (D.I g).subtype = D.U :=
    map_subgroupOf_eq_of_le hUI
  calc
    (D.W g).relIndex D.U = (D.S g).relIndex D.U := inf_relIndex_left _ _
    _ = (pCore 2 (D.I g)).relIndex (D.U.subgroupOf (D.I g)) := by
      rw [← relIndex_map_map_of_injective _ _ (D.I g).subtype_injective, hU]
      rfl
    _ = q.ker.relIndex (D.U.subgroupOf (D.I g)) := by rw [hker]
    _ = Nat.card ((D.U.subgroupOf (D.I g)).map q) := relIndex_ker _ _
    _ = Nat.card (D.star D.U) := by rw [binaryStarRestriction_map _ _ _ hUI]

/-- The product is contained in S before the central-cover step. -/
theorem WProduct_le_S (hstar : D.star D.L ≤ D.star (D.I g)) : WProduct D g ≤ D.S g := by
  change D.W g ⊔ conjugate (D.W g) g ≤ _
  rw [conjugate_W (d.g_mem_I_of_star hstar)]
  exact sup_le inf_le_right inf_le_right

theorem S_normalizes_W_of_star (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.S g ≤ normalizer (D.W g : Set G) :=
  (le_inf (d.S_normalizes_U_of_star hstar) (D.S g).le_normalizer).trans
    inf_normalizer_le_normalizer_inf

/-- P is the literal ordered set product, not only the generated subgroup. -/
theorem WProduct_eq_product (hstar : D.star D.L ≤ D.star (D.I g)) :
    (WProduct D g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) := by
  have hWgS : conjugate (D.W g) g ≤ D.S g := by
    rw [conjugate_W (d.g_mem_I_of_star hstar)]
    exact inf_le_right
  exact coe_mul_of_right_le_normalizer_left _ _
    (hWgS.trans (d.S_normalizes_W_of_star hstar))

/-- Each generator of I centralizes S modulo the actual product P. -/
theorem commutator_S_I_le_WProduct (hstar : D.star D.L ≤ D.star (D.I g)) : ⁅D.S g, D.I g⁆ ≤ WProduct D g := by
  have hbound (A : Subgroup G) (hAI : A ≤ D.I g)
      (hSA : D.S g ≤ normalizer (A : Set G)) : ⁅A, D.S g⁆ ≤ A ⊓ D.S g :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hSA)
      (le_normalizer_iff_commutator_le_right.mp (hAI.trans I_normalizes_core))
  have hU : ⁅D.U, D.S g⁆ ≤ WProduct D g :=
    (hbound _ le_sup_left (d.S_normalizes_U_of_star hstar)).trans le_sup_left
  have hUg : ⁅conjugate D.U g, D.S g⁆ ≤ WProduct D g := by
    have hh := hbound _ le_sup_right (d.S_normalizes_marked_of_star hstar)
    rw [← conjugate_W (d.g_mem_I_of_star hstar)] at hh
    exact hh.trans le_sup_right
  have hgen : D.I g ≤ commutatorPreimage (D.I g) (D.S g) (WProduct D g) :=
    sup_le (le_commutatorPreimage le_sup_left hU) (le_commutatorPreimage le_sup_right hUg)
  have hPS := d.WProduct_le_S hstar
  have hIP : D.I g ≤ normalizer (WProduct D g : Set G) := by
    apply sup_le
    · exact le_normalizer_iff_commutator_le_right.mpr ((commutator_mono le_rfl hPS).trans hU)
    · exact le_normalizer_iff_commutator_le_right.mpr ((commutator_mono le_rfl hPS).trans hUg)
  rw [commutator_comm]
  exact (commutator_mono hgen le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hIP)

/-- Relative normality needed to form I/P. -/
theorem WProduct_normal (hstar : D.star D.L ≤ D.star (D.I g)) :
    ((WProduct D g).subgroupOf (D.I g)).Normal := by
  have hPS := d.WProduct_le_S hstar
  apply (normal_subgroupOf_iff_le_normalizer (hPS.trans (pCoreIn_le 2 _))).mpr
  exact le_normalizer_iff_commutator_le_left.mpr
    ((commutator_mono hPS le_rfl).trans (d.commutator_S_I_le_WProduct hstar))

/-- The literal U-kernel in I/P is W. -/
theorem U_inf_WProduct (hstar : D.star D.L ≤ D.star (D.I g)) : D.U ⊓ WProduct D g = D.W g :=
  le_antisymm (inf_le_inf_left _ (d.WProduct_le_S hstar))
    (le_inf inf_le_left le_sup_left)

/-- The outstanding kernel S/P is central in the literal quotient I/P. -/
theorem image_S_le_center_productQuotient (hstar : D.star D.L ≤ D.star (D.I g))
    [((WProduct D g).subgroupOf (D.I g)).Normal] :
    ((D.S g).subgroupOf (D.I g)).map
      (QuotientGroup.mk' ((WProduct D g).subgroupOf (D.I g))) ≤
        center (D.I g ⧸ (WProduct D g).subgroupOf (D.I g)) := by
  let q := QuotientGroup.mk' ((WProduct D g).subgroupOf (D.I g))
  have hc : ⁅(D.S g).subgroupOf (D.I g), (⊤ : Subgroup (D.I g))⁆ ≤
      (WProduct D g).subgroupOf (D.I g) := by
    intro x hx
    have hm := mem_map_of_mem (D.I g).subtype hx
    rw [map_commutator, map_subgroupOf_eq_of_le (show D.S g ≤ D.I g from pCoreIn_le 2 _),
      ← MonoidHom.range_eq_map, range_subtype] at hm
    exact d.commutator_S_I_le_WProduct hstar hm
  apply commutator_top_right_eq_bot_iff_le_center.mp
  rw [← map_top_of_surjective q (QuotientGroup.mk'_surjective _), ← map_commutator]
  exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hc)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
