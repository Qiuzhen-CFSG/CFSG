module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Source
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.Generation
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Generation and the central quotient in higher-field G.2.3

Starred generation lifts through the normalizing two-core supplement using
L=O²(L). This retains the original conjugator and makes I normal in LT.
Consequently O₂(I)=I∩O₂(LT), with quotient comparison induced by the literal
star projection. The natural geometry supplies the source series.

For P=WWᵍ, normalization proves that this is a subgroup product and that
[S,I]≤P. Thus the remaining central-cover problem is exactly S/P=1.
No vanishing or natural-module decomposition is assumed or asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3, printed pp.333–334, PDF pp.344–345.
-/

@[expose] public section
open Subgroup Matrix
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
open Setup
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g : G} (d : Hypothesis D F n g)

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

theorem I_le_LT (hUT : D.U ≤ D.T) : D.I g ≤ D.LT := binary_I_le_LT hUT d.g_mem

/-- The residual-generation proof already available in the binary development
has no field-size assumption, and applies to this literal higher-field I. -/
theorem I_eq_LU_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) : D.I g = D.L ⊔ D.U := by
  apply binary_I_eq_join_of_star_eq d.setup.toBaseHypothesis hUT g d.g_mem
  apply le_antisymm (binary_star_mono (binary_I_le_join d.g_mem))
  rw [binary_star_sup _ _ le_sup_left (hUT.trans le_sup_right)]
  exact sup_le hstar (binary_star_mono le_sup_left)

theorem L_le_I_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) : D.L ≤ D.I g := by
  rw [d.I_eq_LU_of_star hUT hstar]
  exact le_sup_left

/-- The original g, rather than a replacement, lies in I after generation. -/
theorem g_mem_I_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) : g ∈ D.I g :=
  d.L_le_I_of_star hUT hstar d.g_mem

theorem I_product_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) :
    (D.I g : Set G) = (D.L : Set G) * (D.U : Set G) := by
  rw [d.I_eq_LU_of_star hUT hstar]
  exact coe_mul_of_right_le_normalizer_left _ _ (hUT.trans d.setup.T_normalizes_L)

theorem LT_normalizes_I_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.LT ≤ normalizer (D.I g : Set G) := by
  apply sup_le ((d.L_le_I_of_star hUT hstar).trans (D.I g).le_normalizer)
  rw [d.I_eq_LU_of_star hUT hstar]
  exact (le_inf d.setup.T_normalizes_L d.setup.toBaseHypothesis.binary_T_normalizes_U).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit d [Field F] [Finite F] [Finite G] in
theorem I_normalizes_core : D.I g ≤ normalizer (D.S g : Set G) :=
  (D.I g).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)

omit d [Field F] [Finite F] [Finite G] in
theorem conjugate_W (hg : g ∈ D.I g) :
    conjugate (D.W g) g = conjugate D.U g ⊓ D.S g := by
  have hS : conjugate (D.S g) g = D.S g :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D.S g : Set G)).inv_mem (I_normalizes_core hg))
  change (D.U ⊓ D.S g).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective]
  exact congrArg (conjugate D.U g ⊓ ·) hS

theorem S_le_LT_core_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) : D.S g ≤ D.LT.pCoreIn 2 :=
  le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (D.I g))
    ((pCoreIn_le 2 (D.I g)).trans (d.I_le_LT hUT))
    ((d.LT_normalizes_I_of_star hUT hstar).trans
      (normalizer_le_normalizer_characteristic_image _ _))

theorem S_normalizes_U_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.S g ≤ normalizer (D.U : Set G) :=
  (d.S_le_LT_core_of_star hUT hstar).trans
    (d.setup.toBaseHypothesis.binary_core_le_T.trans
      d.setup.toBaseHypothesis.binary_T_normalizes_U)

theorem S_normalizes_marked_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.S g ≤ normalizer (conjugate D.U g : Set G) :=
  normalizes_conjugate g (I_normalizes_core (d.g_mem_I_of_star hUT hstar))
    (d.S_normalizes_U_of_star hUT hstar)

/-- Relative normality in LT proves the comparison of the two cores. -/
theorem S_eq_star_kernel_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.S g = D.I g ⊓ D.LT.pCoreIn 2 := by
  apply le_antisymm (le_inf (pCoreIn_le 2 _) (d.S_le_LT_core_of_star hUT hstar))
  apply le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 D.LT).of_injective (inclusion inf_le_right) (inclusion_injective _))
    inf_le_left
  have hnorm : D.LT ≤ normalizer (D.LT.pCoreIn 2 : Set G) :=
    D.LT.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)
  exact (le_inf (D.I g).le_normalizer ((d.I_le_LT hUT).trans hnorm)).trans
    inf_normalizer_le_normalizer_inf

/-- The I-series 1≤V≤S₂≤S, with all normalities relative to I and V central in S. -/
theorem series_of_star (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.V ≤ D.S₂ g ∧ D.S₂ g ≤ D.S g ∧
    (D.V.subgroupOf (D.I g)).Normal ∧
    ((D.S₂ g).subgroupOf (D.I g)).Normal ∧
    ((D.S g).subgroupOf (D.I g)).Normal ∧
    D.V ≤ centralizer (D.S g : Set G) ∧
    ⁅D.S₂ g, D.I g⁆ ≤ D.V ∧ IsElementaryAbelian 2 (D.S₂ g) := by
  obtain ⟨hVE, hES, hEN, hc, he⟩ := d.intersection hUT hf
  have hVI : D.V ≤ D.I g := (le_conjugateSpanBy _ _).trans le_sup_left
  exact ⟨hVE, hES, (normal_subgroupOf_iff_le_normalizer hVI).mpr (d.I_normalizes hUT),
    hEN, (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 _)).mpr I_normalizes_core,
    (d.central_first hUT hf (d.L_le_I_of_star hUT hstar)).trans inf_le_right, hc, he⟩

/-- The restriction of the original star map, with target the original L*.
The equality of starred images is the remaining matrix-generation input. -/
def IStarProjection (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) : D.I g →* D.star D.L :=
  ((QuotientGroup.mk' (pCore 2 D.LT)).comp (inclusion (d.I_le_LT hUT))).codRestrict _
    (fun i => hstar ▸ (show QuotientGroup.mk' (pCore 2 D.LT)
      (inclusion (d.I_le_LT hUT) i) ∈ D.star (D.I g) from
        ⟨inclusion (d.I_le_LT hUT) i, i.property, rfl⟩))

theorem IStarProjection_surjective (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) :
    Function.Surjective (d.IStarProjection hUT hstar) := by
  intro q
  have hq : (q : D.Star) ∈ D.star (D.I g) := by rw [hstar]; exact q.property
  obtain ⟨i, hi, he⟩ := hq
  exact ⟨⟨i, hi⟩, Subtype.ext he⟩

theorem IStarProjection_ker (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) :
    (d.IStarProjection hUT hstar).ker = pCore 2 (D.I g) := by
  ext i
  have hs := d.S_eq_star_kernel_of_star hUT hstar.ge
  have hiff : i ∈ (d.IStarProjection hUT hstar).ker ↔ (i : G) ∈ D.LT.pCoreIn 2 := by
    change (d.IStarProjection hUT hstar) i = 1 ↔ _
    rw [Subtype.ext_iff]
    change QuotientGroup.mk' (pCore 2 D.LT) (inclusion (d.I_le_LT hUT) i) = 1 ↔ _
    change (QuotientGroup.mk (inclusion (d.I_le_LT hUT) i) : D.Star) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hi
      exact ⟨_, hi, rfl⟩
    · rintro ⟨j, hj, he⟩
      exact (show j = inclusion (d.I_le_LT hUT) i from Subtype.ext he) ▸ hj
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
noncomputable def coreQuotientEquiv (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) :
    (D.I g ⧸ pCore 2 (D.I g)) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  ((QuotientGroup.quotientMulEquivOfEq (d.IStarProjection_ker hUT hstar).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (d.IStarProjection hUT hstar)
      (d.IStarProjection_surjective hUT hstar))).trans d.model

theorem coreQuotientEquiv_mk (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) (i : D.I g) :
    d.coreQuotientEquiv hUT hstar (QuotientGroup.mk' (pCore 2 (D.I g)) i) =
      d.model (d.IStarProjection hUT hstar i) := rfl

theorem coreQuotientEquiv_on_L (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) (l : D.L) :
    d.coreQuotientEquiv hUT hstar (QuotientGroup.mk' (pCore 2 (D.I g))
      (inclusion (d.L_le_I_of_star hUT hstar.ge) l)) = d.model (starProjection D l) := rfl

theorem LT_core_centralizes_V : D.LT.pCoreIn 2 ≤ centralizer (D.V : Set G) := by
  let := d.setup.elementary
  exact pCoreIn_le_centralizer_of_irreducible D.V D.L D.LT
    (IsElementaryAbelian.isPGroup 2 D.V) (d.setup.V_le_T.trans le_sup_right)
    (sup_le (normalizes_of_span D d.span_eq) d.setup.T_normalizes_V) le_sup_left d.irreducible

/-- The comparison also preserves conjugation on the actual natural module,
for every element of I, rather than only for the original subgroup L. -/
theorem IStarProjection_equivariant (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) (i : D.I g) (v : D.V) :
    (d.coordinates ⟨(i : G) * v * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes hUT i.property) v).mp v.property⟩).toAdd =
      (d.model (d.IStarProjection hUT hstar i)).val *ᵥ (d.coordinates v).toAdd := by
  obtain ⟨l, hl⟩ := starProjection_surjective D (d.IStarProjection hUT hstar i)
  have he : QuotientGroup.mk' (pCore 2 D.LT) (inclusion (d.I_le_LT hUT) i) =
      QuotientGroup.mk' (pCore 2 D.LT) (inclusion (show D.L ≤ D.LT from le_sup_left) l) :=
    (congrArg Subtype.val hl).symm
  let k : D.LT := inclusion (d.I_le_LT hUT) i *
    (inclusion (show D.L ≤ D.LT from le_sup_left) l)⁻¹
  have hk : k ∈ pCore 2 D.LT := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 D.LT) k = 1
    simp only [k, map_mul, map_inv, he, mul_inv_cancel]
  have hkc := d.LT_core_centralizes_V (show (k : G) ∈ D.LT.pCoreIn 2 from ⟨k, hk, rfl⟩)
  have hvl : (l : G) * v * (l : G)⁻¹ ∈ D.V :=
    (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) v).mp v.property
  have hc := hkc _ hvl
  have hc' : (k : G) * ((l : G) * v * (l : G)⁻¹) * (k : G)⁻¹ =
      (l : G) * v * (l : G)⁻¹ := by
    rw [← hc, mul_inv_cancel_right]
  have hconj : (i : G) * v * (i : G)⁻¹ = (l : G) * v * (l : G)⁻¹ := by
    calc
      _ = (k : G) * ((l : G) * v * (l : G)⁻¹) * (k : G)⁻¹ := by
        change _ = ((i : G) * (l : G)⁻¹) * ((l : G) * v * (l : G)⁻¹) *
          ((i : G) * (l : G)⁻¹)⁻¹
        group
      _ = _ := hc'
  have heq : (⟨(i : G) * v * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes hUT i.property) v).mp v.property⟩ : D.V) =
      ⟨(l : G) * v * (l : G)⁻¹, hvl⟩ := Subtype.ext hconj
  rw [heq, ← hl]
  exact d.equivariant l v

/-- Natural conjugation through I/O₂(I), with the same quotient map used
by `coreQuotientEquiv`. -/
theorem coreQuotientEquiv_equivariant (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) (i : D.I g) (v : D.V) :
    (d.coordinates ⟨(i : G) * v * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes hUT i.property) v).mp v.property⟩).toAdd =
      (d.coreQuotientEquiv hUT hstar (QuotientGroup.mk' (pCore 2 (D.I g)) i)).val *ᵥ
        (d.coordinates v).toAdd :=
  d.IStarProjection_equivariant hUT hstar i v


/-- The source relative index is the order of the literal starred U-image. -/
theorem W_index_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star (D.I g) = D.star D.L) :
    (D.W g).relIndex D.U = Nat.card (D.star D.U) := by
  let q := D.binaryStarRestriction (D.I g) (d.I_le_LT hUT)
  have hker : q.ker = pCore 2 (D.I g) := by
    rw [← d.IStarProjection_ker hUT hstar]
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

/-- The numerical conclusion (7) from the two remaining module indices.
The module branch must supply the same multiplicity s as its natural decomposition. -/
theorem order_of_natural_indices (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star (D.I g) = D.star D.L)
    (hU : Nat.card (D.star D.U) = 2 ^ n) (s : ℕ)
    (hW : (D.S₂ g).relIndex (D.W g) = 2 ^ (n * s)) :
    Nat.card D.U = 2 ^ (n * (s + 3)) * D.V.relIndex (D.S₂ g) := by
  have hl := d.intersection hUT hf
  have hEW : D.S₂ g ≤ D.W g := le_inf inf_le_left hl.2.1
  have ht := relIndex_mul_relIndex (D.S₂ g) (D.W g) D.U hEW inf_le_left
  have hv := relIndex_mul_relIndex D.V (D.S₂ g) D.U hl.1 inf_le_left
  have hb := relIndex_mul_relIndex (⊥ : Subgroup G) D.V D.U bot_le
    (hl.1.trans inf_le_left)
  rw [relIndex_bot_left, relIndex_bot_left, d.card_V] at hb
  rw [hW, d.W_index_of_star hUT hstar, hU] at ht
  rw [← hv, ← ht] at hb
  rw [← hb, Nat.mul_add, pow_add]
  have hexp : n * 3 = n + 2 * n := by omega
  rw [hexp, pow_add]
  ring

/-- The product is contained in S before the central-cover step. -/
theorem WProduct_le_S (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) : WProduct D g ≤ D.S g := by
  change D.W g ⊔ conjugate (D.W g) g ≤ _
  rw [conjugate_W (d.g_mem_I_of_star hUT hstar)]
  exact sup_le inf_le_right inf_le_right

theorem S_normalizes_W_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) :
    D.S g ≤ normalizer (D.W g : Set G) :=
  (le_inf (d.S_normalizes_U_of_star hUT hstar) (D.S g).le_normalizer).trans
    inf_normalizer_le_normalizer_inf

/-- P is the literal ordered set product, not only the generated subgroup. -/
theorem WProduct_eq_product (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) :
    (WProduct D g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) := by
  have hWgS : conjugate (D.W g) g ≤ D.S g := by
    rw [conjugate_W (d.g_mem_I_of_star hUT hstar)]
    exact inf_le_right
  exact coe_mul_of_right_le_normalizer_left _ _
    (hWgS.trans (d.S_normalizes_W_of_star hUT hstar))

/-- Each generator of I centralizes S modulo the actual product P. -/
theorem commutator_S_I_le_WProduct (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) : ⁅D.S g, D.I g⁆ ≤ WProduct D g := by
  have hbound (A : Subgroup G) (hAI : A ≤ D.I g)
      (hSA : D.S g ≤ normalizer (A : Set G)) : ⁅A, D.S g⁆ ≤ A ⊓ D.S g :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hSA)
      (le_normalizer_iff_commutator_le_right.mp (hAI.trans I_normalizes_core))
  have hU : ⁅D.U, D.S g⁆ ≤ WProduct D g :=
    (hbound _ le_sup_left (d.S_normalizes_U_of_star hUT hstar)).trans le_sup_left
  have hUg : ⁅conjugate D.U g, D.S g⁆ ≤ WProduct D g := by
    have hh := hbound _ le_sup_right (d.S_normalizes_marked_of_star hUT hstar)
    rw [← conjugate_W (d.g_mem_I_of_star hUT hstar)] at hh
    exact hh.trans le_sup_right
  have hgen : D.I g ≤ commutatorPreimage (D.I g) (D.S g) (WProduct D g) :=
    sup_le (le_commutatorPreimage le_sup_left hU) (le_commutatorPreimage le_sup_right hUg)
  have hPS := d.WProduct_le_S hUT hstar
  have hIP : D.I g ≤ normalizer (WProduct D g : Set G) := by
    apply sup_le
    · exact le_normalizer_iff_commutator_le_right.mpr ((commutator_mono le_rfl hPS).trans hU)
    · exact le_normalizer_iff_commutator_le_right.mpr ((commutator_mono le_rfl hPS).trans hUg)
  rw [commutator_comm]
  exact (commutator_mono hgen le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hIP)

/-- Relative normality needed to form I/P. -/
theorem WProduct_normal (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) :
    ((WProduct D g).subgroupOf (D.I g)).Normal := by
  have hPS := d.WProduct_le_S hUT hstar
  apply (normal_subgroupOf_iff_le_normalizer (hPS.trans (pCoreIn_le 2 _))).mpr
  exact le_normalizer_iff_commutator_le_left.mpr
    ((commutator_mono hPS le_rfl).trans (d.commutator_S_I_le_WProduct hUT hstar))

/-- The literal U-kernel in I/P is W. -/
theorem U_inf_WProduct (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g)) : D.U ⊓ WProduct D g = D.W g :=
  le_antisymm (inf_le_inf_left _ (d.WProduct_le_S hUT hstar))
    (le_inf inf_le_left le_sup_left)

/-- The outstanding kernel S/P is central in the literal quotient I/P. -/
theorem image_S_le_center_productQuotient (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (D.I g))
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
    exact d.commutator_S_I_le_WProduct hUT hstar hm
  apply commutator_top_right_eq_bot_iff_le_center.mp
  rw [← map_top_of_surjective q (QuotientGroup.mk'_surjective _), ← map_commutator]
  exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hc)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
