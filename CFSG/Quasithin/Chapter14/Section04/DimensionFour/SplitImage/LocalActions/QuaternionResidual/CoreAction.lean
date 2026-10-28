module

public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.LocalActions.Inputs
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.QuaternionResidual.CoreAction
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry.Basic
public import Theory.GroupTheory.PResidual.Defs
public import Theory.PGroupCore

/-!
# The extra two-core action in the split dimension-four branch

We retain H = G₁, U = ⟨Vᴴ⟩, V = O₂(L), U = O₂(L₁), the actual
PSL₃(2) quotient of L, and the kernel O₂(H) of H acting on U/Z(U).
For the source element g ∈ L − H and a ∈ Uᵍ, the quaternion commutator
lies in Z(Uᵍ), while Z(U) ∩ Z(Uᵍ) = 1 because H = C_G(Z(U)). Here Uᵍ
means the image under conjugation by g⁻¹, as in the book's right-conjugation
convention. Only the selected a is assumed involutory.

The missing normalization input is C_G(V) ≤ N_G(L). In the standing
source setup this is C_G(V) ≤ M_V ≤ M = N_G(L), used in the proof of
12.8.4(4), with M defined in 12.8.2. Combined with C_L(V) ≤ V for the
natural block, it controls elements of C_G(U) through the actual block.
The generic block calculation then proves that they centralize A. Inner
correction in U gives exactly the required action of the extra two-core.

The output concerns the literal K = (O²(H)).map H.subtype and
Q = (O₂(H)).map H.subtype, with R = K ∩ N_G(A). Neither U = Q nor
self-centralization of U is assumed. The bound is independent of K*'s order
and therefore applies to both d = 4 alternatives before the outer
index-three calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007, and 12.8.2, 12.8.4, 12.8.9–11, pp.849–854.
The normal-closure, block-centralizer and action-kernel facts remain
explicit earlier-source inputs. The source assembly must supply them and
the marked block/core identifications. The conjugate displacement and
center separation are proved here from that arrangement. This module
proves the two-core calculation, not the complete 14.4.4 theorem.
-/

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.QuaternionCoreAction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem disjoint_conjugate_of_card_two
    (Z : Subgroup G) (hZ : Nat.card Z = 2) (g : G)
    (hg : g ∉ centralizer (Z : Set G)) :
    Disjoint Z (Z.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  apply disjoint_def.mpr
  intro x hx hxg
  by_contra hne
  obtain ⟨y, hy, he⟩ := hxg
  have hyne : y ≠ 1 := by
    intro h
    apply hne
    simpa only [h, map_one] using he.symm
  have hxy : x = y := congrArg Subtype.val
    ((hz ⟨x, hx⟩ (fun h => hne (congrArg Subtype.val h))).trans
      (hz ⟨y, hy⟩ (fun h => hyne (congrArg Subtype.val h))).symm)
  have hgy : g * y = y * g := by
    have hh : g * y * g⁻¹ = y := he.trans hxy
    exact mul_inv_eq_iff_eq_mul.mp hh
  apply hg
  intro w hw
  by_cases hw1 : w = 1
  · simp only [hw1, one_mul, mul_one]
  · have hwy : w = y := congrArg Subtype.val
      ((hz ⟨w, hw⟩ (fun h => hw1 (congrArg Subtype.val h))).trans
        (hz ⟨y, hy⟩ (fun h => hyne (congrArg Subtype.val h))).symm)
    rw [hwy]
    exact hgy.symm

/-- Conjugation on the actual central quotient of the embedded U. -/
@[expose] public def quotientAction (H U : Subgroup G) (hHU : H ≤ normalizer (U : Set G)) :
    H →* MulAut (U ⧸ center U) :=
  (quotientAut (center U)).comp (U.normalizerMonoidHom.comp (inclusion hHU))

/-- The genuine block and conjugate-core arrangement control the extra
O₂(H) action on the source sixteen. The relative index is taken in the
literal intersection R ∩ Q, with R = K ∩ N_G(A). -/
public theorem image_and_index
    (H L L₁ V U A TL : Subgroup G)
    (hL₁L : L₁ ≤ L)
    (hVcore : V = (pCore 2 L).map L.subtype)
    (hUcore : U = (pCore 2 L₁).map L₁.subtype)
    (hclosure : U = (normalClosure (V.subgroupOf H : Set H)).map H.subtype)
    (hVU : V ≤ U) (hV : Nat.card V = 8)
    (d : QuaternionCentralProductData U)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.PSL)
    (hfaith : L ⊓ centralizer (V : Set G) ≤ V)
    (hblock : centralizer (V : Set G) ≤ normalizer (L : Set G))
    (hHU : H ≤ normalizer (U : Set G))
    (hkernel : (quotientAction H U hHU).ker = pCore 2 H)
    (hUK : U ≤ (pResidual 2 H).map H.subtype)
    (g a : G) (haL : a ∈ L) (ha : a ^ 2 = 1) (hout : a ∉ U)
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype)
    (hH : H = centralizer ((center U).map U.subtype : Set G))
    (hgL : g ∈ L) (hgH : g ∉ H)
    (haUg : a ∈ U.map (MulAut.conj g⁻¹).toMonoidHom)
    (hA : A = zpowers a ⊔ ⁅U, zpowers a⁆)
    (hTL : TL = U ⊔ zpowers a)
    (hTLN : TL ≤ normalizer (A : Set G)) :
    QuaternionResidual.image A
      (((pResidual 2 H).map H.subtype ⊓ normalizer (A : Set G)) ⊓
        (pCore 2 H).map H.subtype) = QuaternionResidual.image A U ∧
    (centralizer (A : Set G)).relIndex
      (((pResidual 2 H).map H.subtype ⊓ normalizer (A : Set G)) ⊓
        (pCore 2 H).map H.subtype) = 4 := by
  let Q := (pCore 2 H).map H.subtype
  let K := (pResidual 2 H).map H.subtype
  have hUL : U ≤ L := by rw [hUcore]; exact (map_subtype_le _).trans hL₁L
  have hUH : U ≤ H := by rw [hclosure]; exact map_subtype_le _
  have hVident : V.subgroupOf L = pCore 2 L := by
    rw [hVcore]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  let : (V.subgroupOf L).Normal := by rw [hVident]; infer_instance
  let eV : (L ⧸ V.subgroupOf L) ≃* Matrix.PSL3Two.PSL :=
    (QuotientGroup.quotientMulEquivOfEq hVident).trans e
  have haU : a ∈ normalizer (U : Set G) := by
    have hf := (d.elementary_sixteen_of_swap U a ha hout hswap).1
    exact (le_normalizer_iff_commutator_le_left.mpr
      (hf ▸ inf_le_left)) (mem_zpowers a)
  have hLV : L ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hVU.trans hUL)).mp inferInstance
  have hVUg : V ≤ U.map (MulAut.conj g⁻¹).toMonoidHom := by
    have he := mem_normalizer_iff_map_conj_eq.mp (hLV (L.inv_mem hgL))
    rw [← he]
    exact map_mono hVU
  have hcommUU : ⁅U, U⁆ ≤ (center U).map U.subtype := by
    apply commutator_le.mpr
    intro x hx y hy
    exact ⟨⁅(⟨x, hx⟩ : U), ⟨y, hy⟩⁆, d.commutator_mem_center _ _, rfl⟩
  have hmove : ⁅V, zpowers a⁆ ≤
      ((center U).map U.subtype).map (MulAut.conj g⁻¹).toMonoidHom := by
    apply (commutator_mono hVUg (zpowers_le.mpr haUg)).trans
    rw [← map_commutator]
    exact map_mono hcommUU
  have hcenters := disjoint_conjugate_of_card_two ((center U).map U.subtype)
    (by rw [card_map_of_injective U.subtype_injective, d.center_card]) g⁻¹
    (by simpa only [← hH, inv_mem_iff] using hgH)
  have hdisj : Disjoint (U ⊓ centralizer (U : Set G)) ⁅V, zpowers a⁆ := by
    apply disjoint_def.mpr
    intro x hx hm
    have hxZ : x ∈ (center U).map U.subtype := by
      refine ⟨⟨x, hx.1⟩, mem_center_iff.mpr ?_, rfl⟩
      intro u
      exact Subtype.ext (hx.2 u u.property)
    exact disjoint_def.mp hcenters hxZ (hmove hm)
  have hfix := QuaternionResidual.core_centralizer_fixes_A_of_block L V U A hUL hVU
    d hV eV hfaith hblock a haL ha hout haU hdisj hA
  have hUQ : U ≤ Q := by
    intro u hu
    refine ⟨⟨u, hUH hu⟩, ?_, rfl⟩
    rw [← hkernel]
    change quotientAut (center U)
      (U.normalizerMonoidHom ⟨u, hHU (hUH hu)⟩) = 1
    apply (d.quotientAut_eq_one_iff_inner _).mpr
    exact ⟨⟨u, hu⟩, MulEquiv.ext (fun _ => rfl)⟩
  have hQU : Q ≤ normalizer (U : Set G) := (map_subtype_le _).trans hHU
  have hUN : U ≤ normalizer (A : Set G) := (hTL ▸ le_sup_left).trans hTLN
  have hquotient (q : Q) : quotientAut (center U)
      (U.normalizerMonoidHom (inclusion hQU q)) = 1 := by
    obtain ⟨x, hx, he⟩ := q.property
    have hx' : x ∈ (quotientAction H U hHU).ker := hkernel ▸ hx
    have heN : (⟨q, hQU q.property⟩ : normalizer (U : Set G)) =
        inclusion hHU x := Subtype.ext he.symm
    change quotientAut (center U) (U.normalizerMonoidHom ⟨q, hQU q.property⟩) = 1
    rw [heN]
    exact hx'
  have himage := QuaternionResidual.image_core_intersection_eq U A Q K d
    hUQ hUK hUN hQU hquotient hfix
  refine ⟨himage, ?_⟩
  have hKU : K ≤ normalizer (U : Set G) := (map_subtype_le _).trans hHU
  obtain ⟨heq, hfour, _, _⟩ := QuaternionResidual.common_image_of_swap U A TL K
    d a ha hout hswap hA hTL hTLN hUK hKU
  rw [← QuaternionResidual.card_image_eq_relIndex A _ (inf_le_left.trans inf_le_right),
    himage, ← heq]
  exact hfour
end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.QuaternionCoreAction
