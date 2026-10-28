module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers

/-!
# The residual involution cover from the earlier local geometry

`residual_cover_of_earlier_geometry` proves the conclusion of 15.3.61(2)
for the literal two-residual `residualK Z`. The permitted earlier inputs
are the actual natural/dual recognition and geometry through 15.3.59,
the compatible actions on V and P/V, the action kernel from 15.3.48(3),
V = Z(P) from 15.3.55, the order-four U-action and marked orthogonal
hyperplane from 15.3.51–53, and the Sylow conclusion of 15.3.59(2)
(rewritten using I = YU from 15.3.54(1)). The separation of z and v is
15.3.46. No involution-orbit, fixed-lift, block-census or normalizer-motion
conclusion from 15.3.61 is an input.

The extraspecial calculation chooses a in V outside U, proves the inside
and outside fusion reductions, and constructs the actual local-product
isomorphism. Faithfulness on V puts C_U(V) in P, so the local product is
contained in P. The cubic calculation then produces its two actual blocks
and their four-orbit censuses. The same recognized action supplies both
moving normalizers. The final four-orbit argument and the corrected E32
local-plane cover yield the residual cover. In particular, no equal-order
identification replaces an ambient group isomorphism.

The source theorem owner in `Fusion` must supply the earlier-source inputs,
including the chosen involution t. This module closes the residual-orbit
branch and preserves all previously published modules and interfaces.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.61(2),
printed pp.1150–1151, using 15.3.46 and 15.3.48–59.
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
variable {G : Type*} [Group G] {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

private noncomputable def normalizerRecognition
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (d : Core.ResidualGeneration.RecognizedAction T Z ZS V t)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    Normalizers.RecognizedAction Z ZS hkernel where
  actorEquiv := d.actorEquiv
  vectorEquiv :=
    { toFun := fun w => (d.coordinates w.toMul).toAdd
      invFun := fun w => Additive.ofMul (d.coordinates.symm (Multiplicative.ofAdd w))
      left_inv := fun w => d.coordinates.symm_apply_apply w
      right_inv := fun w => d.coordinates.apply_symm_apply w
      map_add' := fun x y => d.coordinates.map_mul x y
      map_smul' := ZMod.map_smul
        ({ toFun := fun w => (d.coordinates w.toMul).toAdd
           map_zero' := d.coordinates.map_one
           map_add' := fun x y => d.coordinates.map_mul x y } :
          Recognition.Space Z ZS →+ NaturalDualSpace) }
  inner_equivariant := by
    intro g w
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (pCore 2 (centralizerH Z))
      (d.actorEquiv.symm (MulAut.conj g))
    rw [← ha, Recognition.actorRepresentation_mk]
    exact d.equivariant a g (by rw [ha, d.actorEquiv.apply_symm_apply]) w.toMul

variable {Y : Subgroup G} {g : G}
variable [(V.subgroupOf (pairP Z ZS g)).Normal]
variable {hIP : pairI Z ZS g ≤ normalizer (pairP Z ZS g : Set G)}
variable {hIV : pairI Z ZS g ≤ normalizer (V : Set G)}

omit [(Z.subgroupOf (closureU Z ZS)).Normal] in
private theorem centralizer_le_pairP
    (d : LayerActions (pairI Z ZS g) Y (pairP Z ZS g) V hIP hIV) :
    closureU Z ZS ⊓ centralizer (V : Set G) ≤ pairP Z ZS g := by
  intro x hx
  let i : pairI Z ZS g := ⟨x, (show closureU Z ZS ≤ pairI Z ZS g from le_sup_left) hx.1⟩
  have hfix : lowerAction (pairI Z ZS g) V hIV i = 1 := by
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change x * (w : G) * x⁻¹ = (w : G)
    rw [← hx.2 _ w.property, mul_inv_cancel_right]
  have he : d.actor i = 1 := by
    apply tensorAction_injective
    apply MulEquiv.ext
    intro w
    obtain ⟨u, rfl⟩ := d.lowerCoordinates.surjective w
    rw [← d.lower_compatible, hfix, map_one]
    rfl
  have hi : i ∈ d.actor.ker := he
  rw [d.kernel] at hi
  exact hi

set_option linter.style.haveILetI false in
/-- Every involution of the actual O²(C_G(Z)) is conjugate in G to z or v,
from the earlier source conclusions through 15.3.59. All local orbit,
product, cubic-block, census and moving-normalizer premises are discharged. -/
theorem residual_cover_of_earlier_geometry [Finite G]
    {M V₁ : Subgroup G} (z v : V)
    [((closureU Z ZS).subgroupOf (residualK Z)).Normal]
    (d : Core.ResidualGeneration.RecognizedAction T Z ZS V t)
    (h : Extraspecial.EarlierGeometry d M V₁ (z : G) (v : G))
    (l : LayerActions (pairI Z ZS g) Y (pairP Z ZS g) V hIP hIV)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hcenterP : V = (center (pairP Z ZS g)).map (pairP Z ZS g).subtype)
    (hW : Nat.card (closureU Z ZS ⊓ V : Subgroup G) = 8)
    (himage : Nat.card (Extraspecial.FixedLift.actionOnV
      ((show closureU Z ZS ≤ pairI Z ZS g from le_sup_left).trans hIV)).range = 4)
    (hsing : (l.lowerCoordinates z).toAdd.det = 0)
    (hperp : closureU Z ZS ⊓ V = CubicBlocks.Realization.sourceHyperplane l z)
    (hv : (l.lowerCoordinates v).toAdd.det ≠ 0)
    (S : Sylow 2 (pairI Z ZS g))
    (hS : (S : Subgroup (pairI Z ZS g)).map (pairI Z ZS g).subtype = residualSylow T Z)
    (hsep : ¬ IsConj (z : G) (v : G)) :
    ∀ x ∈ residualK Z, orderOf x = 2 → IsConj x (z : G) ∨ IsConj x (v : G) := by
  classical
  letI : IsExtraspecial 2 (closureU Z ZS) := h.extraspecial
  letI : IsElementaryAbelian 2 V := l.elementary_lower
  letI : IsElementaryAbelian 2 (VectorQuotient Z ZS) := by
    refine { toIsMulCommutative := IsMulCommutative.of_comm fun x y =>
               d.coordinates.injective (by simp only [map_mul, mul_comm])
             exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro w
    apply d.coordinates.injective
    rw [map_pow, map_one, pow_two]
    change (d.coordinates w).toAdd + (d.coordinates w).toAdd = 0
    exact ZModModule.add_self _
  have hVP : V ≤ pairP Z ZS g := by rw [hcenterP]; exact map_subtype_le _
  have hVK : V ≤ residualK Z :=
    hVP.trans ((CubicBlocks.Realization.pairP_le_residualSylow_of_sylow
      Z ZS T g S hS).trans inf_le_right)
  have hVH : V ≤ centralizerH Z := hVK.trans (residual_le_H Z)
  have hZV : Z ≤ V := by rw [← h.localGeometry.z_mark]; exact zpowers_le.mpr z.property
  have hZU : Z ≤ closureU Z ZS := h.Z_le_ZS.trans (ZS_le_closureU Z ZS)
  have hUV : closureU Z ZS ≤ normalizer (V : Set G) :=
    (show closureU Z ZS ≤ pairI Z ZS g from le_sup_left).trans hIV
  have hVU : V ≤ normalizer (closureU Z ZS : Set G) :=
    hVH.trans (H_normalizes_closureU Z ZS)
  have hnot : ¬ V ≤ closureU Z ZS := by
    intro he
    have hw := hW
    rw [inf_eq_right.mpr he, l.card_lower] at hw
    omega
  have hz : z ≠ 1 := by
    intro he
    have ho := h.localGeometry.z_order
    simp [he] at ho
  have hZcard : Nat.card Z = 2 := by
    rw [← h.localGeometry.z_mark, Nat.card_zpowers, h.localGeometry.z_order]
  have hVstar : Nat.card (Recognition.actorImage Z V) = 2 := by
    have hc := Normalizers.card_eq_actorImage_mul_intersection Z ZS V hVH h.core_eq
    rw [inf_comm V, hW, l.card_lower] at hc
    omega
  have hUZ : (center (closureU Z ZS)).map (closureU Z ZS).subtype = Z := by
    rw [← h.center_eq, subgroupOf_map_subtype, inf_eq_left.mpr hZU]
  obtain ⟨a, haV, haU, ha2, m, hinside, horbits, hpure, hmixed, houtside,
      hUa, hUaW, hac, hcard, hindex, hhyper, hmodel, ⟨e⟩⟩ :=
    Extraspecial.exists_source_premises d h hZV hW l.card_lower hUV himage
      hVK hnot h.localGeometry.z_order h.localGeometry.z_mark hsep
  have hLP : fixedLift Z ZS a ⊔ V ≤ pairP Z ZS g := by
    rw [hUa]
    exact sup_le (centralizer_le_pairP l) hVP
  obtain ⟨D, ai, σ, hblocks, hplanes, hlines, hcomm, hreduce, ⟨census⟩⟩ :=
    CubicBlocks.exists_source_cubic_blocks Z ZS T Y V g l a e hLP hcenterP hUZ
      hUa hVU h.order128 z hz h.localGeometry.z_mark hsing hperp v hv S hS
  have hmove (i : Fin 2) :
      ∃ n ∈ normalizer (fusionBlock (pairP Z ZS g) V (D i) : Set G),
        n ∉ normalizer (V : Set G) :=
    Normalizers.fusionBlock_moving_normalizer Z ZS T V g (D i) (census i).model
      (hblocks i).2.2.2.1 h.Z_le_ZS hZV hZcard h.core_eq h.order128 h.center_eq hkernel
      (normalizerRecognition d hkernel) hVstar
  exact residual_cover_of_local_geometry Z ZS V g a z v e D hinside houtside
    hreduce census hmove hsep

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits
