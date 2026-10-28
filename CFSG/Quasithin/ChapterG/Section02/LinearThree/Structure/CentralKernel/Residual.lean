module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.Interface
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.Residual.Coordinates
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.FixedPointFree

/-!
# The radical image lies in the residual L-image

The literal image U⁺ in I/(WWᵍWʰ) embeds into L*. The source input
[V,U]=V₁ and centralization of V₁ identify its action as shears along the
marked point. A cubic Levi element has no nonidentity fixed shear.
Its lift lies in the actual O²(N_L(V₁)) by functoriality of the two-residual,
and hence normalizes U⁺. Its commutator map on finite U⁺ is surjective.
Since L⁺ is normal and contains that lift, all of U⁺ lies in L⁺.

The construction retains the original star and quotient maps. It uses
only U≤T, I*=L*, and [V,U]=V₁ from the preceding source outputs; no
radical-order or trivial-center hypothesis is needed, even when n=1.
The final theorem supplies IsPPerfect 2 (I/P) to the transfer interface.

Source: Aschbacher–Smith G.2.5(3), printed pp.335–336, referring to
G.2.3, printed pp.333–334.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
open Setup

variable {K : Type*} [Group K] [Finite K]

private theorem subgroup_le_of_fixedPointFree (A B : Subgroup K) [B.Normal]
    (c : K) (hcB : c ∈ B) (hcA : c ∈ normalizer (A : Set K))
    (hfree : ∀ a ∈ A, Commute a c → a = 1) : A ≤ B := by
  let φ := A.normalizerMonoidHom ⟨c, hcA⟩
  have hf : MonoidHom.FixedPointFree φ := by
    intro a ha
    apply Subtype.ext
    apply hfree a a.property
    have he : c * (a : K) * c⁻¹ = a := congrArg Subtype.val ha
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  intro a ha
  obtain ⟨u, hu⟩ := hf.commutatorMap_surjective ⟨a, ha⟩
  have he : (u : K) * (c * (u : K) * c⁻¹)⁻¹ = a := by
    have he' : (u : K) / (c * (u : K) * c⁻¹) = a := congrArg Subtype.val hu
    simpa only [div_eq_mul_inv] using he'
  have hm : ⁅(u : K), c⁆ ∈ B :=
    commutator_le_right A B (commutator_mem_commutator u.property hcB)
  have hh : (u : K) * (c * (u : K) * c⁻¹)⁻¹ = ⁅(u : K), c⁆ := by
    simp only [commutatorElement_def, _root_.mul_inv_rev, inv_inv]
    group
  exact he ▸ hh.symm ▸ hm

variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

omit [Finite G] in
private theorem L1_le_L : D.L₁ ≤ D.L :=
  (map_subtype_le (pResidual 2 (D.L ⊓ D.G₁ : Subgroup G))).trans inf_le_left

private theorem point_fixed_mem_G1 (l : D.L)
    (hl : ∀ v ∈ d.point, d.model (starProjection D l) • v = v) : (l : G) ∈ D.G₁ := by
  apply centralizer_le_normalizer (D.V₁ : Set G)
  intro v hv
  let vV : D.V := ⟨v, d.setup.point_le hv⟩
  have he := d.equivariant l vV
  have hf := hl (d.coordinates vV).toAdd ((d.point_mem vV).mp hv)
  change (d.model (starProjection D l)).val *ᵥ (d.coordinates vV).toAdd =
    (d.coordinates vV).toAdd at hf
  have hh : (l : G) * v * (l : G)⁻¹ = v :=
    congrArg Subtype.val (d.coordinates.injective (he.trans hf))
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem exists_L1_lift (c : SL(3, F)) (hc3 : c ^ 3 = 1)
    (hcP : ∀ v ∈ d.point, c • v = v) :
    ∃ l : D.L, (l : G) ∈ D.L₁ ∧ d.model (starProjection D l) = c := by
  obtain ⟨l, hl⟩ := (d.model.surjective.comp (starProjection_surjective D)) c
  change d.model (starProjection D l) = c at hl
  let N := D.L ⊓ D.G₁
  let f : N →* SL(3, F) := (d.model.toMonoidHom.comp (starProjection D)).comp
    (inclusion inf_le_left)
  let lN : N := ⟨l, l.property, point_fixed_mem_G1 d l (by simpa [hl] using hcP)⟩
  let cR : f.range := f.rangeRestrict lN
  have hcR : (cR : SL(3, F)) = c := hl
  have hcR3 : cR ^ 3 = 1 := by
    apply Subtype.ext
    change (cR : SL(3, F)) ^ 3 = 1
    rw [hcR, hc3]
  have hcres : cR ∈ pResidual 2 f.range :=
    mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hcR3))
  rw [← map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective] at hcres
  obtain ⟨r, hr, he⟩ := hcres
  refine ⟨inclusion inf_le_left r, ⟨r, hr, rfl⟩, ?_⟩
  exact (congrArg Subtype.val he).trans hcR

private theorem U_model_fixes_point (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (u : I D g h) (hu : (u : G) ∈ D.U) :
    ∀ w ∈ d.point, d.model (d.IStarProjection hUT hstar u) • w = w := by
  intro w hw
  obtain ⟨v, hv⟩ := d.coordinates.surjective (Multiplicative.ofAdd w)
  have hv₁ : (v : G) ∈ D.V₁ := (d.point_mem v).mpr (by rw [hv]; exact hw)
  have hcom := d.setup.toBaseHypothesis.U_le_centralizer_point hu (v : G) hv₁
  have he : (u : G) * v * (u : G)⁻¹ = v := by
    rw [← hcom, mul_inv_cancel_right]
  have he' := d.IStarProjection_equivariant hUT hstar u v
  have hv' : (d.coordinates v).toAdd = w := congrArg Multiplicative.toAdd hv
  have heV : (⟨(u : G) * v * (u : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes hUT u.property) v).mp v.property⟩ : D.V) = v :=
    Subtype.ext he
  rw [heV, hv'] at he'
  exact he'.symm

private theorem U_model_displacement (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (hmove : ⁅D.V, D.U⁆ = D.V₁)
    (u : I D g h) (hu : (u : G) ∈ D.U) (w : Fin 3 → F) :
    d.model (d.IStarProjection hUT hstar u) • w - w ∈ d.point := by
  obtain ⟨v, hv⟩ := d.coordinates.surjective (Multiplicative.ofAdd w)
  let uv : D.V := ⟨(u : G) * v * (u : G)⁻¹,
    (mem_normalizer_iff.mp (d.I_normalizes hUT u.property) v).mp v.property⟩
  have hm : ((uv * v⁻¹ : D.V) : G) ∈ D.V₁ := by
    have hh := commutator_mem_commutator hu v.property
    rw [commutator_comm D.U D.V, hmove] at hh
    exact hh
  have hp := (d.point_mem (uv * v⁻¹)).mp hm
  have he' := d.IStarProjection_equivariant hUT hstar u v
  have hv' : (d.coordinates v).toAdd = w := congrArg Multiplicative.toAdd hv
  change (d.coordinates uv).toAdd = _ at he'
  change (d.coordinates uv).toAdd = d.model (d.IStarProjection hUT hstar u) •
    (d.coordinates v).toAdd at he'
  rw [map_mul, map_inv] at hp
  rw [toAdd_mul, toAdd_inv, ← sub_eq_add_neg] at hp
  rwa [he', hv'] at hp

variable [((WProduct D g h).subgroupOf (I D g h)).Normal]
include d

private theorem image_L_normal (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) : (image D g h D.L).Normal := by
  have hLI := d.L_le_I_of_star hstar.ge
  have hIN : I D g h ≤ normalizer (D.L : Set G) := by
    rw [d.I_eq_LU_of_star hstar.ge]
    exact sup_le D.L.le_normalizer (hUT.trans d.setup.T_normalizes_L)
  let : (D.L.subgroupOf (I D g h)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLI).mpr hIN
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

private theorem image_U_le_image_L_of_cubic
    (hUT : D.U ≤ D.T) (hstar : D.star (I D g h) = D.star D.L)
    (c : Quotient D g h) (hc : c ∈ image D g h D.L₁)
    (hfree : ∀ a ∈ image D g h D.U, Commute a c → a = 1) :
    image D g h D.U ≤ image D g h D.L := by
  let := image_L_normal d hUT hstar
  exact subgroup_le_of_fixedPointFree _ _ c
    (map_mono (comap_mono L1_le_L) hc) (image_L₁_normalizes_U d hc) hfree

/-- The point-stabilizer action places the full U-image inside the L-image
in the original quotient I/(WWᵍWʰ). The quotient normality instance may
be supplied by `d.WProduct_normal hUT hstar.ge`. -/
theorem image_U_le_image_L (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (hmove : ⁅D.V, D.U⁆ = D.V₁) : image D g h D.U ≤ image D g h D.L := by
  obtain ⟨c, hc3, hcP, hcfree⟩ := ResidualCoordinates.exists_point_cubic d
  obtain ⟨l, hl, hlc⟩ := exists_L1_lift d c hc3 hcP
  let lI : I D g h := inclusion (d.L_le_I_of_star hstar.ge) l
  let cQ : Quotient D g h := projection D g h lI
  have hcQ : cQ ∈ image D g h D.L₁ := mem_map_of_mem _ hl
  apply image_U_le_image_L_of_cubic d hUT hstar cQ hcQ
  intro a ha hcomm
  obtain ⟨u, hu, rfl⟩ := ha
  have huModel : d.model (d.IStarProjection hUT hstar u) = 1 := by
    apply hcfree _ (U_model_fixes_point d hUT hstar u hu)
      (U_model_displacement d hUT hstar hmove u hu)
    have hm := hcomm.map (d.model.toMonoidHom.comp (starMap d hUT hstar))
    change Commute (d.model (d.IStarProjection hUT hstar u))
      (d.model (starProjection D l)) at hm
    rwa [hlc] at hm
  have hk : projection D g h u ∈ (starMap d hUT hstar).ker := by
    apply MonoidHom.mem_ker.mpr
    apply d.model.injective
    simpa only [starMap_projection, map_one] using huModel
  exact disjoint_def.mp (image_U_disjoint_ker d hUT hstar)
    (mem_map_of_mem (projection D g h) hu) hk

/-- The containment supplies the two-perfect quotient required by the
central-kernel transfer argument, with no residual premise remaining. -/
theorem isPPerfect_quotient (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (hmove : ⁅D.V, D.U⁆ = D.V₁) : IsPPerfect 2 (Quotient D g h) :=
  isPPerfect_of_image_U_le_image_L d hstar (image_U_le_image_L d hUT hstar hmove)

end CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
