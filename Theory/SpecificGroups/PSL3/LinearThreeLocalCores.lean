module

public import Theory.SpecificGroups.PSL3.LinearThreeLocalAffine
public import Theory.SpecificGroups.SL2.Affine.Core

/-!
# Root-plane radicals and local quotients in degree three

The two-by-two linear-part kernels are precisely the coordinate root planes:
entries (0,2),(1,2) for the line local, and (0,1),(0,2) for the point local.
The matrix characterizations below identify these actual subgroups before
transporting the affine two-core calculation. Projective projection is
injective on both locals, so their projective images have the same cores.
All four quotients are explicitly equivalent to SL₂(F).

Source: Aschbacher–Smith, F.1.12(I)(1), printed pp.262–264.
The core results hold in every finite field of characteristic two.
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F]

/-- The line radical, intrinsic to the local subgroup. -/
def lineRadicalSL : Subgroup (lineLocalSL F) :=
  ((SemidirectProduct.rightHom : Matrix.SL2.Affine F →* SL(2, F)).comp
    (lineLocalAffineEquiv F).toMonoidHom).ker

/-- The point radical, intrinsic to the local subgroup. -/
def pointRadicalSL : Subgroup (pointLocalSL F) :=
  ((SemidirectProduct.rightHom : Matrix.SL2.Affine F →* SL(2, F)).comp
    (pointLocalAffineEquiv F).toMonoidHom).ker

instance lineRadicalSL_normal : (lineRadicalSL F).Normal :=
  inferInstanceAs (MonoidHom.ker _).Normal
instance pointRadicalSL_normal : (pointRadicalSL F).Normal :=
  inferInstanceAs (MonoidHom.ker _).Normal

theorem mem_lineRadicalSL_iff (g : lineLocalSL F) : g ∈ lineRadicalSL F ↔
    g.val.val 0 0 = 1 ∧ g.val.val 0 1 = 0 ∧
      g.val.val 1 0 = 0 ∧ g.val.val 1 1 = 1 := by
  change (lineToAffine F g).right = 1 ↔ _
  constructor
  · intro h
    exact ⟨congrArg (fun a : SL(2, F) => a.val 0 0) h,
      congrArg (fun a : SL(2, F) => a.val 0 1) h,
      congrArg (fun a : SL(2, F) => a.val 1 0) h,
      congrArg (fun a : SL(2, F) => a.val 1 1) h⟩
  · rintro ⟨h00,h01,h10,h11⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lineToAffine, h00,h01,h10,h11]

theorem pointRadicalSL_eq_comap_lineRadicalSL : pointRadicalSL F =
    (lineRadicalSL F).comap (pointLineLocalEquiv F).toMonoidHom := rfl

theorem mem_pointRadicalSL_iff (g : pointLocalSL F) : g ∈ pointRadicalSL F ↔
    g.val.val 1 1 = 1 ∧ g.val.val 1 2 = 0 ∧
      g.val.val 2 1 = 0 ∧ g.val.val 2 2 = 1 := by
  rw [← Subgroup.inv_mem_iff, pointRadicalSL_eq_comap_lineRadicalSL,
    Subgroup.mem_comap, mem_lineRadicalSL_iff]
  have hi : ((g⁻¹ : pointLocalSL F).val)⁻¹ = g.val := inv_inv g.val
  change (((g⁻¹ : pointLocalSL F).val)⁻¹.val 2 2 = 1 ∧
    ((g⁻¹ : pointLocalSL F).val)⁻¹.val 1 2 = 0 ∧
    ((g⁻¹ : pointLocalSL F).val)⁻¹.val 2 1 = 0 ∧
    ((g⁻¹ : pointLocalSL F).val)⁻¹.val 1 1 = 1) ↔ _
  rw [hi]
  tauto

/-- The root plane in the actual projective line-local group. -/
noncomputable def lineRadical : Subgroup (lineLocal F) :=
  (lineRadicalSL F).map (lineLocalProjectEquiv F).toMonoidHom

/-- The root plane in the actual projective point-local group. -/
noncomputable def pointRadical : Subgroup (pointLocal F) :=
  (pointRadicalSL F).map (pointLocalProjectEquiv F).toMonoidHom

instance lineRadical_normal : (lineRadical F).Normal :=
  Subgroup.Normal.map inferInstance _ (lineLocalProjectEquiv F).surjective

instance pointRadical_normal : (pointRadical F).Normal :=
  Subgroup.Normal.map inferInstance _ (pointLocalProjectEquiv F).surjective

variable [Finite F] [CharP F 2]
private theorem core_eq_linearPart_ker {G : Type*} [Group G]
    (e : G ≃* Matrix.SL2.Affine F) : pCore 2 G =
      ((SemidirectProduct.rightHom : Matrix.SL2.Affine F →* SL(2, F)).comp
        e.toMonoidHom).ker := by
  have hc : pCore 2 G = (pCore 2 (Matrix.SL2.Affine F)).comap e.toMonoidHom := by
    rw [← pCore_map_iso 2 e]
    symm
    apply Subgroup.comap_map_eq_self
    rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
    exact bot_le
  rw [hc, Matrix.SL2.affine_twoCore_eq]
  rfl

theorem lineLocalSL_twoCore_eq : pCore 2 (lineLocalSL F) = lineRadicalSL F :=
  core_eq_linearPart_ker F (lineLocalAffineEquiv F)

theorem pointLocalSL_twoCore_eq : pCore 2 (pointLocalSL F) = pointRadicalSL F :=
  core_eq_linearPart_ker F (pointLocalAffineEquiv F)

theorem lineLocal_twoCore_eq : pCore 2 (lineLocal F) = lineRadical F := by
  rw [← pCore_map_iso 2 (lineLocalProjectEquiv F), lineLocalSL_twoCore_eq]
  rfl

theorem pointLocal_twoCore_eq : pCore 2 (pointLocal F) = pointRadical F := by
  rw [← pCore_map_iso 2 (pointLocalProjectEquiv F), pointLocalSL_twoCore_eq]
  rfl

/-- The line-local core quotient, via its actual linear block. -/
noncomputable def lineLocalSLCoreQuotientEquiv :
    (lineLocalSL F ⧸ pCore 2 (lineLocalSL F)) ≃* SL(2, F) :=
  (QuotientGroup.congr _ _ (lineLocalAffineEquiv F)
    (pCore_map_iso 2 (lineLocalAffineEquiv F))).trans (Matrix.SL2.affineCoreQuotientEquiv F)

/-- The point-local core quotient, in the natural coordinates obtained by duality. -/
noncomputable def pointLocalSLCoreQuotientEquiv :
    (pointLocalSL F ⧸ pCore 2 (pointLocalSL F)) ≃* SL(2, F) :=
  (QuotientGroup.congr _ _ (pointLocalAffineEquiv F)
    (pCore_map_iso 2 (pointLocalAffineEquiv F))).trans (Matrix.SL2.affineCoreQuotientEquiv F)

/-- The actual projective line-local quotient by O₂. -/
noncomputable def lineLocalCoreQuotientEquiv :
    (lineLocal F ⧸ pCore 2 (lineLocal F)) ≃* SL(2, F) :=
  (QuotientGroup.congr _ _ (lineLocalEquivAffine F)
    (pCore_map_iso 2 (lineLocalEquivAffine F))).trans (Matrix.SL2.affineCoreQuotientEquiv F)

/-- The actual projective point-local quotient by O₂. -/
noncomputable def pointLocalCoreQuotientEquiv :
    (pointLocal F ⧸ pCore 2 (pointLocal F)) ≃* SL(2, F) :=
  (QuotientGroup.congr _ _ (pointLocalEquivAffine F)
    (pCore_map_iso 2 (pointLocalEquivAffine F))).trans (Matrix.SL2.affineCoreQuotientEquiv F)
@[simp] theorem lineLocalSLCoreQuotientEquiv_mk (g : lineLocalSL F) :
    lineLocalSLCoreQuotientEquiv F (QuotientGroup.mk' (pCore 2 (lineLocalSL F)) g) =
      (lineLocalAffineEquiv F g).right := rfl

@[simp] theorem pointLocalSLCoreQuotientEquiv_mk (g : pointLocalSL F) :
    pointLocalSLCoreQuotientEquiv F (QuotientGroup.mk' (pCore 2 (pointLocalSL F)) g) =
      (pointLocalAffineEquiv F g).right := rfl

@[simp] theorem lineLocalCoreQuotientEquiv_mk (g : lineLocal F) :
    lineLocalCoreQuotientEquiv F (QuotientGroup.mk' (pCore 2 (lineLocal F)) g) =
      (lineLocalEquivAffine F g).right := rfl

@[simp] theorem pointLocalCoreQuotientEquiv_mk (g : pointLocal F) :
    pointLocalCoreQuotientEquiv F (QuotientGroup.mk' (pCore 2 (pointLocal F)) g) =
      (pointLocalEquivAffine F g).right := rfl

end Matrix.PSL3.LinearThree
