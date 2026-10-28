module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.SelectedGeometry

/-!
# Both marked singular summands are invariant under X

The new rank-one core lies in P U: its old matrix image is the right
point involution, already in U. The original core centralizes the natural
four-space, while U normalizes both marked planes. The ambient normalizer
property of E therefore gives X-invariance of E and Eᵗ simultaneously.
Source: Aschbacher–Smith 15.3.56(5), printed p.1148.
-/
@[expose] public noncomputable section
open Subgroup ClassicalOrthogonal.FourPlusMatrix
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour Chapter15Collapse
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)

/-- The exact old-core supplement containing the new core. -/
theorem selected_pair_core_le_oldCore_sup_U (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (y : D.I g) (hyc : matrixSection d y=MatrixOrbit.leftCubic) :
    (D.I (y:G)).pCoreIn 2 ≤ D.S g ⊔ D.U := by
  rintro x ⟨j,hj,rfl⟩
  let i := inclusion (selected_pair_le_I y) j
  have hfirst : (matrixSection d i).1=1 := by
    change j ∈ (selectedPlaneActor d z hz y hyc).ker
    rw [selectedPlaneActor_ker_eq_core]
    exact hj
  have hright := (selectedPairActor d z hz y hyc j).property
  have himage : matrixSection d i ∈ matrixImage d D.U := by
    rw [matrixImage_eq_modelImage,d.modelImage_U_eq_vector_stabilizer z hz]
    change matrixAction ((matrixSection d i).1,(matrixSection d i).2) (d.pointVector z)=_
    rw [hfirst]
    exact hright
  obtain ⟨u,hu,he⟩ := himage
  have hku : i*u⁻¹ ∈ pCore 2 (D.I g) := by
    rw [← matrixSection_ker d]
    change matrixSection d (i*u⁻¹)=1
    rw [map_mul,map_inv,← he,mul_inv_cancel]
  have hk : (i:G)*(u:G)⁻¹ ∈ D.S g := ⟨i*u⁻¹,hku,rfl⟩
  have hx := (D.S g ⊔ D.U).mul_mem (mem_sup_left hk) (mem_sup_right hu)
  change (i:G) ∈ D.S g ⊔ D.U
  simpa only [subtype_apply,inv_mul_cancel_right] using hx

/-- The new core normalizes both orbit planes, for every element of T. -/
theorem selected_core_normalizes_conjugate_plane (y : D.I g)
    (hy : (y:G) ∈ leftResidual d) (hyc : matrixSection d y=MatrixOrbit.leftCubic)
    (t : G) (ht : t ∈ D.T) :
    (D.I (y:G)).pCoreIn 2 ≤ normalizer
      (rightConjugate (localSpan D.V₁ (leftResidual d)) t : Set G) := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  let V₀ := localSpan D.V₁ (leftResidual d)
  have hVU : D.U ≤ normalizer (V₀ : Set G) :=
    le_sup_left.trans (selected_pair_normalizes_plane d y hy hyc)
  have hVVL : V₀ ≤ D.VL := (selected_plane d y hy hyc).2.1.trans d.V_le_VL
  have hVtVL : rightConjugate V₀ t ≤ D.VL := by
    rintro _ ⟨v,hv,rfl⟩
    exact (mem_normalizer_iff.mp (T_normalizes_natural d (D.T.inv_mem ht)) v).mp (hVVL hv)
  have hPVL : D.S g ≤ centralizer (D.VL : Set G) := by
    intro p hp v hv
    exact ((d.central_first_layer hv).2 p hp).symm
  have hPN := (hPVL.trans (centralizer_le hVtVL)).trans
    (centralizer_le_normalizer (rightConjugate V₀ t : Set G))
  have hUN : D.U ≤ normalizer (rightConjugate V₀ t : Set G) := by
    have hUt : rightConjugate D.U t=D.U :=
      mem_normalizer_iff_map_conj_eq.mp (d.base.binary_T_normalizes_U (D.T.inv_mem ht))
    rw [← hUt]
    exact (map_mono hVU).trans (le_normalizer_map (MulAut.conj t⁻¹).toMonoidHom)
  exact (selected_pair_core_le_oldCore_sup_U d z hz y hyc).trans (sup_le hPN hUN)

omit [Finite G] in
private theorem conjugate_normalizer_le {V₀ E : Subgroup G}
    (h : normalizer (V₀ : Set G) ≤ normalizer (E : Set G)) (t : G) :
    normalizer (rightConjugate V₀ t : Set G) ≤ normalizer (rightConjugate E t : Set G) := by
  change normalizer (V₀.map (MulAut.conj t⁻¹).toMonoidHom : Set G) ≤
    normalizer (E.map (MulAut.conj t⁻¹).toMonoidHom : Set G)
  rw [← map_normalizer_eq_of_bijective V₀ (MulAut.conj t⁻¹).bijective,
    ← map_normalizer_eq_of_bijective E (MulAut.conj t⁻¹).bijective]
  exact map_mono h

variable {Z ZS Zperp Y T : Subgroup G} {g : G}
/-- Literal simultaneous invariance for the two summands used by MarkedAction. -/
theorem selected_partner_normalizes_both
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (y : (Chapter15.setup Z Zperp Y T).I g) (hy : (y:G)∈leftResidual d)
    (hyc : matrixSection d y=MatrixOrbit.leftCubic) (t : G) (ht : t∈T)
    (geometry : SelectedGeometry Z ZS T (leftResidual d) (y:G)) :
    partnerX Z ZS (y:G) ≤ normalizer (intersectionE Z ZS (y:G):Set G) ∧
      partnerX Z ZS (y:G) ≤ normalizer
        (rightConjugate (intersectionE Z ZS (y:G)) t : Set G) := by
  have hXK : partnerX Z ZS (y:G) ≤ pairP Z ZS (y:G) := geometry.J_core ▸ le_sup_right
  have hXN := selected_core_normalizes_conjugate_plane d y hy hyc t ht
  rw [Chapter15.I_eq _ hZS hperp] at hXN
  have hXJ : partnerX Z ZS (y:G) ≤ pairI Z ZS (y:G) := hXK.trans (pCoreIn_le _ _)
  have hJV := selected_pair_normalizes_plane d y hy hyc
  rw [Chapter15.I_eq _ hZS hperp] at hJV
  exact ⟨(hXJ.trans hJV).trans geometry.E_normalizer,
    (hXK.trans hXN).trans (conjugate_normalizer_le geometry.E_normalizer t)⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
