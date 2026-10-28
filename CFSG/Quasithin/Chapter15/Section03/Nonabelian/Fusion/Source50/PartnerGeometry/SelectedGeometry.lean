module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.SelectedPair
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Normalizers
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# The actual partner normalizers and core product

The symmetric-three quotient exhausts the automorphism group of the selected
four-group. This gives both ambient normalizer conclusions. The same plane
markings identify F with U∩O₂(J), so the binary kernel factorization supplies
O₂(J)=FX and places X in the original Sylow subgroup.
Source: Aschbacher–Smith 15.3.56(3), printed p.1147.
-/
@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
variable {G : Type*} [Group G] [Finite G] (Z ZS : Subgroup G)
omit [Finite G] in


theorem planeAction_ker_map (V₀ : Subgroup G) (y : G)
    (hJV : pairI Z ZS y ≤ normalizer (V₀ : Set G)) :
    (planeAction Z ZS V₀ y hJV).ker.map (pairI Z ZS y).subtype =
      pairI Z ZS y ⊓ centralizer (V₀ : Set G) := by
  ext x
  constructor
  · rintro ⟨j,hj,rfl⟩
    refine ⟨j.property,?_⟩
    intro v hv
    have hh := congrArg Subtype.val (MulEquiv.congr_fun hj ⟨v,hv⟩)
    change (j:G)*v*(j:G)⁻¹=v at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hx
    refine ⟨⟨x,hx.1⟩,?_,rfl⟩
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change x*(v:G)*x⁻¹=v
    rw [← hx.2 v v.property,mul_inv_cancel_right]

theorem planeAction_surjective_of_core (V₀ : Subgroup G) (y : G)
    (hJV : pairI Z ZS y ≤ normalizer (V₀ : Set G))
    (helem : IsElementaryAbelian 2 V₀) (hcard : Nat.card V₀=4)
    (e : (pairI Z ZS y ⧸ pCore 2 (pairI Z ZS y)) ≃* Equiv.Perm (Fin 3))
    (hcore : pairP Z ZS y=pairI Z ZS y ⊓ centralizer (V₀ : Set G)) :
    Function.Surjective (planeAction Z ZS V₀ y hJV) := by
  let := helem
  let : Nontrivial V₀ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour V₀ := ⟨hcard,IsElementaryAbelian.exponent_eq_prime⟩
  have hk : (planeAction Z ZS V₀ y hJV).ker = pCore 2 (pairI Z ZS y) := by
    apply map_injective (pairI Z ZS y).subtype_injective
    change (planeAction Z ZS V₀ y hJV).ker.map _ = pairP Z ZS y
    rw [planeAction_ker_map,hcore]
  apply MonoidHom.range_eq_top.mp
  apply eq_of_le_of_card_ge le_top
  rw [Nat.card_congr (topEquiv.toEquiv), IsKleinFour.card_mulAut V₀,
    ← index_ker,hk,index_eq_card,Nat.card_congr e.toEquiv]
  simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  decide

/-- The group-theoretic fields passed directly into the later marked-partner
geometry. Every field uses the originally selected residual and cubic. -/
structure SelectedGeometry (T Y₁ : Subgroup G) (y : G) where
  V₀_eq : localSpan Z Y₁=Z ⊔ rightConjugate Z y
  V₀_le_U : localSpan Z Y₁ ≤ closureU Z ZS
  V₀_le_E : localSpan Z Y₁ ≤ intersectionE Z ZS y
  E_elementary : IsElementaryAbelian 2 (intersectionE Z ZS y)
  E_eq : intersectionE Z ZS y=closureU Z ZS ⊓ rightConjugate (closureU Z ZS) y
  J_normalizer : normalizer (localSpan Z Y₁ : Set G) ≤ normalizer (pairI Z ZS y : Set G)
  E_normalizer : normalizer (localSpan Z Y₁ : Set G) ≤ normalizer (intersectionE Z ZS y : Set G)
  J_core : pairP Z ZS y=intersectionF Z ZS y ⊔ partnerX Z ZS y
  X_le_T : partnerX Z ZS y ≤ T
  F_index : (intersectionF Z ZS y).relIndex (closureU Z ZS)=2
  E_commutator : ⁅intersectionE Z ZS y,pairI Z ZS y⁆ ≤ localSpan Z Y₁

open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour
variable {Z ZS} {Zperp V Y T : Subgroup G} {g : G}

theorem selected_geometry
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y=V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) (hΩ : omegaCenter T=Z)
    (y : (Chapter15.setup Z Zperp Y T).I g) (hy : (y:G) ∈ leftResidual d)
    (hyc : matrixSection d y=MatrixOrbit.leftCubic) :
    Nonempty (SelectedGeometry Z ZS T (leftResidual d) (y:G)) := by
  obtain ⟨hextra,hcenter,_⟩ := PairGeometry.literal_extraspecial hZS hperp hspan d hΩ
  let := hextra
  have hZSH : ZS ≤ centralizerH Z := hZS.trans (by
    have hh := d.base.U_le_H
    rw [Chapter15.closure_eq hZS hperp] at hh
    exact hperp.trans hh)
  obtain ⟨hplane,hplaneV,hcard,hyn,hdis⟩ := selected_plane d y hy hyc
  change localSpan Z (leftResidual d)=Z ⊔ rightConjugate Z (y:G) at hplane
  obtain ⟨⟨e⟩,hcore,_,hcoreT⟩ := literal_selected_core hZS hperp d y hy hyc
  have hplaneU := hplaneV.trans hperp
  have hf : (frattini (closureU Z ZS)).map (closureU Z ZS).subtype ≤ Z := by
    have hh := d.closure.frattini
    rw [Chapter15.closure_eq hZS hperp] at hh
    exact hh
  obtain ⟨hVE,hEP,hJE,hcomm,helem⟩ := rank_one_intersection_layer Z ZS
    (localSpan Z (leftResidual d)) (y:G) hZSH (IsExtraspecial.isPGroup 2 _) hf
      hplane hplaneU hyn hdis
  have hJV := selected_pair_normalizes_plane d y hy hyc
  rw [Chapter15.I_eq _ hZS hperp] at hJV
  have hVelem : IsElementaryAbelian 2 (localSpan Z (leftResidual d)) := by
    let := d.VL_elementary
    exact IsElementaryAbelian.of_le (hplaneV.trans d.V_le_VL)
  have hfull := planeAction_surjective_of_core Z ZS _ _ hJV hVelem hcard e hcore
  obtain ⟨hNJ,hNE⟩ := partner_normalizers Z ZS _ _ hZSH hplane hyn hJV hJE hfull
  have hyJ := selected_y_mem_pair d y hy hyc
  rw [Chapter15.I_eq _ hZS hperp] at hyJ
  have hindex := intersectionF_index Z ZS (y:G) hcenter d.point_card
    ((show rightConjugate Z (y:G) ≤ localSpan Z (leftResidual d) by rw [hplane]; exact le_sup_right).trans hplaneU) hdis
  have hprod := partner_core_product Z ZS _ (leftResidual d) T (y:G)
    hZSH hplane hcore hyJ e hindex
  exact ⟨⟨hplane,hplaneU,hVE,helem,intersectionE_eq Z ZS _ _ hZSH hplane hyn,
    hNJ,hNE,hprod,(hprod ▸ (show partnerX Z ZS (y:G) ≤ intersectionF Z ZS (y:G) ⊔
      partnerX Z ZS (y:G) from le_sup_right)).trans hcoreT,hindex,hcomm⟩⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
