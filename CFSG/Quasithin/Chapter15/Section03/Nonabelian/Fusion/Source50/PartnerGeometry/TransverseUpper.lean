module
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Assembly
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity

/-!
# The upper-factor bound for the two source56 partners

A subgroup of P centralized modulo V by both literal cubic residual factors
has zero image in P/V, since the two residual images generate the full odd
image of Y. Applying this to E∩E^t gives its containment in the natural
four-space. This uses the same source module witness and quotient map.

Source: Aschbacher–Smith, proof of 15.3.56(5), printed p.1148.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour Chapter15Collapse Chapter15Assembly
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
variable [((OrthogonalPlusFour.S₂ D g).subgroupOf (D.S g)).Normal]
  [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient D g)]

/-- Both cubic residuals detect every nonzero upper vector, with the
literal I/O₂(I) marking retained. -/
theorem le_natural_of_two_residual_commutators (d : Hypothesis D g)
    (f : SourceModuleData d) (hΩ : omegaCenter D.T ≤ D.VL)
    (A : Subgroup G) (hAP : A ≤ D.S g)
    (hleft : ⁅A,oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L
      ProductDecomposition.leftFactor⁆ ≤ D.VL)
    (hright : ⁅A,oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L
      ProductDecomposition.rightFactor⁆ ≤ D.VL) : A ≤ D.VL := by
  let π := moduleProjection d.quotientSymmetricEquiv
  let c := (factorData_of_source f hΩ).conjugation
  have himage : (D.L.subgroupOf (D.I g)).map π =
      (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) :=
    d.quotientSymmetricEquiv_L_image
  have odd_cube (a : S₃) (ha : a ∈ alternatingGroup (Fin 3)) : a ^ 3 = 1 := by
    have cert : ∀ a : S₃, Equiv.Perm.sign a = 1 → a^3=1 := by decide +kernel
    exact cert a (Equiv.Perm.mem_alternatingGroup.mp ha)
  intro x hx
  let p : D.S g := ⟨x,hAP hx⟩
  let v := (c.coordinates p).toAdd
  have hv : v ∈ c.imageSpace A := (c.mem_imageSpace_iff A _).mpr ⟨p,hx,rfl⟩
  have hf : v ∈ fixedSpace (f.representation.comp π) (D.L.subgroupOf (D.I g)) := by
    intro l
    have hl : π l ∈ (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) := by
      rw [← himage]
      exact mem_map.mpr ⟨l,l.property,rfl⟩
    have h1 := mem_oddFactor_image_of_cube π D.L (d.I_eq_LU.symm ▸ le_sup_left)
      ProductDecomposition.leftFactor ((π l).1,1) (by
        rw [himage]
        exact ⟨⟨hl.1,one_mem _⟩,mem_top _,rfl⟩) (by
        exact Prod.ext (odd_cube _ hl.1) (one_pow 3))
    have h2 := mem_oddFactor_image_of_cube π D.L (d.I_eq_LU.symm ▸ le_sup_left)
      ProductDecomposition.rightFactor (1,(π l).2) (by
        rw [himage]
        exact ⟨⟨one_mem _,hl.2⟩,rfl,mem_top _⟩) (by
        exact Prod.ext (one_pow 3) (odd_cube _ hl.2))
    obtain ⟨u,hu,heu⟩ := h1
    obtain ⟨w,hw,hew⟩ := h2
    have hu' := c.fixed_on_imageSpace_of_commutator_le
      (oddFactor π D.L ProductDecomposition.leftFactor) A
      (by rwa [commutator_comm]) u hu v hv
    have hw' := c.fixed_on_imageSpace_of_commutator_le
      (oddFactor π D.L ProductDecomposition.rightFactor) A
      (by rwa [commutator_comm]) w hw v hv
    change f.representation (π u) v = v at hu'
    change f.representation (π w) v = v at hw'
    change f.representation (π l) v = v
    have hprod : π l = π u * π w := by rw [heu,hew]; exact Prod.ext (mul_one _).symm (one_mul _).symm
    rw [hprod,map_mul,Module.End.mul_apply,hw',hu']
  rw [f.odd_fixed,Submodule.mem_bot] at hf
  apply (c.coordinates_eq_one_iff p).mp
  exact Multiplicative.toAdd.injective hf

/-- The marked upper-factor calculation for the actual E and its exchanged
right conjugate. The source matrix image supplies their core containment. -/
theorem partner_intersection_le_natural (d : Hypothesis D g)
    (f : SourceModuleData d) (hΩ : omegaCenter D.T ≤ D.VL)
    (E : Subgroup G) (t : G) (ht : t ∈ D.T)
    (hcore : E ⊓ conjugate E t ≤ D.S g)
    (hcomm : ⁅E,oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L
      ProductDecomposition.leftFactor⁆ ≤ D.VL)
    (hexchange : conjugate
      (oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L
        ProductDecomposition.leftFactor) t =
      oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L
        ProductDecomposition.rightFactor) : E ⊓ conjugate E t ≤ D.VL := by
  apply le_natural_of_two_residual_commutators d f hΩ _ hcore
  · exact (commutator_mono inf_le_left le_rfl).trans hcomm
  · have hm := map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hcomm
    rw [map_commutator] at hm
    change ⁅conjugate E t,conjugate
      (oddFactor (moduleProjection d.quotientSymmetricEquiv) D.L
        ProductDecomposition.leftFactor) t⁆ ≤ conjugate D.VL t at hm
    have hVt : conjugate D.VL t = D.VL :=
      mem_normalizer_iff_map_conj_eq.mp (T_normalizes_natural d (D.T.inv_mem ht))
    rw [hexchange,hVt] at hm
    exact (commutator_mono inf_le_right le_rfl).trans hm

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
