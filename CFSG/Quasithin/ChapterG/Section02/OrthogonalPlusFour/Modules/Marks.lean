module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Quotient
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Source

/-!
# Complementary marked images with the plus-four denominator

The kernel is V_L(U ∩ Uᵍ), not W ∩ Wᵍ. Decompose its V_L part as
V Vᵍ. For two marked representatives with equal coordinates, removing
the V part puts their difference in W ∩ Wᵍ, which the quotient kills.
The core product supplies the complementary spanning assertion.

Source: Aschbacher–Smith, G.2.6(5), printed p.336, PDF p.347.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- Complementarity in the actual section, without assuming S₂ ≤ W. -/
theorem marked_images_complementary
    (d : Hypothesis D g) (hgen : D.I g = D.L ⊔ D.U)
    (hSU : D.S g ≤ normalizer (D.U : Set G))
    (hsplit : D.S g = coreProduct D g)
    (hVV : D.VL = D.V ⊔ conjugate D.V g)
    (hVU : D.VL ⊓ D.U = D.V)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) (D.I g) M}
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g) ρ) :
    IsCompl (c.imageSpace (D.W g)) (c.imageSpace (conjugate (D.W g) g)) := by
  have hgI : g ∈ D.I g := hgen.symm ▸ mem_sup_left d.g_mem
  have hVS : D.VL ≤ D.S g := le_sup_left.trans c.kernel_le
  have hVW : D.V ≤ D.W g :=
    le_inf (le_conjugateSpanBy _ _) (d.V_le_VL.trans hVS)
  have hXS : conjugate (D.W g) g ≤ D.S g := by
    rw [conjugate_W D g hgI]
    exact inf_le_right
  have hVgX : conjugate D.V g ≤ conjugate (D.W g) g := map_mono hVW
  have hSV : D.S g ≤ normalizer (D.V : Set G) := by
    rw [← hVU]
    exact (le_inf ((pCoreIn_le 2 (D.I g)).trans d.I_normalizes_VL) hSU).trans
      inf_normalizer_le_normalizer_inf
  have hVLprod : (D.VL : Set G) = (D.V : Set G) * (conjugate D.V g : Set G) := by
    rw [hVV]
    exact coe_mul_of_right_le_normalizer_left _ _ ((hVgX.trans hXS).trans hSV)
  let f : Subgroup (Multiplicative M) ≃o Submodule (ZMod 2) M :=
    Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2)
  apply f.isCompl
  constructor
  · apply disjoint_def.mpr
    rintro y ⟨w, hw, rfl⟩ ⟨x, hx, he⟩
    have hdiff : ((w * x⁻¹ : D.S g) : G) ∈ S₂ D g := by
      apply (c.coordinates_eq_one_iff _).mp
      rw [map_mul, map_inv, he, mul_inv_cancel]
    have hprod : ((w * x⁻¹ : D.S g) : G) ∈
        (D.VL : Set G) * (D.S₂ g : Set G) :=
      S₂_product d.I_normalizes_VL ▸ hdiff
    obtain ⟨vL, hvL, e, heE, hve⟩ := hprod
    obtain ⟨v, hv, vg, hvg, hvvg⟩ := hVLprod ▸ hvL
    change v * vg = vL at hvvg
    change vL * e = (w : G) * (x : G)⁻¹ at hve
    have hvW := hVW hv
    have heWX : e ∈ D.W g ⊓ conjugate (D.W g) g :=
      (marked_intersection hgI c.kernel_le).symm ▸ heE
    have hwe : (w : G) = (v * vg * e) * x := by
      have hh : v * vg * e = (w : G) * (x : G)⁻¹ := by
        rw [hvvg]
        exact hve
      rw [hh, inv_mul_cancel_right]
    have havg : v⁻¹ * (w : G) = vg * e * x := by
      rw [hwe]
      group
    have haW : v⁻¹ * (w : G) ∈ D.W g := (D.W g).mul_mem ((D.W g).inv_mem hvW) hw
    have haX : v⁻¹ * (w : G) ∈ conjugate (D.W g) g := by
      rw [havg]
      exact (conjugate (D.W g) g).mul_mem
        ((conjugate (D.W g) g).mul_mem (hVgX hvg) heWX.2) hx
    have haE : v⁻¹ * (w : G) ∈ S₂ D g := mem_sup_right
      (marked_intersection hgI c.kernel_le ▸ (show v⁻¹ * (w : G) ∈
        D.W g ⊓ conjugate (D.W g) g from ⟨haW, haX⟩))
    let vs : D.S g := ⟨v, hvW.2⟩
    have hv0 : c.coordinates vs = 1 :=
      (c.coordinates_eq_one_iff _).mpr (mem_sup_left (d.V_le_VL hv))
    have ha0 : c.coordinates (vs⁻¹ * w) = 1 := (c.coordinates_eq_one_iff _).mpr haE
    simpa only [map_mul, map_inv, hv0, inv_one, one_mul] using ha0
  · apply Subgroup.codisjoint_map c.onto
    have hs : D.S g = D.W g ⊔ conjugate (D.W g) g := hsplit
    rw [hs]
    exact codisjoint_subgroupOf_sup _ _

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
