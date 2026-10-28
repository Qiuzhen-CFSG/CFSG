module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Sections

/-!
# The two marked upper summands of G.2.4

The source denominator V_L(U∩Uᵍ) need not lie in W. Its two parts
are controlled using V_L=V Vᵍ, with V≤W and Vᵍ≤Wᵍ. Lifting equal
coordinates in the W and Wᵍ images and factoring the denominator proves
that their common value is zero. Generation supplies their sum, and the
original right conjugator supplies the equivariant comparison.

The results apply to any genuine binary conjugation section with this
literal denominator. No natural-module recognition or nonzero summand
is required, so the trivial upper quotient is included.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(6), printed pp.334–335.
-/

@[expose] public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
  (d : Hypothesis D g)
include d

/-- The second layer splits into its parts in W and Wᵍ. This is the
extra denominator argument required when V_L is not contained in U. -/
theorem second_eq_kernel_join (hLI : D.L ≤ D.I g)
    (hVV : D.V ⊔ conjugate D.V g = D.VL) :
    S₂ D g = (D.W g ⊓ S₂ D g) ⊔ (conjugate (D.W g) g ⊓ S₂ D g) := by
  have hVW : D.V ≤ D.W g :=
    le_inf (le_conjugateSpanBy _ _) ((le_sup_left.trans hVV.le).trans
      ((d.central_first hLI).trans inf_le_left))
  have hVgWg : conjugate D.V g ≤ conjugate (D.W g) g := map_mono hVW
  apply le_antisymm _ (sup_le inf_le_right inf_le_right)
  apply sup_le
  · rw [← hVV]
    exact sup_le ((le_inf hVW ((le_sup_left.trans hVV.le).trans le_sup_left)).trans le_sup_left)
      ((le_inf hVgWg ((le_sup_right.trans hVV.le).trans le_sup_left)).trans le_sup_right)
  · intro x hx
    exact mem_sup_left ⟨⟨hx.1, d.second_le_core hLI (mem_sup_right hx)⟩, mem_sup_right hx⟩

/-- Lifting equal quotient coordinates and factoring the actual denominator
proves disjointness of the original two marked images. -/
theorem upper_marked_disjoint (hLI : D.L ≤ D.I g)
    (hVV : D.V ⊔ conjugate D.V g = D.VL)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) (D.I g) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g) ρ) :
    Disjoint (c.imageSpace (D.W g)) (c.imageSpace (conjugate (D.W g) g)) := by
  have hVW : D.V ≤ D.W g :=
    le_inf (le_conjugateSpanBy _ _) ((le_sup_left.trans hVV.le).trans
      ((d.central_first hLI).trans inf_le_left))
  have hVgWg : conjugate D.V g ≤ conjugate (D.W g) g := map_mono hVW
  have hVS : D.V ≤ D.S g := hVW.trans inf_le_right
  have hn : conjugate D.V g ≤ normalizer (D.V : Set G) :=
    ((le_sup_right.trans hVV.le).trans ((d.central_first hLI).trans inf_le_right)).trans
      ((centralizer_le hVS).trans (Subgroup.centralizer_le_normalizer _))
  have hVLprod : (D.VL : Set G) = (D.V : Set G) * (conjugate D.V g : Set G) := by
    rw [← hVV]
    exact coe_mul_of_right_le_normalizer_left _ _ hn
  have hCS : D.U ⊓ conjugate D.U g ≤ D.S g :=
    le_sup_right.trans (d.second_le_core hLI)
  have hCWg : D.U ⊓ conjugate D.U g ≤ conjugate (D.W g) g := by
    rw [d.recognition_conjugate_W hLI]
    exact le_inf inf_le_right hCS
  apply Submodule.disjoint_def.mpr
  intro v hv hv'
  obtain ⟨a, ha, hav⟩ := (c.mem_imageSpace_iff _ _).mp hv
  obtain ⟨b, hb, hbv⟩ := (c.mem_imageSpace_iff _ _).mp hv'
  have he : (a : G) * (b : G)⁻¹ ∈ S₂ D g := by
    apply (c.coordinates_eq_one_iff (a * b⁻¹)).mp
    rw [map_mul, map_inv]
    rw [Multiplicative.toAdd.injective (hav.trans hbv.symm), mul_inv_cancel]
  have heprod : (a : G) * (b : G)⁻¹ ∈
      (D.VL : Set G) * (D.U ⊓ conjugate D.U g : Subgroup G) :=
    (d.second_product hLI) ▸ he
  obtain ⟨z, hz, t, ht, hzt⟩ := heprod
  have hzprod : z ∈ (D.V : Set G) * (conjugate D.V g : Set G) := hVLprod ▸ hz
  obtain ⟨v₀, hv₀, v₁, hv₁, hvv⟩ := hzprod
  have heq : v₀⁻¹ * (a : G) = v₁ * t * (b : G) := by
    rw [← hvv] at hzt
    change v₀ * v₁ * t = (a : G) * (b : G)⁻¹ at hzt
    calc
      v₀⁻¹ * (a : G) = v₀⁻¹ * (((a : G) * (b : G)⁻¹) * (b : G)) := by group
      _ = v₀⁻¹ * ((v₀ * v₁ * t) * (b : G)) := by rw [hzt]
      _ = _ := by group
  have hw : v₀⁻¹ * (a : G) ∈ D.W g := (D.W g).mul_mem
    ((D.W g).inv_mem (hVW hv₀)) ha
  have hwg : v₀⁻¹ * (a : G) ∈ conjugate (D.W g) g := by
    rw [heq]
    exact mul_mem (mul_mem (hVgWg hv₁) (hCWg ht)) hb
  have hker : v₀⁻¹ * (a : G) ∈ S₂ D g :=
    mem_sup_right ⟨hw.1, (map_mono (show D.W g ≤ D.U from inf_le_left)) hwg⟩
  have haE : (a : G) ∈ S₂ D g := by
    have hh := (S₂ D g).mul_mem
      (mem_sup_left ((le_sup_left.trans hVV.le) hv₀)) hker
    simpa only [mul_inv_cancel_left] using hh
  exact hav.symm.trans (show (c.coordinates a).toAdd = 0 from
    congrArg Multiplicative.toAdd ((c.coordinates_eq_one_iff a).mpr haE))

/-- The two literal marked images span and are complementary; equivariance
uses the original right conjugator g. -/
theorem upper_marked_complement (hLI : D.L ≤ D.I g)
    (hsplit : D.S g = D.W g ⊔ conjugate (D.W g) g)
    (hVV : D.V ⊔ conjugate D.V g = D.VL)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) (D.I g) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g) ρ) :
    IsCompl (c.imageSpace (D.W g)) (c.imageSpace (conjugate (D.W g) g)) ∧
    c.imageSpace (conjugate (D.W g) g) =
      (c.imageSpace (D.W g)).map (ρ (⟨g, hLI d.g_mem⟩ : D.I g)⁻¹) := by
  refine ⟨⟨d.upper_marked_disjoint hLI hVV ρ c, ?_⟩,
    c.imageSpace_conjBy (D.W g) inf_le_right (⟨g, hLI d.g_mem⟩ : D.I g)⁻¹⟩
  let f : Subgroup (Multiplicative M) ≃o Submodule (ZMod 2) M :=
    Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2)
  change Codisjoint (f (((D.W g).subgroupOf (D.S g)).map c.coordinates))
    (f (((conjugate (D.W g) g).subgroupOf (D.S g)).map c.coordinates))
  rw [codisjoint_iff, ← f.map_sup, ← f.map_top]
  apply congrArg f
  apply codisjoint_iff.mp
  apply Subgroup.codisjoint_map c.onto
  rw [hsplit]
  exact codisjoint_subgroupOf_sup _ _

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
