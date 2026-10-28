module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Modules.Marks
public import Theory.Representation.BinaryQuadraticPair.ProductMarks

/-!
# The literal quotient configuration for the two natural factors

Transport the canonical S/S₂ conjugation representation through the given
I/S ≃ S₃ × S₃ comparison, retaining its original quotient coordinates.
The marked order-two subgroups of the U-image supply two independent
involutions. Their moved and fixed bounds and the complementary images
of W and Wᵍ construct the quadratic product configuration. The marked
odd element then eliminates the common A₃ × A₃ fixed space.

Generation, the core product, and the hyperplane identities are preceding
structural inputs. The remaining decomposition into the two factor-specific
natural-module sums is not asserted here.

Source: Aschbacher–Smith, G.2.6(5), printed p.336, PDF p.347.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup InvertedCubicTensor
variable {G : Type*} [Group G] {D : Setup G} {g : G}

/-- The intrinsic core quotient followed by its supplied ordered model. -/
def moduleProjection
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* (S₃ × S₃)) : D.I g →* S₃ × S₃ :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g)))

/-- Change the actor through the model while preserving every quotient coordinate. -/
theorem exists_model_representation
    (hES : S₂ D g ≤ D.S g) (hEN : D.I g ≤ normalizer (S₂ D g : Set G))
    [((S₂ D g).subgroupOf (D.S g)).Normal] [IsElementaryAbelian 2 (Quotient D g)]
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* (S₃ × S₃)) :
    ∃ (σ : Representation (ZMod 2) (S₃ × S₃) (Additive (Quotient D g)))
      (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
        (σ.comp (moduleProjection e))),
      ∀ s : D.S g, (c.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) s) := by
  obtain ⟨σ₀, c₀, hc⟩ := exists_quotient_representation hES hEN
  let σ := σ₀.comp e.symm.toMonoidHom
  let c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
      (σ.comp (moduleProjection e)) := {
    section_le := c₀.section_le
    kernel_le := c₀.kernel_le
    normalized := c₀.normalized
    coordinates := c₀.coordinates
    onto := c₀.onto
    kernel_eq := c₀.kernel_eq
    equivariant := by
      intro i s
      simpa [σ, moduleProjection] using c₀.equivariant i s }
  exact ⟨σ, c, hc⟩

private theorem exists_involution_of_card_two (P : Subgroup S₃) (hP : Nat.card P = 2) :
    ∃ t : S₃, t ∈ P ∧ t * t = 1 ∧ t ≠ 1 := by
  obtain ⟨t, ht, _⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hP
  refine ⟨t, t.property, ?_, fun he => ht (Subtype.ext he)⟩
  have hp := congrArg Subtype.val (pow_card_eq_one' (x := t))
  simpa only [hP, coe_pow, coe_one, pow_two, coe_mul] using hp

/-- The marked subspaces supply the product recognition configuration
for the actual quotient model and the actual image of the source g⁻¹. -/
theorem exists_productMark [Finite G]
    (d : Hypothesis D g) (hgen : D.I g = D.L ⊔ D.U)
    (hSU : D.S g ≤ normalizer (D.U : Set G))
    (hsplit : D.S g = coreProduct D g)
    (hVV : D.VL = D.V ⊔ conjugate D.V g)
    (hVU : D.VL ⊓ D.U = D.V)
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* (S₃ × S₃))
    (hL : (D.L.subgroupOf (D.I g)).map (moduleProjection e) =
      (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)))
    (P₁ P₂ : Subgroup S₃)
    (hU : (D.U.subgroupOf (D.I g)).map (moduleProjection e) = P₁.prod P₂)
    (hP₁ : Nat.card P₁ = 2) (hP₂ : Nat.card P₂ = 2)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) (S₃ × S₃) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
      (σ.comp (moduleProjection e))) :
    ∃ t₁ t₂ : S₃, t₁ ∈ P₁ ∧ t₂ ∈ P₂ ∧
      Representation.BinaryQuadraticPair.ProductMark σ (c.imageSpace (D.W g)) t₁ t₂
        (moduleProjection e (⟨g, hgen.symm ▸ mem_sup_left d.g_mem⟩ : D.I g)⁻¹) := by
  obtain ⟨t₁, ht₁, hs₁, hn₁⟩ := exists_involution_of_card_two P₁ hP₁
  obtain ⟨t₂, ht₂, hs₂, hn₂⟩ := exists_involution_of_card_two P₂ hP₂
  have hq := quotient_quadratic d.base d.closure hSU (σ.comp (moduleProjection e)) c
  have hr (b : S₃ × S₃) (hb : b ∈ P₁.prod P₂) :
      LinearMap.range (σ b - 1) ≤ c.imageSpace (D.W g) := by
    rw [← hU] at hb
    obtain ⟨u, hu, rfl⟩ := hb
    exact hq.1 u hu
  have hf (b : S₃ × S₃) (hb : b ∈ P₁.prod P₂) :
      ∀ v ∈ c.imageSpace (D.W g), σ b v = v := by
    rw [← hU] at hb
    obtain ⟨u, hu, rfl⟩ := hb
    exact hq.2.1 u hu
  refine ⟨t₁, t₂, ht₁, ht₂, hs₁, hn₁, hs₂, hn₂, ?_,
    hf (t₁, 1) ⟨ht₁, P₂.one_mem⟩, hf (1, t₂) ⟨P₁.one_mem, ht₂⟩,
    hr (t₁, 1) ⟨ht₁, P₂.one_mem⟩, hr (1, t₂) ⟨P₁.one_mem, ht₂⟩, ?_⟩
  · rw [← hL]
    exact mem_map_of_mem (moduleProjection e) (D.L.inv_mem d.g_mem)
  · have hgI : g ∈ D.I g := hgen.symm ▸ mem_sup_left d.g_mem
    have he := c.imageSpace_conjBy (D.W g) (show D.W g ≤ D.S g from inf_le_right)
      (⟨g, hgI⟩ : D.I g)⁻¹
    have hc := marked_images_complementary d hgen hSU hsplit hVV hVU c
    change c.imageSpace (conjugate (D.W g) g) = _ at he
    simpa only [he, MonoidHom.comp_apply] using hc

/-- Normality is relative to S; no normality in the ambient group is asserted. -/
theorem moduleSectionNormal [Finite G] (d : Hypothesis D g) (hgen : D.I g = D.L ⊔ D.U) :
    ((S₂ D g).subgroupOf (D.S g)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact (pCoreIn_le 2 (D.I g)).trans
    (le_normalizer_iff_commutator_le_left.mpr ((d.layers hgen).2.2.2.2.trans le_sup_left))

/-- The preceding structural results give exponent two on the actual quotient. -/
theorem moduleSectionElementary [Finite G] (d : Hypothesis D g)
    (hgen : D.I g = D.L ⊔ D.U)
    (hSU : D.S g ≤ normalizer (D.U : Set G)) (hsplit : D.S g = coreProduct D g)
    [((S₂ D g).subgroupOf (D.S g)).Normal] : IsElementaryAbelian 2 (Quotient D g) := by
  exact quotient_elementary d.base d.closure d.g_mem
    (hgen.symm ▸ mem_sup_left d.g_mem)
    (le_normalizer_iff_commutator_le_left.mpr ((d.layers hgen).2.2.2.2.trans le_sup_left)) hSU hsplit

/-- Application to the literal S/S₂: construct its elementary structure,
canonical conjugation coordinates, complementary marks and zero common
odd fixed space from the preceding structural conclusions of G.2.6. -/
theorem source_quotient_configuration [Finite G]
    (d : Hypothesis D g) (hgen : D.I g = D.L ⊔ D.U)
    (hSU : D.S g ≤ normalizer (D.U : Set G))
    (hsplit : D.S g = coreProduct D g)
    (hVV : D.VL = D.V ⊔ conjugate D.V g)
    (hVU : D.VL ⊓ D.U = D.V)
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* (S₃ × S₃))
    (hL : (D.L.subgroupOf (D.I g)).map (moduleProjection e) =
      (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)))
    (P₁ P₂ : Subgroup S₃)
    (hU : (D.U.subgroupOf (D.I g)).map (moduleProjection e) = P₁.prod P₂)
    (hP₁ : Nat.card P₁ = 2) (hP₂ : Nat.card P₂ = 2) :
    letI := moduleSectionNormal d hgen
    letI := moduleSectionElementary d hgen hSU hsplit
    ∃ (σ : Representation (ZMod 2) (S₃ × S₃) (Additive (Quotient D g)))
      (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
        (σ.comp (moduleProjection e))),
      (∀ s : D.S g, (c.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) s)) ∧
      (∃ t₁ t₂ : S₃, t₁ ∈ P₁ ∧ t₂ ∈ P₂ ∧
        Representation.BinaryQuadraticPair.ProductMark σ (c.imageSpace (D.W g)) t₁ t₂
          (moduleProjection e (⟨g, hgen.symm ▸ mem_sup_left d.g_mem⟩ : D.I g)⁻¹)) ∧
      Representation.BinaryOffender.fixedSpace σ
        ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = ⊥ := by
  let := moduleSectionNormal d hgen
  let := moduleSectionElementary d hgen hSU hsplit
  obtain ⟨σ, c, hc⟩ := exists_model_representation (d.layers hgen).2.1
    (le_normalizer_iff_commutator_le_left.mpr ((d.layers hgen).2.2.2.2.trans le_sup_left)) e
  obtain ⟨t₁, t₂, ht₁, ht₂, hm⟩ := exists_productMark d hgen hSU hsplit hVV hVU
    e hL P₁ P₂ hU hP₁ hP₂ σ c
  exact ⟨σ, c, hc, ⟨t₁, t₂, ht₁, ht₂, hm⟩, hm.common_fixed_eq_bot⟩

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
