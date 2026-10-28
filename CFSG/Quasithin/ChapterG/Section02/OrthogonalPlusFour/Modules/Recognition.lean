module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Modules.Configuration
public import Theory.Representation.BinaryQuadraticPair.ProductDecomposition
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The two natural factor modules on the literal G.2.6 quotient

The complementary images of W and Wᵍ construct a quadratic product mark.
Product recognition then splits S/S₂ into two invariant summands, each a
finite sum of the concrete two-dimensional binary natural module for its
own S₃ factor, with the opposite factor acting trivially. Multiplicities
are quantified separately for the two factors, and either may be zero.

The factor preimages lie in the actual I, and the canonical conjugation
coordinates identify each summand with the image of [S,Mᵢ] and with the
fixed space of the other actual factor. The common L-fixed space is zero
by the complementary marks, without an inference from two-perfectness.

`source_quotient_factor_modules` discharges every representation-theoretic
premise on the literal S/S₂, where S₂ = V_L(U ∩ Uᵍ). Its generation,
normalization, core-product, model-image and hyperplane inputs are earlier
structural conclusions, retained for the full G.2.6 assembly owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.2.6(5), printed p.336, PDF p.347, 1 March 2004 manuscript.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup InvertedCubicTensor
open Representation.BinaryOffender Representation.BinaryQuadraticPair
variable {G : Type*} [Group G] {D : Setup G} {g : G}

/-- The actual ambient preimage of a subgroup of the ordered quotient model. -/
def factorPreimage
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* (S₃ × S₃))
    (K : Subgroup (S₃ × S₃)) : Subgroup G :=
  (K.comap (moduleProjection e)).map (D.I g).subtype

theorem factorPreimage_le
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* (S₃ × S₃))
    (K : Subgroup (S₃ × S₃)) : factorPreimage e K ≤ D.I g := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem moduleProjection_surjective
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* (S₃ × S₃)) :
    Function.Surjective (moduleProjection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem factorPreimage_image
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* (S₃ × S₃))
    (K : Subgroup (S₃ × S₃)) :
    ((factorPreimage e K).subgroupOf (D.I g)).map (moduleProjection e) = K := by
  rw [factorPreimage, subgroupOf, comap_map_eq_self_of_injective (D.I g).subtype_injective]
  exact map_comap_eq_self_of_surjective (moduleProjection_surjective e) K

private theorem factorProjection_range
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* (S₃ × S₃))
    (K : Subgroup (S₃ × S₃)) :
    ((moduleProjection e).comp (inclusion (factorPreimage_le e K))).range = K := by
  ext k
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy, he⟩ := x.property
    have he' : y = inclusion (factorPreimage_le e K) x := Subtype.ext he
    change moduleProjection e ((inclusion (factorPreimage_le e K)) x) ∈ K
    change moduleProjection e y ∈ K at hy
    rwa [he'] at hy
  · intro hk
    obtain ⟨i, hi⟩ := moduleProjection_surjective e k
    refine ⟨⟨i, mem_map_of_mem (D.I g).subtype (show i ∈ K.comap (moduleProjection e) from ?_)⟩, hi⟩
    change moduleProjection e i ∈ K
    rwa [hi]

/-- The pulled-back actor fixes exactly the vectors fixed by its model factor. -/
theorem factorPreimage_fixedSpace
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* (S₃ × S₃))
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) (S₃ × S₃) M) (K : Subgroup (S₃ × S₃)) :
    fixedSpace (σ.comp (moduleProjection e)) ((factorPreimage e K).subgroupOf (D.I g)) =
      fixedSpace σ K := by
  rw [fixedSpace_comp_map, factorPreimage_image]

/-- The source commutator quotient uses the actual ambient preimage of the
factor and the original quotient map, with denominator S₂. -/
theorem factorPreimage_commutator_image
    [((S₂ D g).subgroupOf (D.S g)).Normal] [IsElementaryAbelian 2 (Quotient D g)]
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* (S₃ × S₃))
    (σ : Representation (ZMod 2) (S₃ × S₃) (Additive (Quotient D g)))
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
      (σ.comp (moduleProjection e)))
    (hc : ∀ s : D.S g, (c.coordinates s).toAdd =
      Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) s))
    (K : Subgroup (S₃ × S₃)) :
    quotientImage D g ⁅D.S g, factorPreimage e K⁆ =
      binarySubgroup (subspaceCommutator σ ⊤ K) := by
  let q := QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g))
  have hn : factorPreimage e K ≤ normalizer (D.S g : Set G) :=
    (factorPreimage_le e K).trans c.normalized
  have hact : ∀ (x : factorPreimage e K) (s : D.S g),
      σ (((moduleProjection e).comp (inclusion (factorPreimage_le e K))) x)
        (Additive.ofMul (q s)) =
      Additive.ofMul (q ⟨(x : G) * s * (x : G)⁻¹,
        le_normalizer_iff.mp hn x x.property s s.property⟩) := by
    intro x s
    simpa only [hc, q, MonoidHom.comp_apply, coe_inclusion] using
      (c.equivariant (inclusion (factorPreimage_le e K) x) s).symm
  have htop : binarySubgroup (⊤ : Submodule (ZMod 2) (Additive (Quotient D g))) =
      ((D.S g).subgroupOf (D.S g)).map q := by
    rw [subgroupOf_self, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    rfl
  have h := commutator_image_eq σ (D.S g) (D.S g) (factorPreimage e K)
    hn le_rfl ((moduleProjection e).comp (inclusion (factorPreimage_le e K))) q hact ⊤ htop
  rw [factorProjection_range] at h
  exact h

/-- Recognition on the literal G.2.6 quotient. Earlier structural conclusions
remain explicit, and all representation-theoretic premises are discharged.
The two multiplicities in the returned decomposition are independent. -/
theorem source_quotient_factor_modules [Finite G]
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
        (σ.comp (moduleProjection e))) (r : ProductDecomposition σ),
      (∀ s : D.S g, (c.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) s)) ∧
      IsCompl (c.imageSpace (D.W g)) (c.imageSpace (conjugate (D.W g) g)) ∧
      fixedSpace (σ.comp (moduleProjection e)) (D.L.subgroupOf (D.I g)) = ⊥ ∧
      quotientImage D g ⁅D.S g, factorPreimage e ProductDecomposition.leftFactor⁆ =
        binarySubgroup r.left.toSubmodule ∧
      quotientImage D g ⁅D.S g, factorPreimage e ProductDecomposition.rightFactor⁆ =
        binarySubgroup r.right.toSubmodule ∧
      r.left.toSubmodule = fixedSpace (σ.comp (moduleProjection e))
        ((factorPreimage e ProductDecomposition.rightFactor).subgroupOf (D.I g)) ∧
      r.right.toSubmodule = fixedSpace (σ.comp (moduleProjection e))
        ((factorPreimage e ProductDecomposition.leftFactor).subgroupOf (D.I g)) := by
  let := moduleSectionNormal d hgen
  let := moduleSectionElementary d hgen hSU hsplit
  let : FiniteDimensional (ZMod 2) (Additive (Quotient D g)) := Module.Finite.of_finite
  obtain ⟨σ, c, hc, ⟨t₁, t₂, _, _, hm⟩, h0⟩ :=
    source_quotient_configuration d hgen hSU hsplit hVV hVU e hL P₁ P₂ hU hP₁ hP₂
  let r := hm.decomposition
  refine ⟨σ, c, r, hc, marked_images_complementary d hgen hSU hsplit hVV hVU c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fixedSpace_comp_map, hL]
    exact h0
  · rw [factorPreimage_commutator_image e σ c hc, r.left_commutator]
  · rw [factorPreimage_commutator_image e σ c hc, r.right_commutator]
  · rw [factorPreimage_fixedSpace]
    exact r.left_fixed
  · rw [factorPreimage_fixedSpace]
    exact r.right_fixed

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
