module
public import Theory.Representation.SL5ExteriorSquare.TwoGeneratorRecognition.Image
public import Theory.Representation.SL5ExteriorSquare.DecomposablePreserver.NormalizerAction

/-!
# Recognizing the full marked ambient normalizer

Two actual normalizer elements with the checked exterior actions give the lower
image bound. Preservation of the decomposable orbit gives the upper bound via
`DecomposablePreserver.NormalizerAction`. Faithfulness identifies each action
with a unique natural SL₅(2) matrix. The kernel is the literal ambient centralizer
inside the normalizer; when that centralizer equals F, the resulting isomorphism
N_G(F)/F ≃ SL₅(2) retains the original marking and left-conjugation equations.

The transporter and nonidentity-coverage theorems require only the two generators,
so the native class-matching proof can use them before supplying preservation.
This is the ambient application for the native J₄ linear-five construction used
in Aschbacher–Smith 12.5.1. Native existence, class matching, and the centralizer
identity remain inputs owned by that construction.
-/

@[expose] public noncomputable section
namespace Representation.SL5ExteriorSquare.TwoGeneratorRecognition
open SL5TenDimensional
open BinaryConjugationSection
variable {G : Type*} [_root_.Group G] (F : Subgroup G) (c : F ≃* Multiplicative V)

/-- Two marked normalizer elements realize every exterior matrix. -/
theorem exterior_range_le_normalizer_range
    (n0 n1 : (Subgroup.normalizer (F : Set G))) (h0 : ((normalizerAction c.toMonoidHom c.bijective) n0).toLinearMap = exteriorAction 2 A0)
    (h1 : ((normalizerAction c.toMonoidHom c.bijective) n1).toLinearMap = exteriorAction 2 A1) :
    exteriorHom.range ≤ (normalizerAction c.toMonoidHom c.bijective).range := by
  apply range_le_of_generators
  · exact ⟨n0,LinearEquiv.toLinearMap_injective h0⟩
  · exact ⟨n1,LinearEquiv.toLinearMap_injective h1⟩

/-- The upper bound uses preservation of actual decomposable vectors. -/
theorem normalizer_range_le_exterior_range
    (hD : ∀ n : (Subgroup.normalizer (F : Set G)), ∀ x : F, InExteriorOrbit decomposable (c x).toAdd →
      InExteriorOrbit decomposable (c (F.normalizerMonoidHom n x)).toAdd) :
    (normalizerAction c.toMonoidHom c.bijective).range ≤ exteriorHom.range := by
  rintro _ ⟨n,rfl⟩
  obtain ⟨g,hg⟩ := normalizerAction_eq_exteriorAction_of_preserves_decomposable F c n (hD n)
  exact ⟨g,LinearEquiv.toLinearMap_injective hg.symm⟩

/-- Equality for the full ambient normalizer of the literal marked subgroup. -/
theorem normalizer_range_eq_exterior_range
    (n0 n1 : (Subgroup.normalizer (F : Set G))) (h0 : ((normalizerAction c.toMonoidHom c.bijective) n0).toLinearMap = exteriorAction 2 A0)
    (h1 : ((normalizerAction c.toMonoidHom c.bijective) n1).toLinearMap = exteriorAction 2 A1)
    (hD : ∀ n : (Subgroup.normalizer (F : Set G)), ∀ x : F, InExteriorOrbit decomposable (c x).toAdd →
      InExteriorOrbit decomposable (c (F.normalizerMonoidHom n x)).toAdd) :
    (normalizerAction c.toMonoidHom c.bijective).range = exteriorHom.range :=
  le_antisymm (normalizer_range_le_exterior_range F c hD)
    (exterior_range_le_normalizer_range F c n0 n1 h0 h1)

/-- The kernel is literally C_G(F) inside N_G(F), for the specified marking. -/
theorem normalizerAction_ker :
    (normalizerAction c.toMonoidHom c.bijective).ker = (Subgroup.centralizer (F : Set G)).subgroupOf (Subgroup.normalizer (F : Set G)) := by
  rw [← Subgroup.normalizerMonoidHom_ker]
  ext n
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    apply MulEquiv.ext
    intro x
    apply c.injective
    change (c (F.normalizerMonoidHom n x)).toAdd = (c x).toAdd
    have he := normalizerAction_coordinates c.toMonoidHom c.bijective n x
    rw [h] at he
    exact he.symm
  · intro h
    apply LinearEquiv.ext
    intro v
    obtain ⟨x,hx⟩ := c.surjective (Multiplicative.ofAdd v)
    have hv : (c x).toAdd = v := congrArg Multiplicative.toAdd hx
    rw [← hv]
    exact (normalizerAction_coordinates c.toMonoidHom c.bijective n x).trans
      (congrArg (fun y : F => (c y).toAdd) (DFunLike.congr_fun h x))

variable (hD : ∀ n : (Subgroup.normalizer (F : Set G)), ∀ x : F, InExteriorOrbit decomposable (c x).toAdd →
      InExteriorOrbit decomposable (c (F.normalizerMonoidHom n x)).toAdd)

/-- The unique natural matrix inducing each marked normalizer action. -/
def normalizerToSL : (Subgroup.normalizer (F : Set G)) →* Group :=
  (MonoidHom.ofInjective exteriorHom_injective).symm.toMonoidHom.comp
    ((normalizerAction c.toMonoidHom c.bijective).codRestrict exteriorHom.range (fun n =>
      normalizer_range_le_exterior_range F c hD ⟨n,rfl⟩))

@[simp] theorem exteriorHom_normalizerToSL (n : (Subgroup.normalizer (F : Set G))) :
    exteriorHom (normalizerToSL F c hD n) = (normalizerAction c.toMonoidHom c.bijective) n :=
  MonoidHom.apply_ofInjective_symm exteriorHom_injective _

/-- Pointwise intertwining with the original marking and left conjugation. -/
theorem normalizerToSL_intertwines (n : (Subgroup.normalizer (F : Set G))) (x : F) :
    (c (F.normalizerMonoidHom n x)).toAdd =
      exteriorAction 2 (normalizerToSL F c hD n) (c x).toAdd := by
  rw [← exteriorHom_apply, exteriorHom_normalizerToSL]
  exact (normalizerAction_coordinates c.toMonoidHom c.bijective n x).symm

theorem normalizerToSL_ker :
    (normalizerToSL F c hD).ker = (Subgroup.centralizer (F : Set G)).subgroupOf (Subgroup.normalizer (F : Set G)) := by
  rw [← normalizerAction_ker F c]
  ext n
  simp only [MonoidHom.mem_ker]
  rw [← exteriorHom_normalizerToSL F c hD n, ← exteriorHom.map_one,
    exteriorHom_injective.eq_iff]

theorem normalizerToSL_surjective
    (n0 n1 : (Subgroup.normalizer (F : Set G))) (h0 : ((normalizerAction c.toMonoidHom c.bijective) n0).toLinearMap = exteriorAction 2 A0)
    (h1 : ((normalizerAction c.toMonoidHom c.bijective) n1).toLinearMap = exteriorAction 2 A1) :
    Function.Surjective (normalizerToSL F c hD) := by
  intro g
  obtain ⟨n,hn⟩ := exterior_range_le_normalizer_range F c n0 n1 h0 h1
    (show exteriorHom g ∈ exteriorHom.range from ⟨g,rfl⟩)
  exact ⟨n,exteriorHom_injective ((exteriorHom_normalizerToSL F c hD n).trans hn)⟩

variable (n0 n1 : (Subgroup.normalizer (F : Set G))) (h0 : ((normalizerAction c.toMonoidHom c.bijective) n0).toLinearMap = exteriorAction 2 A0)
    (h1 : ((normalizerAction c.toMonoidHom c.bijective) n1).toLinearMap = exteriorAction 2 A1)
    (hC : Subgroup.centralizer (F : Set G) = F)

/-- The resulting isomorphism of the literal normalizer quotient by F. -/
def normalizerQuotientEquiv : ((Subgroup.normalizer (F : Set G)) ⧸ F.subgroupOf (Subgroup.normalizer (F : Set G))) ≃* Group :=
  (QuotientGroup.quotientMulEquivOfEq
    (by rw [normalizerToSL_ker F c hD, hC] :
      F.subgroupOf (Subgroup.normalizer (F : Set G)) = (normalizerToSL F c hD).ker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (normalizerToSL F c hD)
      (normalizerToSL_surjective F c hD n0 n1 h0 h1))

/-- The quotient isomorphism sends each literal representative to its inducing matrix. -/
@[simp] theorem normalizerQuotientEquiv_mk (n : (Subgroup.normalizer (F : Set G))) :
    normalizerQuotientEquiv F c hD n0 n1 h0 h1 hC (QuotientGroup.mk n) =
      normalizerToSL F c hD n := rfl

/-- The quotient action is the exterior square through this very isomorphism. -/
theorem normalizerQuotientEquiv_intertwines (n : (Subgroup.normalizer (F : Set G))) (x : F) :
    (c (F.normalizerMonoidHom n x)).toAdd =
      exteriorAction 2
        (normalizerQuotientEquiv F c hD n0 n1 h0 h1 hC (QuotientGroup.mk n))
        (c x).toAdd :=
  normalizerToSL_intertwines F c hD n x

/-- The representative equation in the original ambient group. -/
theorem normalizerQuotientEquiv_ambient (n : (Subgroup.normalizer (F : Set G))) (x : F) :
    (c.symm (Multiplicative.ofAdd (exteriorAction 2
      (normalizerQuotientEquiv F c hD n0 n1 h0 h1 hC (QuotientGroup.mk n))
      (c x).toAdd)) : G) = (n : G) * (x : G) * (n : G)⁻¹ := by
  rw [← normalizerQuotientEquiv_intertwines F c hD n0 n1 h0 h1 hC n x]
  change (c.symm (c (F.normalizerMonoidHom n x)) : G) = _
  rw [c.symm_apply_apply]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe F n x

include n0 n1 h0 h1 in
/-- The two realized generators lift any exterior transporter. No decomposable
preservation premise is needed, so this can be used to prove native class matching. -/
theorem normalizer_transporter_of_exteriorOrbit (x y : F)
    (hxy : InExteriorOrbit (c x).toAdd (c y).toAdd) :
    ∃ n : Subgroup.normalizer (F : Set G), F.normalizerMonoidHom n x = y := by
  obtain ⟨g,hg⟩ := hxy
  obtain ⟨n,hn⟩ := exterior_range_le_normalizer_range F c n0 n1 h0 h1
    (show exteriorHom g ∈ exteriorHom.range from ⟨g,rfl⟩)
  refine ⟨n,c.injective ?_⟩
  change (c (F.normalizerMonoidHom n x)).toAdd = (c y).toAdd
  have he := normalizerAction_coordinates c.toMonoidHom c.bijective n x
  rw [hn] at he
  exact he.symm.trans hg

include n0 n1 h0 h1 in
/-- Two marked representatives cover all nonidentity elements under ambient
normalizer conjugation, already before establishing the upper bound. -/
theorem normalizer_nonzero_orbits (x0 x1 : F)
    (hx0 : (c x0).toAdd = decomposable) (hx1 : (c x1).toAdd = nondecomposable)
    (y : F) (hy : y ≠ 1) :
    (∃ n : Subgroup.normalizer (F : Set G), F.normalizerMonoidHom n x0 = y) ∨
    (∃ n : Subgroup.normalizer (F : Set G), F.normalizerMonoidHom n x1 = y) := by
  have hyv : (c y).toAdd ≠ 0 := by
    intro he
    apply hy
    apply c.injective
    exact (congrArg Multiplicative.ofAdd he).trans c.map_one.symm
  rcases exterior_orbits_exhaustive (c y).toAdd hyv with h | h
  · exact Or.inl (normalizer_transporter_of_exteriorOrbit F c n0 n1 h0 h1 x0 y
      (hx0.symm ▸ h))
  · exact Or.inr (normalizer_transporter_of_exteriorOrbit F c n0 n1 h0 h1 x1 y
      (hx1.symm ▸ h))

/-- The two named quotient representatives are exactly the supplied natural matrices. -/
theorem normalizerQuotientEquiv_generators :
    normalizerQuotientEquiv F c hD n0 n1 h0 h1 hC (QuotientGroup.mk n0) = A0 ∧
    normalizerQuotientEquiv F c hD n0 n1 h0 h1 hC (QuotientGroup.mk n1) = A1 := by
  constructor
  · apply exteriorHom_injective
    rw [normalizerQuotientEquiv_mk,exteriorHom_normalizerToSL]
    exact LinearEquiv.toLinearMap_injective h0
  · apply exteriorHom_injective
    rw [normalizerQuotientEquiv_mk,exteriorHom_normalizerToSL]
    exact LinearEquiv.toLinearMap_injective h1

include hD n0 n1 h0 h1 in
/-- Orbit transport in the original subgroup, using the full ambient normalizer. -/
theorem normalizer_orbit_iff (x y : F) :
    (∃ n : Subgroup.normalizer (F : Set G), F.normalizerMonoidHom n x = y) ↔
      InExteriorOrbit (c x).toAdd (c y).toAdd := by
  constructor
  · rintro ⟨n,rfl⟩
    exact ⟨normalizerToSL F c hD n,(normalizerToSL_intertwines F c hD n x).symm⟩
  · exact normalizer_transporter_of_exteriorOrbit F c n0 n1 h0 h1 x y

/-- Native conjugation equations suffice to establish the transported linear-map equation. -/
theorem action_eq_of_coordinates (n : Subgroup.normalizer (F : Set G)) (g : Group)
    (hn : ∀ x : F, (c (F.normalizerMonoidHom n x)).toAdd =
      exteriorAction 2 g (c x).toAdd) :
    (normalizerAction c.toMonoidHom c.bijective n).toLinearMap = exteriorAction 2 g := by
  apply LinearMap.ext
  intro v
  obtain ⟨x,hx⟩ := c.surjective (Multiplicative.ofAdd v)
  have hv : (c x).toAdd = v := congrArg Multiplicative.toAdd hx
  rw [← hv]
  exact (normalizerAction_coordinates c.toMonoidHom c.bijective n x).trans (hn x)

end Representation.SL5ExteriorSquare.TwoGeneratorRecognition
