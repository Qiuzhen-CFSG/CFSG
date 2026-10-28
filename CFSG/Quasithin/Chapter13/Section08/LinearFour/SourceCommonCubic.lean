module
public import Theory.Representation.BinaryParabolicExteriorSquare.ComplementCubic
public import Theory.Representation.CyclicSeedTensor.SeedCentralizer
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorSeed
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages

/-!
# Compatible placement of the scalar cubic

Lift the cubic fixing the first natural plane through the actual two-group
kernel. It fixes V₂/V₁ and therefore normalizes the literal V₂. The first
tensor proves that every pure second-factor actor moving its marked vector
fails to normalize U_H. Consequently the scalar subgroup L₀, which does
normalize U_H, cannot contain the pure second-factor cubic used by the
conditional extra-line norm argument when both tensors use the same
source quotient map.

This is an obstruction to that local placement premise, not to 13.8.28.
The complementary-plane marking supplies the compatible chief accounting;
the extra-line movement argument still needs a different source route.
Earlier setup remains with qt-d-138-six-g2-source and final assembly with
qt-d-1381-source; the local repair belongs to qt-d-138-linear-four-source.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
13.8.29–31, printed pp.964–965, and the L₀ convention in Notation 13.2.1.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups TensorProduct
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryParabolicExteriorSquare.PlaneSpan
variable {G : Type*} [Group G] [Finite G]

/-- Construct one common cubic in the original L₀, with its exact natural matrix. -/
theorem source_common_complement_cubic
    (H D QH : Subgroup G) (hDH : D ≤ H) (hQH : IsPGroup 2 QH)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hcubic : complementElement ∈ (D.subgroupOf H).map π) :
    ∃ (A : Subgroup G) (hAD : A ≤ D) (a : A), Nat.card A = 3 ∧
      (∀ b, b ∈ zpowers a) ∧ (π (inclusion (hAD.trans hDH) a)).val = complementCubic := by
  let πD := π.comp (inclusion hDH)
  have hk : πD.ker = QH.subgroupOf D := by
    ext x
    change inclusion hDH x ∈ π.ker ↔ (x:G) ∈ QH
    rw [hker]
    rfl
  have hc : complementElement ∈ πD.range := by
    obtain ⟨x,hx,he⟩ := hcubic
    exact ⟨⟨x,hx⟩,he⟩
  obtain ⟨B,b,hB,hb,hmat⟩ := exists_complement_cubic πD
    (by rw [hk]; exact hQH.comap_subtype) hc
  let A := B.map D.subtype
  have hAD : A ≤ D := map_subtype_le B
  let E : B ≃* A := B.equivMapOfInjective D.subtype D.subtype_injective
  have hA : Nat.card A = 3 := (Nat.card_congr E.toEquiv).symm.trans hB
  refine ⟨A,hAD,E b,hA,?_,congrArg Subtype.val hmat⟩
  intro x
  obtain ⟨n,hn⟩ := hb (E.symm x)
  refine ⟨n,?_⟩
  change E b ^ n = x
  change b ^ n = E.symm x at hn
  exact (map_zpow E b n).symm.trans ((congrArg E hn).trans (E.apply_symm_apply x))


omit [Finite G] in
/-- The complementary cubic normalizes the literal V₂; no new quotient map
or additional kernel hypothesis is used to place this actor. -/
theorem source_complement_cubic_mem_G2
    (H UH V1 V2 : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2))
    (hnatural : ∀ h v, ρ h v = Matrix.mulVec (π h).val v)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (a : H) (ha : (π a).val = complementCubic) : (a:G) ∈ G2 V2 := by
  have he := d.subspacePreimage_imageSpace V2 h2U h12
  rw [hpoint] at he
  change (a:G) ∈ normalizer (V2:Set G)
  rw [←he,d.mem_normalizer_subspacePreimage_iff]
  rw [Submodule.map_span,Set.image_singleton,hnatural,ha,complementCubic_fixes_point]

/-- One order-three subgroup is lifted inside L₀ and lies in the actual G₂.
The generator, natural marking and quotient kernel are all retained. -/
theorem source_common_complement_cubic_in_G2
    (H D QH UH V1 V2 : Subgroup G) (hDH : D ≤ H) (hQH : IsPGroup 2 QH)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h v, ρ h v = Matrix.mulVec (π h).val v)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hcubic : complementElement ∈ (D.subgroupOf H).map π) :
    ∃ (A : Subgroup G) (hAD : A ≤ D) (a : A), Nat.card A = 3 ∧
      (∀ b, b ∈ zpowers a) ∧
      (π (inclusion (hAD.trans hDH) a)).val = complementCubic ∧ A ≤ G2 V2 := by
  obtain ⟨A,hAD,a,hA,ha,hmat⟩ :=
    source_common_complement_cubic H D QH hDH hQH π hker hcubic
  have haG : (a:G) ∈ G2 V2 := source_complement_cubic_mem_G2
    H UH V1 V2 ρ d π hnatural h12 h2U hpoint (inclusion (hAD.trans hDH) a) hmat
  refine ⟨A,hAD,a,hA,ha,hmat,?_⟩
  intro x hx
  obtain ⟨n,hn⟩ := ha ⟨x,hx⟩
  have he : (a:G)^n = x := congrArg Subtype.val hn
  rw [←he]
  exact (G2 V2).zpow_mem haG n

end CFSG.Quasithin.Chapter13.Section08.LinearFour

open Subgroup Representation
open scoped MatrixGroups TensorProduct
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I U W : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
  (UH V2 : Subgroup G) (π : G2 V2 →* K × I)
  (ρ : Representation (ZMod 2) (K × I) W)
  (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
  (d : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 (ρ.comp π))
  (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I)))
  (himage : f.range.toSubmodule = d.imageSpace UH)
  (u₀ : U) (hcyclic : Submodule.span (ZMod 2) (Set.range fun k => σ k u₀) = ⊤)
  (t : μ.IntertwiningMap (ρ.comp (MonoidHom.inr K I)))
  (ht : t first = f u₀) (a : I) (ha : μ a first = second)
  (hf : Function.Injective f) (b : I)
  (hb0 : μ b first = first) (hb1 : μ b second = first + second)
include himage hcyclic ht ha hf hb0 hb1 in
public theorem source_tensor_swap_not_normalizes
    (g : G2 V2) (hg : π g = (1,a))
    (hV2U : V2 ≤ UH) (hproper : UH ≠ V2) : (g:G) ∉ normalizer (UH:Set G) := by
  intro hn
  have hconj : UH.conjBy (g:G) = UH := mem_normalizer_iff_map_conj_eq.mp hn
  have hh := (source_tensor_two_conjugates UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 g⁻¹ (by simpa only [inv_inv] using hg) hV2U).2
  have hi : ((g⁻¹ : G2 V2) : G)⁻¹ = (g:G) := by simp
  rw [hi,hconj,inf_idem] at hh
  exact hproper hh

include himage hf in
/-- A nonzero marked seed proves that the first tensor slice is larger
than its literal kernel V₂. -/
theorem source_tensor_seed_ne_kernel (hu₀ : u₀ ≠ 0) : UH ≠ V2 := by
  intro he
  have hw : f u₀ ∈ d.imageSpace V2 := by
    rw [←congrArg d.imageSpace he,←himage]
    exact ⟨u₀,rfl⟩
  obtain ⟨x,hx,hcoord⟩ := (d.mem_imageSpace_iff V2 (f u₀)).mp hw
  have hx1 : d.coordinates x = 1 := (d.coordinates_eq_one_iff x).mpr hx
  have hf0 : f u₀ = 0 := hcoord.symm.trans (congrArg Multiplicative.toAdd hx1)
  exact hu₀ (hf (hf0.trans (map_zero f).symm))

include himage hcyclic ht ha hf hb0 hb1 in
public theorem source_scalar_subgroup_tensor_image_ne
    (D : Subgroup G) (hDU : D ≤ normalizer (UH:Set G))
    (g : D) (hg : (g:G) ∈ G2 V2) (hV2U : V2 ≤ UH) (hu₀ : u₀ ≠ 0) :
    π ⟨g,hg⟩ ≠ (1,a) := by
  intro he
  exact source_tensor_swap_not_normalizes UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 ⟨g,hg⟩ he hV2U
    (source_tensor_seed_ne_kernel UH V2 π ρ σ d f himage u₀ hf hu₀) (hDU g.property)

include himage hcyclic ht ha hf hb0 hb1 in
/-- Centralizing the actual V forces trivial action in the second tensor
factor and fixes its marked first-factor seed. This is the source placement
of the common scalar subgroup, on the original product quotient map. -/
theorem source_seed_centralizer_tensor_factors
    (V : Subgroup G) (htimage : t.range.toSubmodule = d.imageSpace V)
    (uNonzero : u₀ ≠ 0) (g : G2 V2) (hg : (g:G) ∈ centralizer (V:Set G)) :
    σ (π g).1 u₀ = u₀ ∧ μ (π g).2 = 1 := by
  let E := source_tensor_coordinates UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1
  have hseed (v : Fin 2 → ZMod 2) : E (u₀ ⊗ₜ[ZMod 2] v) = t v :=
    seed_tensor ρ σ μ f a u₀ t ht ha v
  apply fixed_marked_seed_plane_factors σ μ ρ E u₀ uNonzero (π g)
  intro v
  rw [hseed]
  have hv : t v ∈ d.imageSpace V := by rw [←htimage]; exact ⟨v,rfl⟩
  obtain ⟨x,hx,hcoord⟩ := (d.mem_imageSpace_iff V (t v)).mp hv
  have he : (⟨(g:G) * x * (g:G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized g.property) x).mp x.property⟩ : U0 UH V2) = x := by
    apply Subtype.ext
    change (g:G) * (x:G) * (g:G)⁻¹ = (x:G)
    have hc : (x:G) * (g:G) = (g:G) * x := hg x hx
    rw [←hc,mul_assoc,mul_inv_cancel,mul_one]
  have hh := d.equivariant g x
  rw [he,hcoord] at hh
  exact hh.symm

include himage hcyclic ht ha hf hb0 hb1 in
/-- With the faithful natural I₂-action, the common cubic has literal
second quotient coordinate one, rather than a cubic in that factor. -/
theorem source_scalar_cubic_second_coordinate
    (V D : Subgroup G) (htimage : t.range.toSubmodule = d.imageSpace V)
    (uNonzero : u₀ ≠ 0) (hfaithful : Function.Injective μ)
    (hDV : D ≤ centralizer (V:Set G)) (g : D) (hg : (g:G) ∈ G2 V2) :
    (π ⟨g,hg⟩).2 = 1 := by
  apply hfaithful
  exact (source_seed_centralizer_tensor_factors UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 V htimage uNonzero ⟨g,hg⟩ (hDV g.property)).2.trans
    (map_one μ).symm


include himage hcyclic ht ha hf hb0 hb1 in
/-- The common natural cubic and its tensor placement are realized by the
same original subgroup and generator. Centralization of V determines the
second coordinate of the actual product quotient. -/
theorem source_common_cubic_tensor_placement [Finite G]
    (H D QH V : Subgroup G) (hDH : D ≤ H) (hQH : IsPGroup 2 QH)
    (π₄ : H →* SL(4,ZMod 2)) (hker : π₄.ker = QH.subgroupOf H)
    (hcubic : BinaryParabolicExteriorSquare.PlaneSpan.complementElement ∈
      (D.subgroupOf H).map π₄)
    (hDV : D ≤ centralizer (V:Set G)) (hV2V : V2 ≤ V)
    (htimage : t.range.toSubmodule = d.imageSpace V)
    (uNonzero : u₀ ≠ 0) (hfaithful : Function.Injective μ) :
    ∃ (A : Subgroup G) (hAD : A ≤ D) (a₀ : A) (hAG : A ≤ G2 V2),
      Nat.card A = 3 ∧ (∀ x, x ∈ zpowers a₀) ∧
      (π₄ (inclusion (hAD.trans hDH) a₀)).val =
        BinaryParabolicExteriorSquare.PlaneSpan.complementCubic ∧
      (π (inclusion hAG a₀)).2 = 1 := by
  obtain ⟨A,hAD,a₀,hA,hgen,hmat⟩ :=
    source_common_complement_cubic H D QH hDH hQH π₄ hker hcubic
  have hDG : D ≤ G2 V2 := by
    change D ≤ normalizer (V2:Set G)
    exact hDV.trans ((centralizer_le hV2V).trans (centralizer_le_normalizer (V2:Set G)))
  refine ⟨A,hAD,a₀,hAD.trans hDG,hA,hgen,hmat,?_⟩
  exact source_scalar_cubic_second_coordinate UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 V D htimage uNonzero hfaithful hDV
    (inclusion hAD a₀) (hDG (hAD a₀.property))

end CFSG.Quasithin.Chapter13.Section08.LinearFour
