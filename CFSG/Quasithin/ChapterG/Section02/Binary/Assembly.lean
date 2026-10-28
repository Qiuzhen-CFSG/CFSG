module

public import CFSG.Quasithin.ChapterG.Section02.Binary.Order

/-!
# The binary G.2.3 deductions after quotient recognition

The earlier Frattini bound supplies both the commutator and square bounds.
The checked rank-one intersection lemmas supply the source series. The
actual elementary quotient, descended action, natural tensor and order
formula are then constructed together, retaining all original markings.

This is explicitly conditional on the earlier quotient-recognition and
generation calculations. It is not the completed G.2.3 source theorem.
Source: Aschbacher–Smith, G.2.3(3–7), printed pp.333–334.
-/

open Subgroup InvertedCubicTensor
open scoped IsMulCommutative Pointwise _root_.TensorProduct

namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]

/-- The normalizer form of the rank-one intersection result. -/
public theorem binary_intersection_normalized (D : Setup G) (g : G)
    (hp : IsPGroup 2 D.U) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hpoint : D.V₁ ≤ D.V) (hIV : D.I g ≤ normalizer (D.V : Set G))
    (hgV : g ∈ normalizer (D.V : Set G))
    (hdis : Disjoint D.V₁ (conjugate D.V₁ g)) :
    D.I g ≤ normalizer (D.S₂ g : Set G) :=
  (normal_subgroupOf_iff_le_normalizer
    (show D.S₂ g ≤ D.I g from inf_le_left.trans le_sup_left)).mp
      (D.rank_one_intersection_layer g hp hf hpoint hIV hgV hdis).2.2.1

/-- The source product is a literal product of the two marked subgroups. -/
public theorem binary_core_product (D : Setup G) (g : G)
    (hg : g ∈ D.I g)
    (e : ((D.I g) ⧸ pCore 2 (D.I g)) ≃* S₃)
    (hnorm : D.S g ≤ normalizer (D.U : Set G))
    (hindex : (D.W g).relIndex D.U = 2) :
    (D.S g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) := by
  have hs := D.binary_core_factorization g hg e hnorm hindex
  have hSW : D.S g ≤ normalizer (D.W g : Set G) :=
    (le_inf hnorm (D.S g).le_normalizer).trans inf_normalizer_le_normalizer_inf
  rw [← coe_mul_of_right_le_normalizer_left _ _
    ((le_sup_right.trans hs.ge).trans hSW), ← hs]

/-- All later binary clauses, including the actual natural decomposition,
its marked fixed spaces, and its multiplicity in the source order formula.
The earlier S₃ recognition, Sylow image and containment L≤I are explicit. -/
public theorem binary_clauses_three_to_seven (D : Setup G) (g : G)
    (hp : IsPGroup 2 D.U) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hpoint : D.V₁ ≤ D.V) (hIV : D.I g ≤ normalizer (D.V : Set G))
    (hgV : g ∈ normalizer (D.V : Set G))
    (hdis : Disjoint D.V₁ (conjugate D.V₁ g))
    (hLI : D.L ≤ D.I g)
    (hirr : ∀ A : Subgroup G, A ≤ D.V → D.L ≤ normalizer (A : Set G) →
      A = ⊥ ∨ A = D.V)
    (hg : g ∈ D.I g)
    (e : ((D.I g) ⧸ pCore 2 (D.I g)) ≃* S₃)
    (hnorm : D.S g ≤ normalizer (D.U : Set G))
    (hindex : (D.W g).relIndex D.U = 2) (hVcard : Nat.card D.V = 4) :
    ∃ (hN : ((D.S₂ g).subgroupOf (D.S g)).Normal),
      letI := hN
      ∃ (hA : IsElementaryAbelian 2 ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))),
        letI := hA
        ∃ (σ : Representation (ZMod 2) S₃
            (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))
          (d : Representation.BinaryConjugationSection (D.I g) (D.S g)
            (D.S₂ g) (σ.comp (D.binaryCoreProjection g e))),
          D.S g = D.W g ⊔ conjugate (D.W g) g ∧
          (D.S g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) ∧
          D.V ≤ D.S₂ g ∧ D.S₂ g ≤ D.S g ∧
          D.V ≤ D.S g ⊓ centralizer (D.S g : Set G) ∧
          (D.V.subgroupOf (D.I g)).Normal ∧
          ((D.S₂ g).subgroupOf (D.I g)).Normal ∧
          ⁅D.S₂ g, D.I g⁆ ≤ D.V ∧ IsElementaryAbelian 2 (D.S₂ g) ∧
          (∀ s : D.S g, (d.coordinates s).toAdd =
            Additive.ofMul (QuotientGroup.mk' ((D.S₂ g).subgroupOf (D.S g)) s)) ∧
          Finite (multiplicitySpace σ) ∧
          IsCompl (d.imageSpace (D.W g)) (d.imageSpace (conjugate (D.W g) g)) ∧
          (∃ j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
                Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g)),
              ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
                  (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
                σ a (j z)) ∧
          Nat.card D.U = 2 ^ (Module.finrank (ZMod 2) (multiplicitySpace σ) + 3) *
            D.V.relIndex (D.S₂ g) ∧
          (∀ u : D.I g, (u : G) ∈ D.U → (u : G) ∉ D.W g →
              LinearMap.ker (σ (D.binaryCoreProjection g e u) - (1 : Module.End (ZMod 2) (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))) = d.imageSpace (D.W g) ∧
              LinearMap.range (σ (D.binaryCoreProjection g e u) - (1 : Module.End (ZMod 2) (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))) = d.imageSpace (D.W g) ∧
              (d.imageSpace (conjugate (D.W g) g)).map (σ (D.binaryCoreProjection g e u) - (1 : Module.End (ZMod 2) (Additive ((D.S g) ⧸ (D.S₂ g).subgroupOf (D.S g))))) =
                d.imageSpace (D.W g)) ∧
          ∀ v, (∀ u : D.I g, (u : G) ∈ D.U → σ (D.binaryCoreProjection g e u) v = v) ↔
            v ∈ d.imageSpace (D.W g) := by
  have hl := D.rank_one_intersection_layer g hp hf hpoint hIV hgV hdis
  have hEN := D.binary_intersection_normalized g hp hf hpoint hIV hgV hdis
  have hs := D.binary_core_factorization g hg e hnorm hindex
  have hcomm := derived_le_of_frattini_image_le hp hf
  have hsq : ∀ u ∈ D.U, u ^ 2 ∈ D.V₁ := by
    let : Fact (IsPGroup 2 D.U) := ⟨hp⟩
    intro u hu
    exact hf (mem_map_of_mem D.U.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨u, hu⟩ : D.U)))
  let hN : ((D.S₂ g).subgroupOf (D.S g)).Normal :=
    normal_subgroupOf_of_le_normalizer ((pCoreIn_le 2 (D.I g)).trans hEN)
  let hA := D.binary_quotient_elementary g hg hgV hpoint hl.1 hl.2.1 hEN hnorm hs hsq
  obtain ⟨σ, d, hc, hfinite, hcompl, ⟨j, hj⟩, hmarks⟩ :=
    D.binary_natural_quotient g hg hgV hpoint hl.1 hl.2.1 hEN e hnorm hindex hcomm hsq
  refine ⟨hN, hA, σ, d, hs, D.binary_core_product g hg e hnorm hindex, hl.1, hl.2.1,
    D.rank_one_central_first_layer g hp hf hpoint hIV hgV hdis hLI hirr,
    normal_subgroupOf_of_le_normalizer hIV, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2,
    hc, hfinite, hcompl, ⟨j, hj⟩,
    D.binary_order_of_natural_quotient g hg e hnorm hindex hl.1 hl.2.1 hVcard σ d j,
    hmarks, ?_⟩
  have hUW : ⁅D.U, D.W g⁆ ≤ D.S₂ g :=
    ((commutator_mono le_rfl (show D.W g ≤ D.U from inf_le_left)).trans hcomm).trans
      (hpoint.trans hl.1)
  have hex : ∃ v : G, v ∈ D.U ∧ v ∉ D.W g := by
    by_contra! h
    have he : (D.W g).relIndex D.U = 1 := relIndex_eq_one.mpr h
    omega
  obtain ⟨u, hu, huw⟩ := hex
  let ui : D.I g := ⟨u, (show D.U ≤ D.I g from le_sup_left) hu⟩
  intro v
  constructor
  · intro hv
    rw [← (hmarks ui hu huw).1]
    change σ (D.binaryCoreProjection g e ui) v - v = 0
    exact sub_eq_zero.mpr (hv ui hu)
  · intro hv a ha
    exact d.fixed_on_imageSpace_of_commutator_le D.U (D.W g) hUW a ha v hv

end CFSG.Quasithin.ChapterG.Section02.Setup
