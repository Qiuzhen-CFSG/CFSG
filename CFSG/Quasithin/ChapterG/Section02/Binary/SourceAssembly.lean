module

public import CFSG.Quasithin.ChapterG.Section02.Binary.Geometry
public import CFSG.Quasithin.ChapterG.Section02.Binary.Assembly

/-!
# Source specialization of the binary almost-special deductions

The actual C₃ natural coordinates discharge the four-group order,
irreducibility and displaced-point inputs. G.2.1 and U≤T discharge the
two-group and invariance inputs. This leaves precisely the earlier
quotient-recognition, generation, Sylow-index and core-normalization
calculations; no natural-module or later-series premise remains.

Source: Aschbacher–Smith, G.2.3, printed pp.333–334.
-/

open Subgroup InvertedCubicTensor
open scoped IsMulCommutative Pointwise _root_.TensorProduct

namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]

/-- Specialize all later clauses to the genuine binary source input.
U≤T and the Frattini bound are the allowed preceding G.2.2 conclusions.
The remaining recognition premises are not asserted here. -/
public theorem binary_source_clauses_three_to_seven (D : Setup G)
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (hI : D.I g = D.L ⊔ D.U)
    (e : ((D.I g) ⧸ pCore 2 (D.I g)) ≃* S₃)
    (hnorm : D.S g ≤ normalizer (D.U : Set G))
    (hindex : (D.W g).relIndex D.U = 2) :
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
  obtain ⟨P, hP⟩ := h.sylow_LT
  have hT : IsPGroup 2 D.T := by
    rw [← hP]
    exact P.isPGroup'.map D.LT.subtype
  have hp : IsPGroup 2 D.U :=
    hT.of_injective (inclusion hUT) (inclusion_injective hUT)
  have hIV : D.I g ≤ normalizer (D.V : Set G) := by
    rw [hI]
    exact sup_le b.L_normalizes_V (hUT.trans h.T_normalizes_V)
  have hLI : D.L ≤ D.I g := le_sup_left.trans hI.ge
  exact D.binary_clauses_three_to_seven g hp hf h.point_le hIV
    (b.L_normalizes_V hgL) (b.point_disjoint g hgN) hLI b.irreducible
    (hLI hgL) e hnorm hindex b.card_V

end CFSG.Quasithin.ChapterG.Section02.Setup
