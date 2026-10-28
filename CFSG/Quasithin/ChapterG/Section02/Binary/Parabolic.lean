module

public import CFSG.Quasithin.ChapterG.Section02.Applications.Parabolic
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryModule
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryModule.IntersectionCommutator

/-!
# The binary G.2.3 conclusions on the original Section 12.8 flag

The genuine rank-one intersection application supplies the elementary
normal E=U∩Uᵍ. Its point commutators give [E,I₂]=V₂. The original-conjugator
core theorem and the constructed literal quotient action supply the
natural tensor and every fixed/moved-space identity of 12.8.9(2–3).
Only preceding source inputs remain explicit. In particular the Frattini
bound supplies the commutator and square premises of the quotient builder.
Their discharge belongs to the Section12.08 parabolic assembly owner.

Source: Aschbacher–Smith, 12.8.9(2–3), printed pp.852–853.
-/

open Subgroup InvertedCubicTensor
open scoped IsMulCommutative Pointwise _root_.TensorProduct

namespace CFSG.Quasithin.ChapterG.Section02.Applications
open CFSG.Quasithin.Chapter12.Section08

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The full marked 12.8.9(2–3) application, from its preceding source
inputs. The displayed action lives on the actual O₂(I₂)/E quotient. -/
public theorem parabolic_binary_clauses_two_three
    (F : InvariantFlag T V n) [IsMulCommutative V] (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hp : IsPGroup 2 F.U) (hf : (frattini F.U).map F.U.subtype ≤ F.Vi 1)
    (hspan : conjugateSpanBy (F.Vi 2) F.H = F.U)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hPH : (F.P L).pCoreIn 2 ≤ F.H)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    (hindex : F.W.relIndex F.U = 2) :
    ∃ (hN : ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)).Normal),
      letI := hN
      ∃ (hA : IsElementaryAbelian 2
          (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2))),
        letI := hA
        ∃ (σ : Representation (ZMod 2) S₃
            (Additive (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2))))
          (d : Representation.BinaryConjugationSection (F.I₂ L) ((F.I₂ L).pCoreIn 2)
            (F.E g) (σ.comp (F.binaryCoreProjection L e))),
          F.E g = F.U ⊓ conjugate F.U g ∧
          F.Vi 2 ≤ F.E g ∧ F.E g ≤ (F.I₂ L).pCoreIn 2 ∧
          ((F.E g).subgroupOf (F.I₂ L)).Normal ∧
          IsElementaryAbelian 2 (F.E g) ∧
          (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g ∧
          ((F.I₂ L).pCoreIn 2 : Set G) = (F.W : Set G) * (F.X g : Set G) ∧
          ⁅F.E g, F.I₂ L⁆ = F.Vi 2 ∧
          (∀ s : (F.I₂ L).pCoreIn 2, (d.coordinates s).toAdd =
            Additive.ofMul (QuotientGroup.mk' ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) s)) ∧
          Finite (multiplicitySpace σ) ∧
          IsCompl (d.imageSpace F.W) (d.imageSpace (F.X g)) ∧
          (∃ j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
                Additive (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)),
              ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
                  (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
                σ a (j z)) ∧
          ∀ u : F.I₂ L, (u : G) ∈ F.U → (u : G) ∉ F.W →
              LinearMap.ker (σ (F.binaryCoreProjection L e u) - (1 : Module.End (ZMod 2) (Additive (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2))))) = d.imageSpace F.W ∧
              LinearMap.range (σ (F.binaryCoreProjection L e u) - (1 : Module.End (ZMod 2) (Additive (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2))))) = d.imageSpace F.W ∧
              (d.imageSpace (F.X g)).map (σ (F.binaryCoreProjection L e u) - (1 : Module.End (ZMod 2) (Additive (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2))))) =
                d.imageSpace F.W := by
  have hl := parabolic_intersection_layer F hn L hL g hgP hgH hp hf hspan hgen hcore
  have hcomm := derived_le_of_frattini_image_le hp hf
  have hsq : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1 := by
    let : Fact (IsPGroup 2 F.U) := ⟨hp⟩
    intro u hu
    exact hf (mem_map_of_mem F.U.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨u, hu⟩ : F.U)))
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen e hcore hindex
  have hW : F.W = F.U ⊓ (F.I₂ L).pCoreIn 2 := by
    rw [← hcore, ← inf_assoc,
      inf_eq_left.mpr (show F.U ≤ F.I₂ L from le_conjugateSpanBy _ _)]
    rfl
  have hSW : (F.I₂ L).pCoreIn 2 ≤ normalizer (F.W : Set G) := by
    rw [hW]
    exact (le_inf (F.binary_core_normalizes_U L hfactor hPH)
      ((F.I₂ L).pCoreIn 2).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hprod : ((F.I₂ L).pCoreIn 2 : Set G) = (F.W : Set G) * (F.X g : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      ((le_sup_right.trans hsplit.ge).trans hSW), ← hsplit]
  let hN := F.binary_source_E_normal_in_core L hL g hgP hgen hcomm
  let hA := F.binary_source_quotient_elementary L hL g hgP hgen hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsq
  obtain ⟨σ, d, hc, hfinite, hnatural, hmarks⟩ :=
    F.binary_natural_quotient L hL g hgP hfactor hPH hgen e hcore hindex hcomm hsq
  exact ⟨hN, hA, σ, d, hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2.2,
    hsplit, hprod, F.binary_intersection_commutator hn L hL g hgP hgH hgen hcomm hindex,
    hc, hfinite, d.isCompl_imageSpace F.W (F.X g) hsplit rfl, hnatural, hmarks⟩

end CFSG.Quasithin.ChapterG.Section02.Applications
