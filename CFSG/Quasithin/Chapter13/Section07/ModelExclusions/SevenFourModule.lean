module
public import Theory.Representation.BinaryAlternatingSevenControl.CentralCovers
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ComponentNormality
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.CoverProjection

/-!
# Full coordinates for a contained four-dimensional A₇ section

Original component normality gives U_H=[U_H,K]. The marked section therefore
supplies a central covering map from U_H/V₁ onto the irreducible four-space.
The A₇ cohomology theorem makes its kernel zero. The resulting linear
equivalence retains the supplied K/O₂(K) marking on every K representative.

Source: Aschbacher–Smith, 13.7.5(1) and 13.7.6(4), printed pp.938–939,
and I.1.5–6, printed p.408.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]

/-- The actual source module has the specified irreducible A₇ four-space coordinates. -/
theorem seven_four_full_module_of_one_le
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) E)
    (hirr : IsIrreducible τ) (hd : Module.finrank (ZMod 2) E = 4)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH τ eK) :
    ∃ eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] E,
      ∀ k : K, ∀ v,
        eV (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) v) =
          τ (eK (QuotientGroup.mk' (pCore 2 K) k)) (eV v) := by
  let : IsIrreducible τ := hirr
  let : FiniteDimensional (ZMod 2) E := Module.finite_of_finrank_pos (by omega)
  let : Module.Finite (ZMod 2) (Additive (Section08.Source.Utilde H V₃ V₁)) :=
    Module.Finite.of_finite
  have hgen := (component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K).2.symm
  obtain ⟨p,hp⟩ := exists_cover_of_section hKH hK ρ hρ hgen τ eK hs
  let eV := LinearEquiv.ofBijective p.toLinearMap
    ⟨BinaryAlternatingSevenControl.four_cover_injective hd p hp,hp.1⟩
  refine ⟨eV,?_⟩
  intro k v
  have he := LinearMap.congr_fun
    (p.isIntertwining' (eK (QuotientGroup.mk' (pCore 2 K) k))) v
  change p (ρ (modelActor hKH hK eK (eK (QuotientGroup.mk' (pCore 2 K) k))) v) = _ at he
  rw [modelActor_mk] at he
  exact he

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
