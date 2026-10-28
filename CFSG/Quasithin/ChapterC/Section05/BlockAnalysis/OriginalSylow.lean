module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Alternating
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalSylow.Geometry
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup.Source

/-!
# The original C.5.6(6) reduction in every block case

The genuine C.5.3–4 producers construct the natural, A₃ or A₅ source setup.
Their actual Sylow section excludes a single block and produces the required
conjugator on the literal stabilizer T₁=N_T(U₁). Thus the original common-normal
counterexample has two blocks, and no action, marking, index or conjugator
conclusion remains an input. The final existence statement retains only the
independently owned earlier C.1.28 source implication and local SQTK of H.

Source: Aschbacher–Smith C.5.6(6), C.5.8, printed pp.157–160.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
universe u
variable {G : Type u} [Group G] [Finite G] {H M K R T : Subgroup G}

/-- C.5.6(6), including the actual C.5.4 source markings in all cases. -/
theorem OriginalHypotheses.source_sylow_replacement
    (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i : Fin b.size) (P : Sylow 2 G) (hP : (P : Subgroup G) = T) :
    b.size = 2 ∧
      let T₁ := T ⊓ normalizer (ambientModule (b.block i) : Set G)
      T₁.relIndex T = 2 ∧ ∃ x ∈ M,
        x ∈ normalizer (T₁ : Set G) ∧ x ^ 2 ∈ T₁ ∧
        ¬ (ambientModule (b.block i)).map (MulAut.conj x⁻¹).toMonoidHom ≤
          centralizer (ambientModule (b.block i) : Set G) := by
  rcases d.rankOne_setup_or_alternating b i with ⟨F,_,⟨h⟩⟩ | ha
  · exact d.rankOne_sylow_replacement b i h P hP
  · exact d.alternating_source_sylow b i ha P hP

/-- The original common-normal counterexample constructs the two-block
Sylow geometry; SQTK is required only for its local group H. -/
theorem OriginalHypotheses.exists_source_sylow_replacement
    (d : OriginalHypotheses H M K R T) {𝒦 : GroupClass.{u}}
    (outside : C128Outside 𝒦) (hH : IsSQTK 𝒦 H)
    (P : Sylow 2 G) (hP : (P : Subgroup G) = T) :
    ∃ b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H),
      b.size = 2 ∧ ∃ i : Fin b.size,
        let T₁ := T ⊓ normalizer (ambientModule (b.block i) : Set G)
        T₁.relIndex T = 2 ∧ ∃ x ∈ M,
          x ∈ normalizer (T₁ : Set G) ∧ x ^ 2 ∈ T₁ ∧
          ¬ (ambientModule (b.block i)).map (MulAut.conj x⁻¹).toMonoidHom ≤
            centralizer (ambientModule (b.block i) : Set G) := by
  obtain ⟨b⟩ := d.block_decomposition_of_local outside hH
  let i : Fin b.size := ⟨0,b.positive⟩
  obtain ⟨hs,h⟩ := d.source_sylow_replacement b i P hP
  exact ⟨b,hs,i,h⟩

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
