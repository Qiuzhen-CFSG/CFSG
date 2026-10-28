module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.ProjectiveDegree
public import Theory.SpecificGroups.PSL2.ThreeInvolutionGeneration

/-!
# Three inner involution conjugates generate the actual source component

Faithful binary irreducibility and the checked central-cover calculation
identify the literal F*(G) with PSL2(q). Its three-conjugate involution
generators pull back through that actual isomorphism and then through the
subgroup inclusion into G. The resulting closure contains F*(G), with
exactly the ambient conjugation convention used by SourceGenerationBounds.

This proves that interface's inner clause without a ratio hypothesis.
The independent outer generation and actor-rank clauses remain with their
own producer and the RankOneSize assembly.

Sources: Aschbacher--Smith K.2, printed p.453; Guralnick--Malle,
Classification of 2F-modules I, (2.6) and Proposition 4.1, pp.4,8--9.
-/

public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
open Subgroup Theory.GroupTheory

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- The inner clause of `SourceGenerationBounds`, on the literal source component in G. -/
theorem source_inner_three_conjugates {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hlarge : 25 < p ^ e)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e))
    (t : G) (htL : t ∈ generalizedFitting G) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ g : Fin 3 → G, generalizedFitting G ≤
      closure (Set.range fun i => g i * t * (g i)⁻¹) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hField, hFin, hF, ⟨f⟩⟩ :=
    source_component_isPSL ρ h (by omega) (ho.pow (n := e)) (by omega) hm
  let tL : generalizedFitting G := ⟨t, htL⟩
  have hft : f tL ≠ 1 := by
    intro heq
    have h1 : tL = 1 := f.injective (heq.trans (map_one f).symm)
    exact ht (congrArg Subtype.val h1)
  have hft2 : (f tL) ^ 2 = 1 := by
    rw [← map_pow]
    have h2 : tL ^ 2 = 1 := Subtype.ext ht2
    rw [h2, map_one]
  obtain ⟨g, hg⟩ := Theory.PSL2.exists_three_involution_conjugates ho he hF hlarge
    (f tL) hft hft2
  let φ := (generalizedFitting G).subtype.comp f.symm.toMonoidHom
  let H := closure (Set.range fun i => φ (g i) * t * (φ (g i))⁻¹)
  have hφ : φ (f tL) = t := by simp [φ, tL]
  have hle : closure (Set.range fun i => g i * f tL * (g i)⁻¹) ≤ H.comap φ := by
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change φ (g i * f tL * (g i)⁻¹) ∈ H
    simp only [map_mul, map_inv, hφ]
    exact subset_closure ⟨i, rfl⟩
  refine ⟨fun i => φ (g i), ?_⟩
  intro x hx
  have hmem : f ⟨x, hx⟩ ∈ H.comap φ := hle (hg ▸ mem_top _)
  change φ (f ⟨x, hx⟩) ∈ H at hmem
  change x ∈ H
  simpa [φ] using hmem

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
