module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.Words
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.Reduction

/-!
# Binary vector encoding and orthogonal transport steps

Encoding and decoding recover every vector of the split eight-space. Direct
finite checks establish that both literal small matrices preserve the quadratic
form, not just its polarization. They therefore lift to actual isometries.
Multiplying these lifts transports certified reachable vectors inside the same
matrix-generated subgroup. This supports the finite singular orbit certificate.

Source purpose: the Ω₈⁺(2) section in GLS3 Table 5.3l; see `source/README.md`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
open Packed ClassicalOrthogonal

def vectorCode (v : V) : Fin 256 :=
  ∑ i : Fin 8, if coordinates v i = 0 then 0 else (2 : Fin 256) ^ i.val

def decodeVector (c : Fin 256) : V :=
  coordinates.symm (fun i => bit c.val i.val)

theorem decodeVector_code : ∀ v : V, decodeVector (vectorCode v) = v := by
  decide +kernel

theorem generator_preserves : ∀ (b : Bool) (v : V),
    Q (linearAction (generator b) v) = Q v := by
  decide +kernel

def orthogonalGenerator (b : Bool) : O :=
  ⟨linearAction (generator b),
    (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup Q _).mpr (generator_preserves b)⟩

theorem matrixHom_orthogonalGenerator (b : Bool) :
    matrixHom (orthogonalGenerator b) = generator b :=
  linearAction.symm_apply_apply (generator b)

def Reachable (v : V) : Prop := ∃ g : O,
  matrixHom g ∈ smallGenerated ∧ g.val e0 = v

theorem reachable_e0 : Reachable e0 := by
  refine ⟨1, ?_, rfl⟩
  rw [map_one]
  exact smallGenerated.one_mem

theorem reachable_step (b : Bool) (u v : V)
    (h : linearAction (generator b) u = v) (hu : Reachable u) : Reachable v := by
  obtain ⟨g, hg, hgu⟩ := hu
  refine ⟨orthogonalGenerator b * g, ?_, ?_⟩
  · rw [map_mul, matrixHom_orthogonalGenerator]
    exact smallGenerated.mul_mem (generator_mem b) hg
  · change linearAction (generator b) (g.val e0) = v
    rw [hgu, h]

end Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
