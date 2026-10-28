module

public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.SourceActions
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Assembly of orthogonal recognition from the local seed embedding

An injective intertwiner from the actual orthogonal six-space whose image
contains the original vector contains its whole orbit. The source spanning
hypothesis makes the intertwiner surjective, giving an actual equivariant
linear isomorphism. This supplies the final assembly of B.4.13 once its local
geometric embedding has been constructed; that construction remains an
explicit premise here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma B.4.13, printed pp.97–98.
-/

public section

open Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SmallRecognition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual module isomorphism produced by cyclic generation. -/
noncomputable def orthogonalEquivOfEmbedding (e : G ≃* PSL(4, ZMod 2))
    (ρ : Representation (ZMod 2) G V) (v : V)
    (s : OrthogonalSeed e ρ v)
    (hspan : Submodule.span (ZMod 2) (Set.range fun g => ρ g v) = ⊤)
    (f : IntertwiningMap (orthogonalAction e) ρ)
    (hf : Function.Injective f) (hx : f s.point = v) :
    ρ.Equiv (orthogonalAction e) := by
  have hrange : LinearMap.range f.toLinearMap = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro w ⟨g, rfl⟩
    exact ⟨orthogonalAction e g s.point,
      (IntertwiningMap.isIntertwining (orthogonalAction e) ρ f g s.point).trans (by rw [hx])⟩
  exact (f.ofBijective ⟨hf, LinearMap.range_eq_top.mp hrange⟩).symm

/-- Conditional B.4.13 assembly; the local embedding still has to be proved. -/
theorem lemma_B_4_13_of_embedding (e : G ≃* PSL(4, ZMod 2))
    (ρ : Representation (ZMod 2) G V) (v : V)
    (s : OrthogonalSeed e ρ v)
    (hspan : Submodule.span (ZMod 2) (Set.range fun g => ρ g v) = ⊤)
    (hembed : ∃ f : IntertwiningMap (orthogonalAction e) ρ,
      Function.Injective f ∧ f s.point = v) :
    Nonempty (ρ.Equiv (orthogonalAction e)) := by
  obtain ⟨f, hf, hx⟩ := hembed
  exact ⟨orthogonalEquivOfEmbedding e ρ v s hspan f hf hx⟩

end CFSG.Quasithin.ChapterB.SmallRecognition
