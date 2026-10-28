module

public import Theory.Representation.BinaryNaturalDual.FirstCohomology
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.DualCommutator

/-!
# Natural-plus-dual embeddings in moved sections

Surjectivity of the marked actor and vanishing of the dual fixed space put
the embedded module inside the ambient commutator span. Vanishing of its
own fixed space makes its intersection with the ambient fixed space zero.
Thus passage to the actual moved central quotient preserves injectivity.

Source application: Aschbacher--Smith C.4.8, printed pp.153--154, in the
degree-four doubled-natural exclusion of 12.1.9, printed p.793.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryNaturalDual
variable {D F Y : Type*} [Group D] [Group F] [AddCommGroup Y] [Module (ZMod 2) Y]
    {n : ℕ} (hn : 2 ≤ n)
    (ρ : Representation (ZMod 2) D Y) (K : Subgroup D)
    (p : F →* BinaryLinear.OuterCyclic.LinearGroup n) (hp : Function.Surjective p)
    (q : F →* D) (hq : ∀ x, q x ∈ K)
    (f : CoordinateSpace n →ₗ[ZMod 2] Y) (hf : Function.Injective f)
    (he : ∀ x v, f (naturalDualRepresentation (p x) v) = ρ (q x) (f v))

include hn hp hq hf he in
/-- A natural-plus-dual submodule with a surjective original actor lies in
the ambient moved space and meets the ambient fixed space trivially. -/
theorem embedding_le_moved_and_disjoint_fixed :
    f.range ≤ subspaceCommutator ρ ⊤ K ∧ Disjoint f.range (Representation.BinaryOffender.fixedSpace ρ K) := by
  let σ := naturalDualRepresentation (V := BinaryLinear.OuterCyclic.Space n)
  have hc : Coinvariants.ker σ = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    rw [←invariants_dual_eq_commutator_annihilator]
    exact naturalDual_dual_fixed_eq_bot hn
  constructor
  · have hle : Coinvariants.ker σ ≤ (subspaceCommutator ρ ⊤ K).comap f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a,v⟩,rfl⟩
      obtain ⟨x,rfl⟩ := hp a
      change f (σ (p x) v-v) ∈ subspaceCommutator ρ ⊤ K
      rw [map_sub,he]
      exact Submodule.subset_span ⟨q x,hq x,f v,Submodule.mem_top,rfl⟩
    rintro _ ⟨v,rfl⟩
    exact hle (hc.symm ▸ Submodule.mem_top)
  · apply Submodule.disjoint_def.mpr
    rintro _ ⟨v,rfl⟩ hv
    have hv0 : v ∈ OneCohomology.fixed σ := by
      intro a
      obtain ⟨x,rfl⟩ := hp a
      apply hf
      rw [he]
      exact hv ⟨q x,hq x⟩
    have hvz : v = 0 := by
      simpa only [σ,naturalDual_fixed_eq_bot hn,Submodule.mem_bot] using hv0
    rw [hvz,map_zero]

end BinaryNaturalDual
