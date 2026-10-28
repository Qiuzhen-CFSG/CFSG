module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.Transport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.SourceAlignment.Extraction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.SourceAlignment.Conjugacy
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.SourceAlignment.FieldSeparation

/-!
# From the raw source Cartan to simultaneous triality coordinates

Extraction from FH makes B normalize the Sylow intersection in D. The Sylow
intersection is Sylow in the normal component, and simultaneous conjugacy then
constructs a genuine isomorphism taking B into the standard torus and the Sylow
intersection onto the standard positive subgroup.

The concrete field/inner-diagonal separation theorem discharges the automorphism
premise in `hasCartanAlignment_of_raw`. The only remaining model inputs are the
Borel geometry and the positive Sylow witness. The full raw configuration retains
the source field convention, the relative Cartan and the literal products; it
contains no alignment or power-action assumption. The caller supplies the raw
A.3.15(5) case, and the parent source proof supplies those geometric inputs.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, A.3.15(5), pp.50–51; Notation
A.2.5, p.33; and the proof of Proposition 1.3.4, p.511.
-/

@[expose] public section
noncomputable section
open Subgroup
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.CartanAction
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment

/-- The raw source configuration yields alignment once the concrete automorphism
separation is supplied. This theorem is the final reduction, not its discharge. -/
theorem hasCartanAlignment_of_raw_of_separation
    {J : Type*} [Group J] [Finite J] {κ : GroupClass}
    {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}
    (hA : AmbientInput κ D B S p)
    (P : Parameters) (n : ℕ) (e : D ≃* Carrier P)
    (hraw : RawConfiguration P n
      (((S : Subgroup J).subgroupOf D).map e.toMonoidHom)
      ((B.subgroupOf D).map e.toMonoidHom))
    (hG : BorelGeometry P)
    (U : Sylow 2 (Carrier P)) (hU : (U : Subgroup (Carrier P)) = unipotent P)
    (hsep : ∀ a : MulAut (Carrier P), IsSourceFieldAutomorphism P a →
      a ∈ innerDiagonal P → a = 1) :
    HasCartanAlignment D B S P := by
  let : D.Normal := hA.normal
  let : Fact p.Prime := ⟨hA.prime⟩
  have hBN : B.subgroupOf D ≤ normalizer ((S : Subgroup J).subgroupOf D) := by
    have h := hraw.normalizes hsep
    rw [← map_normalizer_eq_of_bijective _ e.bijective] at h
    exact (map_le_map_iff_of_injective e.injective).mp h
  have hp := hA.large
  exact hasCartanAlignment_of_normalizes D B S P hG U hU e
    (by omega : p ≠ 2) hA.p_group hBN

/-- The raw A.3.15(5) triality configuration gives actual simultaneous Cartan
and Sylow coordinates. Field/inner-diagonal separation is proved in the genuine
binary model; only the Borel geometry and positive Sylow witness remain explicit. -/
theorem hasCartanAlignment_of_raw
    {J : Type*} [Group J] [Finite J] {κ : GroupClass}
    {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}
    (hA : AmbientInput κ D B S p)
    (P : Parameters) (n : ℕ) (e : D ≃* Carrier P)
    (hraw : RawConfiguration P n
      (((S : Subgroup J).subgroupOf D).map e.toMonoidHom)
      ((B.subgroupOf D).map e.toMonoidHom))
    (hG : BorelGeometry P)
    (U : Sylow 2 (Carrier P)) (hU : (U : Subgroup (Carrier P)) = unipotent P) :
    HasCartanAlignment D B S P := by
  exact hasCartanAlignment_of_raw_of_separation hA P n e hraw hG U hU
    (sourceField_eq_one_of_mem_innerDiagonal_of_q_eq P n hraw.q_eq hraw.degree_gt_one)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment
