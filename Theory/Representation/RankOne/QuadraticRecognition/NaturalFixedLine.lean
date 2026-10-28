module
public import Theory.Representation.RankOne.QuadraticRecognition.NaturalConsequences

/-!
# The normalizer action on a natural Sylow fixed line

Global transitivity on nonzero natural vectors restricts to transitivity
by the Sylow normalizer: if a matrix takes one nonzero Sylow-fixed vector
to another, the original and conjugated Sylow fixed spaces intersect
nontrivially, so complementarity forces the Sylows to coincide.
Consequently a normalizer-invariant binary subspace of the fixed line is
zero or the whole line. No choice of upper-triangular coordinates is needed.

Source application: DGS, *Groups and Graphs* (1985), 10.5(c), p.156.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V]
local instance naturalFixedLineAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The actual Sylow normalizer is transitive on nonzero natural fixed vectors. -/
theorem normalizer_transitive_on_natural_fixed
    (ρ : Representation (ZMod 2) SL(2,F) V) (S : Sylow 2 SL(2,F))
    (hq : IsQuadratic ρ S) (hgen : GeneratedByFixedSpace ρ S)
    (hfix : fixedSpace ρ ⊤ = ⊥)
    (E : V ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, E (ρ g v) = Matrix.mulVec g.val (E v))
    {v w : V} (hv : v ∈ fixedSpace ρ S) (hw : w ∈ fixedSpace ρ S)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    ∃ g ∈ normalizer (S : Set SL(2,F)), ρ g v = w := by
  obtain ⟨g,hg⟩ := transitive_of_natural_coordinates ρ E he hv0 hw0
  refine ⟨g,?_,hg⟩
  by_contra hn
  have hne : S ≠ g • S := by
    intro h
    exact hn (Sylow.smul_eq_iff_mem_normalizer.mp h.symm)
  have hc := sl2_sylow_fixed_isCompl ρ S (g • S) hne hq hgen hfix
  have hw' : w ∈ fixedSpace ρ (g • S : Sylow 2 SL(2,F)) := by
    change w ∈ fixedSpace ρ ((S : Subgroup SL(2,F)).map (MulAut.conj g).toMonoidHom)
    rw [SL2SylowFixedRecognition.fixedSpace_conjugate]
    exact ⟨v,hv,hg⟩
  exact hw0 (hc.disjoint.le_bot ⟨hw,hw'⟩)

/-- An invariant binary subspace of the natural fixed line is zero or the full line. -/
theorem invariant_subspace_of_natural_fixed
    (ρ : Representation (ZMod 2) SL(2,F) V) (S : Sylow 2 SL(2,F))
    (hq : IsQuadratic ρ S) (hgen : GeneratedByFixedSpace ρ S)
    (hfix : fixedSpace ρ ⊤ = ⊥)
    (E : V ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, E (ρ g v) = Matrix.mulVec g.val (E v))
    (A : Submodule (ZMod 2) V) (hA : A ≤ fixedSpace ρ S)
    (hn : ∀ g ∈ normalizer (S : Set SL(2,F)), ∀ v ∈ A, ρ g v ∈ A) :
    A = ⊥ ∨ A = fixedSpace ρ S := by
  by_cases hb : A = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  apply le_antisymm hA
  intro w hw
  by_cases hw0 : w = 0
  · exact hw0 ▸ A.zero_mem
  obtain ⟨g,hg,hvw⟩ := normalizer_transitive_on_natural_fixed ρ S hq hgen hfix E he
    (hA hv) hw hv0 hw0
  exact hvw ▸ hn g hg v hv

end Representation.RankOne.QuadraticRecognition
