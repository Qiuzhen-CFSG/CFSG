module
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.BinaryPermutation
public import Theory.Alternating.Aut
public import Theory.Representation.G2NaturalSemilinear
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# Automorphism-invariant rows in the moved-seed sieve

Inner-field coverage supplies actual binary intertwiners for the natural
SL₂ and G₂ modules. The deleted permutation module extends over the full
automorphism group of Aₙ for n at least five other than six. The binary
G₂ derived action likewise extends over its full conjugation automorphism
group. These intertwiners remove the invariant rows of B.4.2 from D.3.5.

The literal chosen-seed exclusions are in `SeedAlternativesMovedSylowSieve`.
Source: Aschbacher--Smith B.4.2 and D.3.5(5), combined manuscript
of 1 March 2004, printed pp.86 and195--196.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325

/-- The binary deleted permutation module is invariant under every automorphism
of A_n for n at least five other than six. -/
theorem alternating_natural_twist (n : ℕ) (hn : 5 ≤ n) (h6 : n ≠ 6)
    (a : MulAut (alternatingGroup (Fin n))) :
    ∃ c : BinaryPermutation.natural (Fin n) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin n), ∀ g v,
      c (BinaryPermutation.naturalRepresentation (Fin n) g.val v) =
        BinaryPermutation.naturalRepresentation (Fin n) (a g).val (c v) := by
  obtain ⟨p,hp⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    n hn h6).surjective a
  let σ := BinaryPermutation.naturalRepresentation (Fin n)
  refine ⟨LinearEquiv.ofBijective (σ p) (σ.apply_bijective p),?_⟩
  intro g v
  have he : (a g : Equiv.Perm (Fin n)) = p * g.val * p⁻¹ :=
    (congrArg (fun f : MulAut (alternatingGroup (Fin n)) => (f g).val) hp).symm
  change σ p (σ g.val v) = σ (a g).val (σ p v)
  rw [he]
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

/-- The derived binary G₂ module extends to its complete automorphism group. -/
theorem g2_two_derived_natural_twist
    (a : MulAut (commutator (Atlas.G2.Model (ZMod 2)))) :
    ∃ c : Atlas.G2.Natural.Space (ZMod 2) ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2),
      ∀ g v, c (g2Natural (ZMod 2) g.val v) =
        g2Natural (ZMod 2) (a g).val (c v) := by
  obtain ⟨g,rfl⟩ := Atlas.G2.LieAutomorphismExtensions.binaryConjugation_surjective a
  let τ := g2Natural (ZMod 2)
  refine ⟨LinearEquiv.ofBijective (τ g) (τ.apply_bijective g),?_⟩
  intro x v
  change τ g (τ x.val v) = τ (g * x.val * g⁻¹) (τ g v)
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

/-- The full binary G₂ conjugation action also detects every central element
of its actual derived subgroup. -/
theorem g2_two_derived_center_eq_bot :
    center (commutator (Atlas.G2.Model (ZMod 2))) = ⊥ := by
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply Subtype.ext
  apply Atlas.G2.LieAutomorphismExtensions.binaryConjugation_injective
  rw [Subgroup.coe_one,map_one]
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  change x.val * y.val * x.val⁻¹ = y.val
  have he := congrArg Subtype.val (mem_center_iff.mp hx y)
  change y.val * x.val = x.val * y.val at he
  rw [← he,mul_inv_cancel_right]

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Field automorphisms and inner conjugation implement every automorphism
of binary SL₂ on its actual natural space. -/
theorem linear_two_natural_twist (a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ c : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F), ∀ g v,
      c (g.val.mulVec v) = (a g).val.mulVec (c v) := by
  obtain ⟨g,σ,rfl⟩ := Theory.PSL2.sl2_semilinear_coverage a
  let d : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F) :=
    { (Equiv.piCongrRight (fun _ : Fin 2 => σ.toEquiv)) with
      map_add' := by intro v w; ext i; exact map_add σ _ _
      map_smul' := by intro z v; ext i; exact ZMod.map_smul σ.toAddMonoidHom z (v i) }
  let τ := Representation.restrictScalars (k := ZMod 2)
    (specialLinearNatural 2 (k := F))
  let e := LinearEquiv.ofBijective (τ g) (τ.apply_bijective g)
  refine ⟨d.trans e,?_⟩
  intro x v
  have hd : d (x.val.mulVec v) = (Theory.PSL2.sl2FieldAut σ x).val.mulVec (d v) := by
    ext i
    change σ (∑ j, x.val i j * v j) = ∑ j, σ (x.val i j) * σ (v j)
    simp only [map_sum,map_mul]
  change τ g (d (x.val.mulVec v)) =
    τ (g * Theory.PSL2.sl2FieldAut σ x * g⁻¹) (τ g (d v))
  rw [hd]
  change τ g (τ (Theory.PSL2.sl2FieldAut σ x) (d v)) = _
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

/-- The natural G₂ action over a binary field of order greater than two
implements its complete inner-field automorphism group. -/
theorem g2_natural_twist (hq : 2 < Nat.card F) (a : MulAut (Atlas.G2.Model F)) :
    ∃ c : Atlas.G2.Natural.Space F ≃ₗ[ZMod 2] Atlas.G2.Natural.Space F,
      ∀ g v, c (g2Natural F g v) = g2Natural F (a g) (c v) := by
  obtain ⟨g,σ,rfl⟩ := Atlas.G2.LieAutomorphismExtensions.exists_inner_field hq a
  let τ := Representation.restrictScalars (k := ZMod 2) (g2Natural F)
  let d := Atlas.G2.Natural.BinarySemilinear.fieldEquivalence F σ
  let e := LinearEquiv.ofBijective (τ g) (τ.apply_bijective g)
  refine ⟨d.trans e,?_⟩
  intro x v
  change τ g (d (g2Natural F x v)) =
    τ (g * Atlas.G2.LieAutomorphismExtensions.fieldAction σ x * g⁻¹) (τ g (d v))
  rw [Atlas.G2.Natural.BinarySemilinear.fieldEquivalence_action]
  change τ g (τ (Atlas.G2.LieAutomorphismExtensions.fieldAction σ x) (d v)) = _
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
