module
public import Theory.Representation.SL2SylowFixedRecognition.Complementary.Coordinates
public import Theory.Representation.SL2SylowFixedRecognition.Reduction

/-!
# General binary SL₂ recognition from Sylow fixed spaces

The central quotient is fully moved and globally fixed-free. Its two standard
root groups are quadratic and generate SL₂, so they give a complementary root
pair. The diagonal word normalizes the upper fixed space, and the reconstructed
field action supplies coordinates for the original actors.

This proves G.1.6 without assuming that the original central extension splits.
Source: Aschbacher--Smith, pp.329--330.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2SylowFixedRecognition

/-- Conjugating the actor conjugates its actual fixed space. -/
theorem fixedSpace_conjugate {G M : Type*} [Group G] [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) G M) (B : Subgroup G) (a : G) :
    fixedSpace ρ (B.map (MulAut.conj a).toMonoidHom) = (fixedSpace ρ B).map (ρ a) := by
  ext v
  constructor
  · intro hv
    refine ⟨ρ a⁻¹ v, ?_, ρ.self_inv_apply a v⟩
    intro b
    have hh := hv ⟨a * b * a⁻¹, b, b.property, rfl⟩
    change ρ (a * b * a⁻¹) v = v at hh
    change ρ (b : G) (ρ a⁻¹ v) = ρ a⁻¹ v
    have hh' := congrArg (ρ a⁻¹) hh
    simpa only [map_mul,Module.End.mul_apply,ρ.inv_self_apply] using hh'
  · rintro ⟨w,hw,rfl⟩ ⟨b,c,hc,rfl⟩
    change ρ (a*c*a⁻¹) (ρ a w) = ρ a w
    simp only [map_mul,Module.End.mul_apply,ρ.inv_self_apply]
    exact congrArg (ρ a) (hw ⟨c,hc⟩)

namespace RootCoordinates
variable {F V : Type*} [Field F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The standard two root groups generate the original matrix group. -/
theorem upper_opposite_generates :
    Matrix.SpecialLinearGroup.upperUnipotent F ⊔
      (Matrix.SpecialLinearGroup.upperUnipotent F).map
        (MulAut.conj (weyl : SL(2,F))).toMonoidHom = ⊤ := by
  let U := Matrix.SpecialLinearGroup.upperUnipotent F
  apply top_unique
  intro g _
  apply Matrix.SL2.transvection_induction
    (fun g => g ∈ U ⊔ U.map (MulAut.conj (weyl : SL(2,F))).toMonoidHom) ?_
    (fun _ _ => mul_mem) g
  intro i j hij t
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact mem_sup_left ⟨Multiplicative.ofAdd t,rfl⟩
  · rw [← weyl_upper_weyl]
    apply mem_sup_right
    refine ⟨upper t,⟨Multiplicative.ofAdd t,rfl⟩,?_⟩
    change weyl * upper t * weyl⁻¹ = weyl * upper t * weyl
    rw [weyl_inv]
  · exact (hij rfl).elim

/-- The quadratic, fully moved, fixed-free action supplies a standard root pair.
There is no conjugation of the actors in the resulting coordinates. -/
theorem natural_of_quadratic_moved_fixed_free [Finite F] [Finite V]
    (ρ : Representation (ZMod 2) SL(2,F) V)
    (hq : IsQuadratic ρ (Matrix.SpecialLinearGroup.upperUnipotent F))
    (hm : subspaceCommutator ρ ⊤ ⊤ = ⊤) (hz : fixedSpace ρ ⊤ = ⊥) :
    NaturalCoordinates ρ := by
  let U := Matrix.SpecialLinearGroup.upperUnipotent F
  let A := fixedSpace ρ U
  have hc : IsCompl A (A.map (ρ weyl)) := by
    change IsCompl (fixedSpace ρ U) ((fixedSpace ρ U).map (ρ weyl))
    rw [← fixedSpace_conjugate]
    exact isCompl_fixedSpace_of_quadratic_generators ρ U _ upper_opposite_generates
      hq (quadratic_conjugate ρ hq weyl) hm hz
  have hu (t : F) : upper t ∈ U := ⟨Multiplicative.ofAdd t,rfl⟩
  have hp : RootPair ρ weyl A := ⟨hc,
    fun t x hx => hx ⟨upper t,hu t⟩,
    fun t x a => hq a a.property (upper t) (hu t) x⟩
  apply natural_coordinates hp
  intro a ha x hx b
  obtain ⟨t,ht⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F b.val).mp b.property
  have he : upper t * diagonalWord a = diagonalWord a * upper (a⁻¹*a⁻¹*t) := by
    have hh := diagonalWord_upper ha (a⁻¹*a⁻¹*t)
    have ht : a*a*(a⁻¹*a⁻¹*t) = t := by field_simp
    simpa only [ht] using hh.symm
  change ρ b.val (ρ (diagonalWord a) x) = ρ (diagonalWord a) x
  rw [← ht]
  change ρ (upper t) (ρ (diagonalWord a) x) = ρ (diagonalWord a) x
  rw [← Module.End.mul_apply,← map_mul,he,map_mul,Module.End.mul_apply,
    show ρ (upper (a⁻¹*a⁻¹*t)) x = x from hx ⟨_,hu _⟩]
end RootCoordinates

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- G.1.6: actual natural coordinates on the literal central quotient. -/
theorem natural_centralQuotient (ρ : Representation (ZMod 2) SL(2,F) V)
    (R : Sylow 2 SL(2,F)) (h : FixedSpaceHypotheses ρ R)
    (d : ℕ) (hd : 2 ≤ d) (hF : Nat.card F = 2^d) :
    NaturalCoordinates (centralQuotient ρ) := by
  let : Finite (V ⧸ fixedSpace ρ ⊤) :=
    Finite.of_surjective _ (fixedSpace ρ ⊤).mkQ_surjective
  have hc : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = 2^2 by norm_num) ▸ Nat.pow_le_pow_right (by decide) hd
  exact RootCoordinates.natural_of_quadratic_moved_fixed_free (centralQuotient ρ)
    (centralQuotient_quadratic ρ R h (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2))
    (centralQuotient_moved_eq_top ρ R h) (centralQuotient_fixed_eq_bot ρ hc)

/-- The original module maps equivariantly onto natural copies, with kernel
exactly its global fixed space. No central extension is assumed to split. -/
theorem quotientCoordinates_of_fixedSpaceHypotheses
    (ρ : Representation (ZMod 2) SL(2,F) V)
    (R : Sylow 2 SL(2,F)) (h : FixedSpaceHypotheses ρ R)
    (d : ℕ) (hd : 2 ≤ d) (hF : Nat.card F = 2^d) :
    Nonempty (QuotientCoordinates ρ) :=
  quotientCoordinates_of_natural ρ (natural_centralQuotient ρ R h d hd hF)

end Representation.SL2SylowFixedRecognition
