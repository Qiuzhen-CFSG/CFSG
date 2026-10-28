module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Central characters of the six PSL₃(4) tensor words

A scalar of order three acts on the four concrete restricted factors by
exponents 0, 1, 2, 0. On a two-letter word its exponent is the first weight
plus twice the second. Thus precisely the two equal natural/dual pairs and
the four pairs of trivial/adjoint factors kill the center. Applying this test
to the existing complete SL₃ catalogue retains an actual representation
equivalence for every irreducible that factors through the central quotient.

This is the central-kernel reduction in Aschbacher–Smith H.4.7, printed p.382
of refs/quasithin.pdf. Binary descent and involution displacement are separate
steps; this module does not claim the final source theorem.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open scoped MatrixGroups TensorProduct
open Representation Representation.SL3.BinaryDefiningFactors
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four
variable {F K : Type*} [Field F] [Field K]

def centralWeight : Factor → ℕ
  | .trivial => 0
  | .natural => 1
  | .dual => 2
  | .adjoint => 0

private theorem natural_scalar (ι : F →+* K) (g : SL(3,F)) (a : F)
    (hg : g.val = Matrix.scalar (Fin 3) a) : natural ι g = ι a • 1 := by
  apply LinearMap.ext
  intro v
  funext i
  simp [natural, specialLinearNatural_apply, hg, Matrix.scalar, Matrix.mulVec,
    dotProduct, Matrix.diagonal, apply_ite]

private theorem natural_inv_scalar (ι : F →+* K) (g : SL(3,F)) (a : F)
    (ha : a ^ 3 = 1) (hg : g.val = Matrix.scalar (Fin 3) a) :
    natural ι g⁻¹ = (ι a) ^ 2 • 1 := by
  have h3 : (ι a) ^ 3 = 1 := by rw [← map_pow, ha, map_one]
  calc
    natural ι g⁻¹ = ((ι a) ^ 3) • natural ι g⁻¹ := by rw [h3, one_smul]
    _ = (ι a) ^ 2 • (natural ι g * natural ι g⁻¹) := by
      rw [natural_scalar ι g a hg, smul_mul_assoc, one_mul, smul_smul, ← pow_succ]
    _ = (ι a) ^ 2 • 1 := by rw [← map_mul, mul_inv_cancel, map_one]

theorem factorRep_scalar (ι : F →+* K) (g : SL(3,F)) (a : F)
    (ha : a ^ 3 = 1) (hg : g.val = Matrix.scalar (Fin 3) a) (b : Factor) :
    factorRep ι b g = (ι a) ^ centralWeight b • 1 := by
  cases b with
  | trivial => simp only [centralWeight, pow_zero, one_smul]; rfl
  | natural =>
    change natural ι g = (ι a)^1 • 1
    simpa only [pow_one] using natural_scalar ι g a hg
  | dual =>
    change (natural ι).dual g = (ι a)^2 • 1
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    change f (natural ι g⁻¹ v) = (ι a) ^ 2 * f v
    rw [natural_inv_scalar ι g a ha hg]
    simp
  | adjoint =>
    change (traceZero ι).toRepresentation g = (ι a)^0 • 1
    simp only [pow_zero, one_smul]
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    funext i
    change (natural ι g (f.val (natural ι g⁻¹ v))) i = f.val v i
    rw [natural_scalar ι g a hg, natural_inv_scalar ι g a ha hg]
    simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [← mul_assoc, ← pow_succ, ← map_pow, ha, map_one, one_mul]

variable [CharP K 2]

theorem pairRep_scalar (ι : F →+* K) (g : SL(3,F)) (a : F)
    (ha : a ^ 3 = 1) (hg : g.val = Matrix.scalar (Fin 3) a) (b c : Factor) :
    wordRep ι [b,c] g = (ι a) ^ (centralWeight b + 2 * centralWeight c) • 1 := by
  dsimp only [WordSpace, WordModule]
  change TensorProduct.map (factorRep ι b g)
    (TensorProduct.map (factorRep ((frobenius K 2).comp ι) c g) 1) = _
  rw [factorRep_scalar ι g a ha hg, factorRep_scalar _ g a ha hg,
    TensorProduct.map_smul_left, TensorProduct.map_smul_left, TensorProduct.map_one,
    TensorProduct.map_smul_right, TensorProduct.map_one,
    smul_smul]
  congr 1
  change (ι a) ^ centralWeight b * ((ι a) ^ 2) ^ centralWeight c = _
  rw [← pow_mul, pow_add]

/-- Exactly the six pairs on which the central cubic acts trivially. -/
def PairSurvives (b c : Factor) : Prop :=
  (b = .natural ∧ c = .natural) ∨ (b = .dual ∧ c = .dual) ∨
    ((b = .trivial ∨ b = .adjoint) ∧ (c = .trivial ∨ c = .adjoint))

theorem pairRep_scalar_eq_one_iff (ι : F →+* K) (g : SL(3,F)) (a : F)
    (ha : orderOf a = 3) (hg : g.val = Matrix.scalar (Fin 3) a) (b c : Factor) :
    wordRep ι [b,c] g = 1 ↔ PairSurvives b c := by
  have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hpos : 0 < Module.finrank K (WordSpace K [b,c]) := by
    rw [finrank_wordSpace]
    cases b <;> cases c <;> norm_num [wordDegree, Factor.dimension]
  let : Nontrivial (WordSpace K [b,c]) := Module.finrank_pos_iff.mp hpos
  rw [pairRep_scalar ι g a ha3 hg]
  have hs (x : K) : x • (1 : Module.End K (WordSpace K [b,c])) = 1 ↔ x = 1 := by
    constructor
    · intro h
      apply FaithfulSMul.algebraMap_injective K (Module.End K (WordSpace K [b,c]))
      simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using h
    · rintro rfl
      exact one_smul _ _
  have hoa : orderOf (ι a) = 3 := (orderOf_injective ι.toMonoidHom ι.injective a).trans ha
  rw [hs, ← orderOf_dvd_iff_pow_eq_one, hoa]
  cases b <;> cases c <;> norm_num [centralWeight, PairSurvives] <;> decide

variable [Finite F]

omit [Field K] [CharP K 2] in
theorem exists_central_generator (hcard : Nat.card F = 4) :
    ∃ (g : SL(3,F)) (a : F), g ∈ Subgroup.center SL(3,F) ∧
      orderOf a = 3 ∧ g.val = Matrix.scalar (Fin 3) a := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by
    rw [Nat.card_units, hcard])
  have ha' : orderOf (a : F) = 3 := orderOf_units.trans ha
  have ha3 : (a : F) ^ 3 = 1 := ha' ▸ pow_orderOf_eq_one (a : F)
  let g : SL(3,F) := ⟨Matrix.scalar (Fin 3) (a : F), by simpa using ha3⟩
  exact ⟨g, a, Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨a, by simpa using ha3, rfl⟩,
    ha', rfl⟩

theorem center_le_pairRep_ker_iff (ι : F →+* K) (hcard : Nat.card F = 4)
    (b c : Factor) :
    Subgroup.center SL(3,F) ≤ (wordRep ι [b,c]).ker ↔ PairSurvives b c := by
  constructor
  · intro h
    obtain ⟨g,a,hg,ha,hga⟩ := exists_central_generator hcard
    exact (pairRep_scalar_eq_one_iff ι g a ha hga b c).mp (h hg)
  · intro h g hg
    obtain ⟨a,ha,hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
    have ha3 : a ^ 3 = 1 := by simpa using ha
    change wordRep ι [b,c] g = 1
    rw [pairRep_scalar ι g a ha3 hga.symm]
    have hi : (ι a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨hb,hc⟩
    · norm_num [centralWeight, hi]
    · norm_num [centralWeight, show (ι a)^6 = 1 by rw [show 6 = 3*2 from rfl, pow_mul, hi, one_pow]]
    · rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> simp [centralWeight]

variable [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Central descent filters the existing complete catalogue, retaining its actual equivalence. -/
theorem exists_pair_model (ι : F →+* K) (hcard : Nat.card F = 4)
    (ρ : Representation K SL(3,F) V) [IsIrreducible ρ]
    (hcenter : Subgroup.center SL(3,F) ≤ ρ.ker) :
    ∃ b c : Factor, PairSurvives b c ∧ Nonempty (ρ.Equiv (wordRep ι [b,c])) := by
  obtain ⟨w,hw,⟨e⟩⟩ := exists_word_equiv ι 2 (by simpa using hcard) ρ
  obtain ⟨b,c,rfl⟩ := List.length_eq_two.mp hw
  refine ⟨b,c,?_,⟨e⟩⟩
  apply (center_le_pairRep_ker_iff ι hcard b c).mp
  intro g hg
  change wordRep ι [b,c] g = 1
  apply LinearMap.ext
  intro x
  obtain ⟨v,rfl⟩ := e.toLinearEquiv.surjective x
  have he := Representation.IntertwiningMap.isIntertwining ρ (wordRep ι [b,c])
    e.toIntertwiningMap g v
  have hc : ρ g = 1 := hcenter hg
  rw [hc] at he
  convert he.symm using 1 <;> rfl

end CFSG.Quasithin.ChapterH.Section01To04.L3Four
