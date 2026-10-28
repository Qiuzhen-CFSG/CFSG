module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.ModelInvolutions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.Relations
public import Theory.Alternating.Theorem523A6

/-!
# An A10 overgroup from Held's marked generators

Eight elements satisfying the relations of Held 5.11 define a homomorphism
from the actual alternating group on ten letters. We use the proved Suzuki
presentation: for the seven involutory generators, the distant product
relations are equivalent to commuting relations. Its proved bijective
projection supplies the comparison with the concrete alternating carrier.

The product of generators 2, 4 and 6 is exactly (01)(23)(45)(67) in these
coordinates. If its image is the distinguished ambient involution, the map
is nontrivial and simplicity of A10 makes it injective. The image of the
model centralizer has order 384 and lies in the original centralizer of
order 384, so they are equal. This proves containment of the whole original
centralizer in the range, without an additional generation assumption.

The result is conditional on constructing the eight elements and their
marked word. That remaining local geometry uses the two ambient hypotheses
from the recognition task (nonfusion and centralizer order 2880). None of
those construction steps is asserted here.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 5.11, pp.238--239.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction
open GLS3.Chapter5.SchurPresentation
universe u
variable {G : Type u} [Group G]

private theorem commute_of_three_squares {a b : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) :
    Commute a b := by
  have hai : a⁻¹ = a := (eq_inv_of_mul_eq_one_left (by simpa [pow_two] using ha)).symm
  have hbi : b⁻¹ = b := (eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hb)).symm
  have habi : (a * b)⁻¹ = a * b :=
    (eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hab)).symm
  change a * b = b * a
  rw [← habi, mul_inv_rev, hai, hbi]

private theorem DicksonRelations.relators {M : Fin 8 → G} (hM : DicksonRelations M)
    (r : SuzukiRelator 5) : FreeGroup.lift M r.word = 1 := by
  cases r with
  | rootCube =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using hM.root_cube
  | tailSquare i hi =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using hM.tail_square i hi
  | rootAdjacentCube =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using hM.adjacent_cube 0
  | tailAdjacentCube i hi =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using hM.adjacent_cube i
  | rootFarSquare j hj =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using hM.distant_square 0 j hj
  | tailFarCommutator i j hi hj hfar =>
      rw [SuzukiRelator.word, map_commutatorElement]
      simp only [suzukiFreeGenerator, FreeGroup.lift_apply_of]
      apply commutatorElement_eq_one_iff_commute.mpr
      rcases hfar with h | h
      · exact commute_of_three_squares (hM.tail_square i hi) (hM.tail_square j hj)
          (hM.distant_square i j h)
      · exact (commute_of_three_squares (hM.tail_square j hj) (hM.tail_square i hi)
          (hM.distant_square j i h)).symm

/-- Held's relations give a homomorphism from the actual A10 carrier,
with the prescribed values on all eight standard generators. -/
public theorem DicksonRelations.exists_hom {M : Fin 8 → G} (hM : DicksonRelations M) :
    ∃ f : alternatingGroup (Fin 10) →* G,
      ∀ i, f (alternatingSuzukiGenerator 5 i) = M i := by
  let h : SuzukiPresentedGroup 5 →* G := PresentedGroup.toGroup (by
    rintro _ ⟨r, rfl⟩
    exact hM.relators r)
  let e : SuzukiPresentedGroup 5 ≃* alternatingGroup (Fin 10) :=
    MulEquiv.ofBijective (suzukiPresentedProjection 5)
      ⟨suzukiPresentedProjection_injective 5, suzukiPresentedProjection_surjective 5⟩
  refine ⟨h.comp e.symm.toMonoidHom, ?_⟩
  intro i
  have he : e (PresentedGroup.of i) = alternatingSuzukiGenerator 5 i :=
    suzukiPresentedProjection_of 5 i
  change h (e.symm (alternatingSuzukiGenerator 5 i)) = M i
  rw [← he, e.symm_apply_apply]
  simp [h]

/-- The concrete standard generators satisfy exactly the source relation family. -/
public theorem suzuki_dicksonRelations : DicksonRelations (alternatingSuzukiGenerator 5) := by
  refine ⟨alternatingSuzukiGenerator_zero_pow_three 5,
    alternatingSuzukiGenerator_tail_sq 5, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      exact alternatingSuzukiGenerator_zero_succ_mul_pow_three 5
    · exact alternatingSuzukiGenerator_tail_mul_pow_three 5 i hi
  · intro i j hij
    by_cases hi : i = 0
    · subst i
      exact alternatingSuzukiGenerator_root_far_mul_sq 5 j hij
    · have hj : j ≠ 0 := by
        intro hj
        subst j
        simp at hij
      exact alternatingSuzukiGenerator_tail_far_mul_sq 5 hi hj (Or.inl hij)

/-- The source word `M₂ M₄ M₆` is the concrete central Sylow involution. -/
public theorem suzuki_central_word :
    alternatingSuzukiGenerator 5 1 * alternatingSuzukiGenerator 5 3 *
      alternatingSuzukiGenerator 5 5 = CentralizerModels.a10Involution := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, alternatingSuzukiGenerator_val]
  decide +kernel

/-- Marking the central involution excludes the trivial presentation image;
simplicity of A10 then gives an embedding preserving that marking. -/
public theorem exists_marked_embedding_of_dicksonRelations (D : LocalData G)
    {M : Fin 8 → G} (hM : DicksonRelations M)
    (hz : M 1 * M 3 * M 5 = D.z) :
    ∃ f : alternatingGroup (Fin 10) →* G,
      Function.Injective f ∧ f CentralizerModels.a10Involution = D.z := by
  obtain ⟨f, hf⟩ := hM.exists_hom
  have hfz : f CentralizerModels.a10Involution = D.z := by
    rw [← suzuki_central_word, map_mul, map_mul, hf, hf, hf, hz]
  refine ⟨f, ?_, hfz⟩
  let : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact f.ker_eq_bot_iff.mp hbot
  · exfalso
    apply D.z_ne_one
    rw [← hfz]
    exact MonoidHom.mem_ker.mp (by rw [htop]; trivial)

/-- Any embedding of A10 preserving the distinguished involution contains
its full ambient centralizer, by equality of the two centralizer orders. -/
public theorem centralizer_le_range_of_marked_embedding [Finite G] (D : LocalData G)
    (f : alternatingGroup (Fin 10) →* G) (hf : Function.Injective f)
    (hz : f CentralizerModels.a10Involution = D.z) :
    D.centralizer ≤ f.range := by
  let C : Subgroup G := CentralizerModels.a10Centralizer.map f
  have hC : C ≤ D.centralizer := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [← hz, ← map_mul, ← map_mul]
    exact congrArg f (mem_centralizer_singleton_iff.mp hx)
  have hcard : Nat.card C = Nat.card D.centralizer := by
    rw [Subgroup.card_map_of_injective hf, centralizer_central_card, D.centralizer_card]
  have heq : C = D.centralizer := Subgroup.eq_of_le_of_card_ge hC hcard.ge
  rw [← heq]
  rintro _ ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

/-- Conditional overgroup construction. The local geometry must supply the
generators, all their relations, and the source central-word identity. -/
public theorem overgroup_of_dicksonRelations [Finite G] (D : LocalData G)
    {M : Fin 8 → G} (hM : DicksonRelations M)
    (hz : M 1 * M 3 * M 5 = D.z) :
    ∃ Q : Subgroup G, D.centralizer ≤ Q ∧ Nonempty (Q ≃* alternatingGroup (Fin 10)) := by
  obtain ⟨f, hf, hfz⟩ := exists_marked_embedding_of_dicksonRelations D hM hz
  exact ⟨f.range, centralizer_le_range_of_marked_embedding D f hf hfz,
    ⟨(MonoidHom.ofInjective hf).symm⟩⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction
