module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.Placement
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.Involutions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Recognition

/-!
# Exactly two global F-occurrences in D

Every ambient conjugate of F in D lies in Q and has the full octad-kernel
image. The square-one classification then puts it inside one of the two
constructed elementary groups; equal order gives equality. This quantifies
over all ambient conjugators, not only E- or Q-conjugation. The final theorem
instantiates the literal one-or-two-F normalizer argument, retaining only the
centralizer-container premise for its source branch.

Source: KW (1988), Lemma 1.1.2(ii), p.485, and Proposition 2.2.3, p.491.
-/
@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.Geometry
open Subgroup Cardinality
open Sporadic.Mathieu M24LocalGeometry MathieuCode
open NativeNormalizer
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

/-- D contains exactly the two constructed global F-conjugates. -/
theorem global_conjugates_in_D (g : Model)
    (hD : F.map (MulAut.conj g).toMonoidHom ≤ D) :
    F.map (MulAut.conj g).toMonoidHom = F ∨
      F.map (MulAut.conj g).toMonoidHom = secondF := by
  let H := F.map (MulAut.conj g).toMonoidHom
  let := F_elementary
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.map _
  have hQ := global_conjugate_in_D_le_Q g hD
  have hM := hQ.trans Q_le_M
  have hcard : Nat.card H = 1024 := by
    rw [card_map_of_injective (MulAut.conj g).injective, F_card]
  have hn : ¬ H ≤ E := by
    intro hE
    have hc : centralizer (H : Set Model) ≤ H := by
      intro x hx
      let e := MulAut.conj g
      refine mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [← centralizer_F]
      intro y hy
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)
    have : IsElementaryAbelian 2 E := by
      let := localKernel_elementary matrixA_mul_self matrixB_pow_four
      exact IsElementaryAbelian.map M.subtype
    have heq := le_antisymm hE ((E.le_centralizer.trans (centralizer_le hE)).trans hc)
    have hec : Nat.card E = 2048 := by
      rw [card_map_of_injective M.subtype_injective, localKernel_card]
    rw [heq,hec] at hcard
    omega
  have : IsElementaryAbelian 2 (H.subgroupOf M) := IsElementaryAbelian.subgroupOf hM
  have hc : Nat.card (H.subgroupOf M) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hM).toEquiv
  have hl : H.subgroupOf M ≤ (octadStabilizer O).comap projection := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hD hx
    exact (Subtype.ext he : y=x) ▸ hy
  have hn' : ¬ H.subgroupOf M ≤ localKernel matrixA_mul_self matrixB_pow_four := by
    intro he
    apply hn
    intro x hx
    exact mem_map.mpr ⟨⟨x,hM hx⟩,he hx,rfl⟩
  have hi := local_large_in_D_image (H.subgroupOf M) hl hn' (by rw [hc,hcard])
  rcases elementary_full_image_pair H hQ hi with h | h
  · exact Or.inl (eq_of_le_of_card_ge h (by rw [hcard,F_card]))
  · exact Or.inr (eq_of_le_of_card_ge h (by rw [hcard,secondF_card]))

theorem global_conjugates_in_D_exact :
    {H : Subgroup Model | (∃ g : Model, F.map (MulAut.conj g).toMonoidHom = H) ∧ H ≤ D} =
      {F,secondF} := by
  ext H
  constructor
  · rintro ⟨⟨g,rfl⟩,hD⟩
    exact global_conjugates_in_D g hD
  · rintro (rfl | rfl)
    · exact ⟨⟨1,mem_normalizer_iff_map_conj_eq.mp (normalizer (F : Set Model)).one_mem⟩,
        F_le_Q.trans Q_le_D⟩
    · exact ⟨⟨seed,rfl⟩,secondF_le_Q.trans Q_le_D⟩

/-- The literal one-or-two-F consumer, with its occurrence premise discharged. -/
theorem native_two_occurrence_normalizer (X : Subgroup Model)
    (hXF : X ≤ F) (hCD : centralizer (X : Set Model) ≤ D) :
    normalizer (X : Set Model) ≤ M_F ∨ normalizer (X : Set Model) ≤ M := by
  rw [M_F_eq_fullNormalizer]
  exact ElementaryNormalizerCover.two_occurrence_normalizer_alternatives
    F X seed centralizer_F hXF hCD global_conjugates_in_D intersection_le_E

end Janko4.LocalStructure.LinearFive.Geometry
