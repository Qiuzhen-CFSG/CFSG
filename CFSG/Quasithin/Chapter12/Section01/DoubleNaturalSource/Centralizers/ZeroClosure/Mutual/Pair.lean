module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Reversing the actual mutually normalizing conjugates

Conjugation by g⁻¹ converts the reverse action on Wᵍ into the action
of Wᵍ⁻¹ on W. The image rank of that action equals the fixed codimension
of the original action. All normalizers and centralizers are literal
ambient subgroups; no ambient normality of W is required.

Source: Aschbacher--Smith, 12.1.3 and 12.1.7, printed pp.789--790,792.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G}
  [IsElementaryAbelian 2 W]

omit [Finite G] in
private theorem centralizer_map (U : Subgroup G) (e : G ≃* G) :
    (centralizer (U : Set G)).map e.toMonoidHom =
      centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

omit [Finite G] [IsElementaryAbelian 2 W] in
theorem reverse_normalizes (g : G)
    (hW : W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)) :
    W.map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (W : Set G) := by
  have hh := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hW
  rw [Subgroup.map_equiv_normalizer_eq] at hh
  have he : (W.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = W := Subgroup.conjBy_inv W g
  rwa [he] at hh

omit [Finite G] [IsElementaryAbelian 2 W] in
/-- Reverse the other normalizer containment of the generated pair. -/
theorem reverse_is_normalized (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G)) :
    W ≤ normalizer (W.map (MulAut.conj g⁻¹).toMonoidHom : Set G) := by
  have hm := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hA
  rw [Subgroup.map_equiv_normalizer_eq] at hm
  have he : (W.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = W := Subgroup.conjBy_inv W g
  rwa [he] at hm

omit [Finite G] [IsElementaryAbelian 2 W] in
theorem reverse_noncentral (g : G)
    (hc : ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ⁅W, W.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≠ ⊥ := by
  intro he
  have hm := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
  rw [Subgroup.map_commutator, Subgroup.map_bot] at hm
  have he' : (W.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = W := Subgroup.conjBy_inv' W g
  rw [he', Subgroup.commutator_comm] at hm
  exact hc hm

theorem reverse_rank (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    (hW : W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)) :
    fixedCodim (automizerRepresentation W)
      (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom)) =
    rank (inducedAutomizer W (W.map (MulAut.conj g⁻¹).toMonoidHom)) := by
  rw [fixedCodim_inducedAutomizer W _ hA,
    rank_inducedAutomizer W _ (reverse_normalizes g hW)]
  unfold subgroupCorank
  have hm := Subgroup.relIndex_map_map_of_injective
    (W ⊓ centralizer (W.map (MulAut.conj g).toMonoidHom : Set G)) W
    (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective, centralizer_map] at hm
  have he : (W.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = W := Subgroup.conjBy_inv W g
  rw [he] at hm
  exact congrArg (Nat.log 2) hm.symm

/-- Choose the larger of the two actual action-image ranks. This is the
source's interchange of W and its conjugate, expressed back on W. -/
theorem exists_ordered (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    (hW : W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G))
    (hc : ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ k : G, (k = g ∨ k = g⁻¹) ∧
      W.map (MulAut.conj k).toMonoidHom ≤ normalizer (W : Set G) ∧
      W ≤ normalizer (W.map (MulAut.conj k).toMonoidHom : Set G) ∧
      ⁅W, W.map (MulAut.conj k).toMonoidHom⁆ ≠ ⊥ ∧
      fixedCodim (automizerRepresentation W)
        (inducedAutomizer W (W.map (MulAut.conj k).toMonoidHom)) ≤
      rank (inducedAutomizer W (W.map (MulAut.conj k).toMonoidHom)) := by
  by_cases ho : fixedCodim (automizerRepresentation W)
      (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom)) ≤
      rank (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom))
  · exact ⟨g, Or.inl rfl, hA, hW, hc, ho⟩
  · have hA' := reverse_normalizes g hW
    have hW' := reverse_is_normalized g hA
    refine ⟨g⁻¹, Or.inr rfl, hA', hW', reverse_noncentral g hc, ?_⟩
    have he := reverse_rank g hA hW
    have he' := reverse_rank g⁻¹ hA' hW'
    simp only [inv_inv] at he'
    omega


end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
