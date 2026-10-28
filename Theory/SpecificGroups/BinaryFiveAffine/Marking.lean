module
public import Theory.SpecificGroups.BinaryFiveAffine.Centralizer
import Mathlib.Tactic
/-!
# The last-three Klein four-group and the marked centralizer factors

The two-core of the S₄ factor is exactly the even-weight last-three
coordinate group; it is also the intersection of that factor with the
original vector group. Its three nonidentity elements have weight two
and are conjugate to the marked pair vector in the actual affine group.
The final existential packages the literal multiplication decomposition
for the source normalizer transport in Aschbacher–Smith 13.9.10.
-/
@[expose] public section
namespace BinaryFiveAffine
open Subgroup Theory.SpecificGroups.SymmetricSix.DuadCalculation

instance lastThreeDecidable : DecidablePred (· ∈ lastThree) := fun v =>
  inferInstanceAs (Decidable (v.toAdd.val 0 = 0 ∧ v.toAdd.val 1 = 0))
instance lastThreeFintype : Fintype lastThree := Subtype.fintype _

theorem card_lastThree : Nat.card lastThree = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem tailVector_mem (i : Fin 4) : tailVector i ∈ lastThree := by
  change (tailVector i).toAdd.val 0 = 0 ∧ (tailVector i).toAdd.val 1 = 0
  fin_cases i <;> decide +kernel

theorem symmetricEmbedding_vector_iff (g : Equiv.Perm (Fin 4)) :
    symmetricEmbedding g ∈ vectorGroup ↔ g ∈ pCore 2 (Equiv.Perm (Fin 4)) := by
  rw [mem_vectorGroup, ← core_eq]
  change tailPerm (quotientHom g) = 1 ↔ quotientHom g = 1
  exact map_eq_one_iff tailPerm tailPerm_injective

theorem symmetricCore_image : (pCore 2 (Equiv.Perm (Fin 4))).map symmetricEmbedding =
    lastThree.map (SemidirectProduct.inl : V →* W) := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g,hg,rfl⟩
    have hgV := (mem_vectorGroup _).mp ((symmetricEmbedding_vector_iff g).mpr hg)
    refine ⟨tailVector (g 0), tailVector_mem _, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hgV.symm
  · rw [card_map_of_injective SemidirectProduct.inl_injective,
      card_map_of_injective symmetricEmbedding_injective, card_lastThree, ← core_eq, core_card]

theorem X_inter_vector : X ⊓ vectorGroup =
    lastThree.map (SemidirectProduct.inl : V →* W) := by
  rw [← symmetricCore_image]
  apply le_antisymm
  · rintro w ⟨⟨g,rfl⟩,hg⟩
    exact ⟨g,(symmetricEmbedding_vector_iff g).mp hg,rfl⟩
  · rintro _ ⟨g,hg,rfl⟩
    exact ⟨⟨g,rfl⟩,(symmetricEmbedding_vector_iff g).mpr hg⟩

theorem X_twoCore_image : (pCore 2 X).map X.subtype =
    lastThree.map (SemidirectProduct.inl : V →* W) := by
  rw [← pCore_map_iso 2 symmetricEquiv, Subgroup.map_map]
  exact symmetricCore_image

theorem X_twoCore_vectors (x : X) (hx : x ∈ pCore 2 X) (hne : x ≠ 1) :
    ∃ v : V, v ∈ lastThree ∧ weight v = 2 ∧ SemidirectProduct.inl v = x.val := by
  have hm : x.val ∈ (pCore 2 X).map X.subtype := ⟨x,hx,rfl⟩
  rw [X_twoCore_image] at hm
  obtain ⟨v,hv,he⟩ := hm
  refine ⟨v,hv,lastThree_weight v hv ?_,he⟩
  intro h
  apply hne
  apply Subtype.ext
  simp [← he,h]

set_option maxRecDepth 10000 in
theorem lastThree_nonzero_conjugate (v : V) (hv : v ∈ lastThree) (hne : v ≠ 1) :
    ∃ g : W, g * t * g⁻¹ = SemidirectProduct.inl v := by
  have hc : ∀ a : Fin 5 → ZMod 2, ((∑ i,a i)=0 ∧ a 0=0 ∧ a 1=0 ∧ a≠0) →
      a = ![0,0,0,1,1] ∨ a = ![0,0,1,0,1] ∨ a = ![0,0,1,1,0] := by decide +kernel
  have hn : v.toAdd.val ≠ 0 := fun h => hne (Subtype.ext h)
  rcases hc v.toAdd.val ⟨v.toAdd.property,hv.1,hv.2,hn⟩ with h | h | h
  · have he : v=tailVector 1 := Subtype.ext h
    subst v
    refine ⟨SemidirectProduct.inr (Equiv.swap 0 3 * Equiv.swap 1 4), ?_⟩
    apply SemidirectProduct.ext <;> decide +kernel
  · have he : v=tailVector 2 := Subtype.ext h
    subst v
    refine ⟨SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 4), ?_⟩
    apply SemidirectProduct.ext <;> decide +kernel
  · have he : v=tailVector 3 := Subtype.ext h
    subst v
    refine ⟨SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 3), ?_⟩
    apply SemidirectProduct.ext <;> decide +kernel

theorem X_twoCore_conjugate (x : X) (hx : x ∈ pCore 2 X) (hne : x ≠ 1) :
    ∃ g : W, g * t * g⁻¹ = x.val := by
  obtain ⟨v,hv,_,he⟩ := X_twoCore_vectors x hx hne
  rw [← he]
  apply lastThree_nonzero_conjugate v hv
  intro h
  apply hne
  apply Subtype.ext
  simp [← he,h]

theorem exists_marked_factors : ∃ (R₀ X₀ : Subgroup W)
    (split₀ : centralizer ≃* R₀ × X₀)
    (_ : R₀ ≃* DihedralGroup 4) (_ : X₀ ≃* Equiv.Perm (Fin 4)),
    R₀ ≤ centralizer ∧ X₀ ≤ centralizer ∧ t ∈ R₀ ∧
    R₀ ≤ Subgroup.centralizer (X₀ : Set W) ∧
    (∀ c : centralizer, (split₀ c).1.val * (split₀ c).2.val = c.val) ∧
    X₀ ⊓ vectorGroup = lastThree.map (SemidirectProduct.inl : V →* W) ∧
    (pCore 2 X₀).map X₀.subtype = lastThree.map (SemidirectProduct.inl : V →* W) ∧
    (∀ x : X₀, x ∈ pCore 2 X₀ → x ≠ 1 → ∃ g : W, g*t*g⁻¹=x.val) := by
  exact ⟨R,X,split,dihedralEquiv.symm,symmetricEquiv.symm,R_le_centralizer,X_le_centralizer,
    t_mem_R,R_centralizes_X,split_coordinates,X_inter_vector,X_twoCore_image,X_twoCore_conjugate⟩

end BinaryFiveAffine
