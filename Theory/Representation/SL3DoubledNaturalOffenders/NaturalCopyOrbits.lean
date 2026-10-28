module
public import Theory.Representation.SL3DoubledNaturalOffenders.BinaryOrbits

/-!
# The source sets as unions of actual natural submodules

Equivariant embeddings give the two coordinate copies and the diagonal.
The previously proved commutant classification shows that these are all
natural copies. Thus the independent-pair orbit is the complement of their
union, and the 14-point orbit is that union minus the swap-invariant copy.
The swap itself is checked as a nontrivial involution on the module.

Source: Aschbacher--Smith, 13.1.12, printed pp.872--873.
-/

public noncomputable section
namespace Representation.SL3DoubledNaturalOffenders.BinaryOrbits
open BinaryLinearThree

@[expose] def firstEmbedding : W.IntertwiningMap rho where
  toFun v := ![v,0]
  map_add' v w := by funext i; fin_cases i <;> simp
  map_smul' c v := by funext i; fin_cases i <;> simp
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i
    · rfl
    · change 0 = W g 0
      simp

@[expose] def secondEmbedding : W.IntertwiningMap rho where
  toFun v := ![0,v]
  map_add' v w := by funext i; fin_cases i <;> simp
  map_smul' c v := by funext i; fin_cases i <;> simp
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i
    · change 0 = W g 0
      simp
    · rfl

theorem firstEmbedding_injective : Function.Injective firstEmbedding := by
  intro v w h
  exact congrFun h 0

theorem secondEmbedding_injective : Function.Injective secondEmbedding := by
  intro v w h
  exact congrFun h 1

theorem firstEmbedding_range : firstEmbedding.toLinearMap.range = firstCopy := by
  ext v
  change (∃ w, (![w,0] : V) = v) ↔ v 1 = 0
  constructor
  · rintro ⟨w,rfl⟩; rfl
  · intro hv
    refine ⟨v 0,?_⟩
    funext i
    fin_cases i
    · rfl
    · exact hv.symm

theorem secondEmbedding_range : secondEmbedding.toLinearMap.range = secondCopy := by
  ext v
  change (∃ w, (![0,w] : V) = v) ↔ v 0 = 0
  constructor
  · rintro ⟨w,rfl⟩; rfl
  · intro hv
    refine ⟨v 1,?_⟩
    funext i
    fin_cases i
    · exact hv.symm
    · rfl

/-- The independent-pair orbit is precisely the complement of the union
of all natural submodules, expressed by actual equivariant embeddings. -/
theorem independent_iff_no_natural_copy (v : V) : v ∈ independent ↔
    ∀ (e : W.IntertwiningMap rho), Function.Injective e → v ∉ e.toLinearMap.range := by
  constructor
  · intro hv e he
    rcases natural_copy_classification e he with hc | hc | hc
    · rw [hc]; exact hv.2.1
    · rw [hc]; exact hv.1
    · rw [hc]; exact hv.2.2
  · intro hv
    refine ⟨?_,?_,?_⟩
    · change v ∉ secondCopy
      rw [← secondEmbedding_range]
      exact hv secondEmbedding secondEmbedding_injective
    · change v ∉ firstCopy
      rw [← firstEmbedding_range]
      exact hv firstEmbedding firstEmbedding_injective
    · change v ∉ diagonal
      rw [← diagonalEmbedding_range]
      exact hv diagonalEmbedding diagonalEmbedding_injective

/-- The possible 14-point orbit is the union of the natural copies with
the unique swap-invariant copy removed. -/
theorem rankOne_iff_natural_copy_not_diagonal (v : V) : v ∈ rankOne ↔
    (∃ (e : W.IntertwiningMap rho), Function.Injective e ∧ v ∈ e.toLinearMap.range) ∧
      v ∉ diagonal := by
  constructor
  · intro hv
    rcases hv with h | h
    · refine ⟨⟨firstEmbedding,firstEmbedding_injective,?_⟩,?_⟩
      · rw [firstEmbedding_range]; exact h.2
      · intro he; exact h.1 (he.trans h.2)
    · refine ⟨⟨secondEmbedding,secondEmbedding_injective,?_⟩,?_⟩
      · rw [secondEmbedding_range]; exact h.1
      · intro he; exact h.2 (he.symm.trans h.1)
  · rintro ⟨⟨e,he,hv⟩,hd⟩
    rcases natural_copy_classification e he with hc | hc | hc
    · rw [hc] at hv
      exact Or.inl ⟨fun hz => hd (hz.trans hv.symm),hv⟩
    · rw [hc] at hv
      exact Or.inr ⟨hv,fun hz => hd (hv.trans hz.symm)⟩
    · exact False.elim (hd (hc ▸ hv))

/-- The multiplicity actor is an actual nontrivial involution on the module. -/
theorem outer_swap_involution : outerRepresentation (1,Equiv.swap 0 1) ≠ 1 ∧
    outerRepresentation (1,Equiv.swap 0 1) ^ 2 = 1 := by
  constructor
  · intro he
    have hh := congrArg (fun f : Module.End (ZMod 2) V => f ![![1,0,0],0] 0 0) he
    exact (by decide : (0 : ZMod 2) ≠ 1) hh
  · rw [pow_two,← map_mul]
    have he : ((1,Equiv.swap 0 1) : BinaryLinearThree.Group × Equiv.Perm (Fin 2)) *
        (1,Equiv.swap 0 1) = 1 := by ext <;> simp
    rw [he,map_one]

end Representation.SL3DoubledNaturalOffenders.BinaryOrbits
