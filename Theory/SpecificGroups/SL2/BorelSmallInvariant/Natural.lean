module

public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.SpecificGroups.SL2.Affine

/-!
# Additive subgroups invariant under the natural Borel action

Every nonzero additive subgroup of the natural plane invariant under the
upper triangular Borel contains the entire first-coordinate line. If a
vector has nonzero second coordinate, subtracting its upper-transvection
image gives this line. Otherwise the diagonal matrices supply the line.
This uses additive closure alone, without assuming closure under F-scalars.

A nonzero coordinate projection gives the corresponding bound on two natural
planes. The homomorphism `naturalPairAction` records the independent matrix
actions, for use with actual quotient-module identifications.

Source: the natural-module case in Aschbacher–Smith, `refs/quasithin.pdf`,
printed p.1164, proof of 15.4.20. These calculations hold over every field;
only the cardinal inequalities require finiteness.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one

/-- A nonzero invariant additive subgroup contains every vector `(t, 0)`. -/
theorem firstLine_mem_of_borel_invariant (W : AddSubgroup (Fin 2 → F)) (hne : W ≠ ⊥)
    (hinv : ∀ g ∈ rankOneBorel F, ∀ v ∈ W, g.val *ᵥ v ∈ W) (t : F) :
    ![t, 0] ∈ W := by
  rcases W.bot_or_exists_ne_zero with h | ⟨v, hv, hv0⟩
  · exact (hne h).elim
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h0
      apply hv0
      ext i
      fin_cases i <;> simp_all
    by_cases ht : t = 0
    · subst t
      have he : (![0, 0] : Fin 2 → F) = 0 := by ext i; fin_cases i <;> rfl
      rw [he]
      exact W.zero_mem
    have ha : t / v 0 ≠ 0 := div_ne_zero ht h0
    have hm := hinv (diag2 (t / v 0) ha) (diag_mem_rankOneBorel _ ha) v hv
    have he : (diag2 (t / v 0) ha).val *ᵥ v = ![t, 0] := by
      ext i
      fin_cases i <;> simp [diag2_coe', mulVec, dotProduct, Fin.sum_univ_two, h1, h0]
    exact he ▸ hm
  · have hm := W.sub_mem (hinv (u (t / v 1)) (upper_mem_rankOneBorel _) v hv) hv
    have he : (u (t / v 1)).val *ᵥ v - v = ![t, 0] := by
      ext i
      fin_cases i <;> simp [transvection_coe, mulVec, dotProduct, Fin.sum_univ_two, h1]
    exact he ▸ hm

theorem card_le_of_natural_borel_invariant [Finite F]
    (W : AddSubgroup (Fin 2 → F)) (hne : W ≠ ⊥)
    (hinv : ∀ g ∈ rankOneBorel F, ∀ v ∈ W, g.val *ᵥ v ∈ W) :
    Nat.card F ≤ Nat.card W := by
  let f : F → W := fun t => ⟨![t, 0], firstLine_mem_of_borel_invariant W hne hinv t⟩
  apply Nat.card_le_card_of_injective f
  intro s t h
  exact congrArg (fun w : W => w.val 0) h

theorem card_le_of_natural_pair_borel_invariant [Finite F]
    (W : AddSubgroup ((Fin 2 → F) × (Fin 2 → F))) (hne : W ≠ ⊥)
    (hinv : ∀ g ∈ (rankOneBorel F).prod (rankOneBorel F), ∀ v ∈ W,
      (g.1.val *ᵥ v.1, g.2.val *ᵥ v.2) ∈ W) : Nat.card F ≤ Nat.card W := by
  let p₁ : ((Fin 2 → F) × (Fin 2 → F)) →+ (Fin 2 → F) := AddMonoidHom.fst _ _
  let p₂ : ((Fin 2 → F) × (Fin 2 → F)) →+ (Fin 2 → F) := AddMonoidHom.snd _ _
  have h₁ : ∀ g ∈ rankOneBorel F, ∀ v ∈ W.map p₁, g.val *ᵥ v ∈ W.map p₁ := by
    intro g hg v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨_, hinv (g, 1) ⟨hg, (rankOneBorel F).one_mem⟩ w hw, rfl⟩
  have h₂ : ∀ g ∈ rankOneBorel F, ∀ v ∈ W.map p₂, g.val *ᵥ v ∈ W.map p₂ := by
    intro g hg v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨_, hinv (1, g) ⟨(rankOneBorel F).one_mem, hg⟩ w hw, rfl⟩
  rcases W.bot_or_exists_ne_zero with h | ⟨w, hw, hw0⟩
  · exact (hne h).elim
  by_cases hfirst : w.1 = 0
  · have hne₂ : W.map p₂ ≠ ⊥ := by
      intro h
      have hm : w.2 ∈ W.map p₂ := ⟨w, hw, rfl⟩
      rw [h, AddSubgroup.mem_bot] at hm
      exact hw0 (Prod.ext hfirst hm)
    exact (card_le_of_natural_borel_invariant (W.map p₂) hne₂ h₂).trans
      (Nat.card_image_le (Set.toFinite _))
  · have hne₁ : W.map p₁ ≠ ⊥ := by
      intro h
      have hm : w.1 ∈ W.map p₁ := ⟨w, hw, rfl⟩
      rw [h, AddSubgroup.mem_bot] at hm
      exact hfirst hm
    exact (card_le_of_natural_borel_invariant (W.map p₁) hne₁ h₁).trans
      (Nat.card_image_le (Set.toFinite _))

end Matrix.SpecialLinearGroup

namespace Matrix.SL2
variable (F : Type*) [Field F]

/-- The two factors act independently on their own natural plane. -/
def naturalPairAction : (SL(2, F) × SL(2, F)) →*
    MulAut (Multiplicative ((Fin 2 → F) × (Fin 2 → F))) where
  toFun g := ((SpecialLinearGroup.toLin' g.1).toAddEquiv.prodCongr
    (SpecialLinearGroup.toLin' g.2).toAddEquiv).toMultiplicative
  map_one' := by
    ext v : 1
    apply Multiplicative.toAdd.injective
    change ((1 : SL(2, F)).val *ᵥ v.toAdd.1,
      (1 : SL(2, F)).val *ᵥ v.toAdd.2) = v.toAdd
    simp
  map_mul' g h := by
    ext v : 1
    apply Multiplicative.toAdd.injective
    change ((g.1 * h.1).val *ᵥ v.toAdd.1, (g.2 * h.2).val *ᵥ v.toAdd.2) =
      (g.1.val *ᵥ (h.1.val *ᵥ v.toAdd.1), g.2.val *ᵥ (h.2.val *ᵥ v.toAdd.2))
    simp [mulVec_mulVec]

theorem naturalPairAction_apply (g : SL(2, F) × SL(2, F))
    (v : Multiplicative ((Fin 2 → F) × (Fin 2 → F))) :
    (naturalPairAction F g v).toAdd = (g.1.val *ᵥ v.toAdd.1, g.2.val *ᵥ v.toAdd.2) := rfl

variable {F}
open SpecialLinearGroup

theorem card_le_of_naturalAction_borel_invariant [Finite F]
    (W : Subgroup (Multiplicative (Fin 2 → F))) (hne : W ≠ ⊥)
    (hinv : ∀ g ∈ rankOneBorel F, ∀ v ∈ W, naturalAction F g v ∈ W) :
    Nat.card F ≤ Nat.card W := by
  apply card_le_of_natural_borel_invariant W.toAddSubgroup'
  · intro h
    apply hne
    simpa using congrArg AddSubgroup.toSubgroup h
  · intro g hg v hv
    exact hinv g hg (Multiplicative.ofAdd v) hv

theorem card_le_of_naturalPairAction_borel_invariant [Finite F]
    (W : Subgroup (Multiplicative ((Fin 2 → F) × (Fin 2 → F)))) (hne : W ≠ ⊥)
    (hinv : ∀ g ∈ (rankOneBorel F).prod (rankOneBorel F), ∀ v ∈ W,
      naturalPairAction F g v ∈ W) : Nat.card F ≤ Nat.card W := by
  apply card_le_of_natural_pair_borel_invariant W.toAddSubgroup'
  · intro h
    apply hne
    simpa using congrArg AddSubgroup.toSubgroup h
  · intro g hg v hv
    exact hinv g hg (Multiplicative.ofAdd v) hv

end Matrix.SL2
