module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.Coordinates
open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification
/-!
# Fixed spaces of the standard Sylow subgroup

The eight words in the two commuting double transpositions and `(0 1)` form
a Sylow two-subgroup of S₄. Its fixed vectors are precisely those fixed by
these three generators. Genuine Sylow conjugacy transports their cardinality
to any supplied Sylow subgroup via the given action. A separate 24-word
normal form identifies full fixed vectors from the three S₄ generators.

These coordinate lemmas support the action classification used for
Huppert–Blackburn, *Finite Groups III*, XII.1.18(b), p.314.
-/
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.NormalizedMatrices
public theorem sylow_fixed_card_eq (β : SymmetricFour →* MulAut BinaryFour)
    (P Q : Sylow 2 SymmetricFour) :
    Nat.card {v : BinaryFour // ∀ s : P, β (s : SymmetricFour) v = v} =
    Nat.card {v : BinaryFour // ∀ s : Q, β (s : SymmetricFour) v = v} := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq SymmetricFour P Q
  apply Nat.card_congr
  apply (β g).toEquiv.subtypeEquiv
  intro v
  have hc (s : P) : β ((P.equivSMul g) s : SymmetricFour) (β g v) =
      β g (β (s : SymmetricFour) v) := by
    change β (g * (s : SymmetricFour) * g⁻¹) (β g v) = _
    simp [map_mul, MulAut.mul_apply]
  constructor
  · intro hv s
    obtain ⟨s, rfl⟩ := (P.equivSMul g).surjective s
    exact (hc s).trans (congrArg (β g) (hv s))
  · intro hv s
    apply (β g).injective
    exact (hc s).symm.trans (hv ((P.equivSMul g) s))
@[expose] public def otherDouble : SymmetricFour := threeCycle * doubleTransposition * threeCycle⁻¹
private def sylowWord (i j k : Fin 2) : SymmetricFour :=
  doubleTransposition ^ i.val * otherDouble ^ j.val * transposition ^ k.val
private def sylowSet (s : SymmetricFour) : Prop := ∃ i j k : Fin 2, s = sylowWord i j k
private instance (s : SymmetricFour) : Decidable (sylowSet s) := inferInstanceAs (Decidable (∃ _ _ _, _))
private def standardGroup : Subgroup SymmetricFour where
  carrier := {s | sylowSet s}
  one_mem' := by decide +kernel
  mul_mem' := by
    have h : ∀ a b, sylowSet a → sylowSet b → sylowSet (a*b) := by decide +kernel
    exact h
  inv_mem' := by
    have h : ∀ a, sylowSet a → sylowSet a⁻¹ := by decide +kernel
    exact h
private theorem standard_card : Nat.card standardGroup = 8 := by
  change Nat.card {s : SymmetricFour // sylowSet s} = 8
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private def standardSylow : Sylow 2 SymmetricFour := Sylow.ofCard standardGroup (by
  rw [standard_card]
  have h : Nat.card SymmetricFour = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [h]
  decide +kernel)
private def actorStabilizer (β : SymmetricFour →* MulAut BinaryFour) (v : BinaryFour) : Subgroup SymmetricFour where
  carrier := {s | β s v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change β (a*b) v = v
    rw [map_mul, MulAut.mul_apply, hb, ha]
  inv_mem' := by
    intro s hs
    change β s⁻¹ v = v
    apply (β s).injective
    simpa using hs.symm
private theorem sylow_fixed_iff (β : SymmetricFour →* MulAut BinaryFour) (v : BinaryFour) :
    (∀ s : standardSylow, β (s : SymmetricFour) v = v) ↔
    β transposition v = v ∧ β doubleTransposition v = v ∧ β otherDouble v = v := by
  constructor
  · intro h
    exact ⟨h ⟨transposition, by change sylowSet transposition; decide +kernel⟩,
      h ⟨doubleTransposition, by change sylowSet doubleTransposition; decide +kernel⟩,
      h ⟨otherDouble, by change sylowSet otherDouble; decide +kernel⟩⟩
  · rintro ⟨ht, hk, hl⟩ s
    obtain ⟨i,j,k,hs⟩ := s.property
    rw [hs]
    let H := actorStabilizer β v
    exact H.mul_mem (H.mul_mem (H.pow_mem hk _) (H.pow_mem hl _)) (H.pow_mem ht _)
private def kleinWord (i : Fin 4) : SymmetricFour :=
  if i = 0 then 1 else if i = 1 then doubleTransposition
  else if i = 2 then otherDouble
  else threeCycle⁻¹ * doubleTransposition * threeCycle
private theorem full_fixed_iff (β : SymmetricFour →* MulAut BinaryFour) (v : BinaryFour) :
    (∀ s : SymmetricFour, β s v = v) ↔
    β threeCycle v = v ∧ β transposition v = v ∧ β doubleTransposition v = v := by
  constructor
  · intro h
    exact ⟨h _, h _, h _⟩
  · rintro ⟨hx,ht,hk⟩ s
    have hwords : ∀ s : SymmetricFour, ∃ (i : Fin 4) (j : Fin 3) (k : Fin 2),
        s = kleinWord i * threeCycle ^ j.val * transposition ^ k.val := by decide +kernel
    obtain ⟨i,j,k,rfl⟩ := hwords s
    let H := actorStabilizer β v
    have hi : kleinWord i ∈ H := by
      unfold kleinWord otherDouble
      split_ifs
      · exact H.one_mem
      · exact hk
      · exact H.mul_mem (H.mul_mem hx hk) (H.inv_mem hx)
      · exact H.mul_mem (H.mul_mem (H.inv_mem hx) hk) hx
    exact H.mul_mem (H.mul_mem hi (H.pow_mem hx _)) (H.pow_mem ht _)
public theorem full_fixed_card (β : SymmetricFour →* MulAut BinaryFour) :
    Nat.card {v : BinaryFour // β threeCycle v = v ∧ β transposition v = v ∧ β doubleTransposition v = v} =
    Nat.card {v : BinaryFour // ∀ s : SymmetricFour, β s v = v} :=
  Nat.card_congr ((Equiv.refl BinaryFour).subtypeEquiv (fun v => (full_fixed_iff β v).symm))
public theorem sylow_fixed_card (β : SymmetricFour →* MulAut BinaryFour) (P : Sylow 2 SymmetricFour) :
    Nat.card {v : BinaryFour // β transposition v = v ∧ β doubleTransposition v = v ∧ β otherDouble v = v} =
    Nat.card {v : BinaryFour // ∀ s : P, β (s : SymmetricFour) v = v} := by
  exact (Nat.card_congr ((Equiv.refl BinaryFour).subtypeEquiv (fun v =>
    (sylow_fixed_iff β v).symm))).trans (sylow_fixed_card_eq β standardSylow P)
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.NormalizedMatrices
