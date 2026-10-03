module

public import Theory.Character.ClassFunction
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Characters of finite permutation actions

The representation on complex-valued functions pulls back by the inverse
permutation. Its trace counts fixed points. Burnside's orbit-counting formula
then identifies the principal multiplicity and the character norm with the
numbers of orbits on points and ordered pairs, respectively.

Source: ordinary permutation character theory; the rank-two criterion is used
in Wong (1964), printed p.110.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace Representation

variable (G X : Type*) [Group G] [MulAction G X]

/-- The complex permutation representation on functions on the acted-on set. -/
def permutationAction : Representation ℂ G (X → ℂ) where
  toFun g :=
    { toFun := fun f x => f (g⁻¹ • x)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

@[simp] theorem permutationAction_apply (g : G) (f : X → ℂ) (x : X) :
    permutationAction G X g f x = f (g⁻¹ • x) := rfl

variable [Finite X]
attribute [local instance] Fintype.ofFinite

/-- The permutation character counts the points fixed by the given element. -/
theorem permutationAction_character (g : G) :
    (permutationAction G X).character g = (Nat.card (MulAction.fixedBy X g) : ℂ) := by
  classical
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ X)]
  change (∑ x : X, (Pi.single x 1 : X → ℂ) (g⁻¹ • x)) = _
  have heq (x : X) : (g⁻¹ • x = x) ↔ (g • x = x) := by
    constructor <;> intro h
    · simpa using (congrArg (g • ·) h).symm
    · simpa using (congrArg (g⁻¹ • ·) h).symm
  simp [Pi.single_apply, heq, Nat.card_eq_fintype_card, Fintype.card_subtype, MulAction.fixedBy]

/-- The function-space permutation character is a genuine finite-dimensional character. -/
theorem permutationAction_isCharacter : IsCharacter (permutationAction G X).character := by
  let e := (Module.finBasis ℂ (X → ℂ)).equivFun
  let σ : Representation ℂ G (Fin (Module.finrank ℂ (X → ℂ)) → ℂ) :=
    { toFun := fun g => e.conj (permutationAction G X g)
      map_one' := by ext f; simp [LinearEquiv.conj_apply]
      map_mul' := by intros; ext f; simp [LinearEquiv.conj_apply, map_mul] }
  refine ⟨_, σ, ?_⟩
  funext g
  exact (LinearMap.trace_conj' (permutationAction G X g) e).symm

variable [Fintype G]

/-- Burnside's lemma expresses the principal multiplicity as the orbit count. -/
theorem permutationAction_scalarProduct_one :
    scalarProduct G (permutationAction G X).character 1 =
      (Nat.card (MulAction.orbitRel.Quotient G X) : ℂ) := by
  classical
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have hc : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  unfold scalarProduct
  simp only [permutationAction_character, Pi.one_apply, star_one, mul_one]
  rw [show (∑ g : G, (Nat.card (MulAction.fixedBy X g) : ℂ)) =
      (Nat.card (MulAction.orbitRel.Quotient G X) : ℂ) * Nat.card G by
    simpa only [Nat.card_eq_fintype_card] using (show
      (∑ g : G, (Fintype.card (MulAction.fixedBy X g) : ℂ)) =
        (Fintype.card (MulAction.orbitRel.Quotient G X) : ℂ) * Fintype.card G by
      exact_mod_cast h)]
  field_simp

/-- A nonempty transitive permutation character contains the principal character once. -/
theorem permutationAction_scalarProduct_one_of_pretransitive
    [Nonempty X] [MulAction.IsPretransitive G X] :
    scalarProduct G (permutationAction G X).character 1 = 1 := by
  rw [permutationAction_scalarProduct_one]
  have : Subsingleton (MulAction.orbitRel.Quotient G X) :=
    (MulAction.pretransitive_iff_subsingleton_quotient G X).mp inferInstance
  have hcard : Nat.card (MulAction.orbitRel.Quotient G X) = 1 :=
    Nat.card_eq_one_iff_unique.mpr
      ⟨this, ⟨Quotient.mk'' (Classical.choice (inferInstance : Nonempty X))⟩⟩
  rw [hcard]
  norm_num

/-- The norm of a permutation character is the number of orbits on ordered pairs. -/
theorem permutationAction_scalarProduct_self :
    scalarProduct G (permutationAction G X).character (permutationAction G X).character =
      (Nat.card (MulAction.orbitRel.Quotient G (X × X)) : ℂ) := by
  classical
  have hcard (g : G) : Nat.card (MulAction.fixedBy (X × X) g) =
      Nat.card (MulAction.fixedBy X g) * Nat.card (MulAction.fixedBy X g) := by
    rw [← Nat.card_prod]
    apply Nat.card_congr
    exact {
      toFun := fun p => ⟨⟨p.1.1, congrArg Prod.fst p.2⟩,
        ⟨p.1.2, congrArg Prod.snd p.2⟩⟩
      invFun := fun p => ⟨(p.1.1, p.2.1), Prod.ext p.1.2 p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← permutationAction_scalarProduct_one G (X × X)]
  unfold scalarProduct
  simp only [permutationAction_character, star_natCast, Pi.one_apply, star_one,
    mul_one, hcard, Nat.cast_mul]

/-- A permutation character of norm two gives a doubly pretransitive action. -/
theorem permutationAction_two_pretransitive_of_norm_two
    (h : scalarProduct G (permutationAction G X).character
      (permutationAction G X).character = 2) :
    MulAction.IsMultiplyPretransitive G X 2 := by
  rw [permutationAction_scalarProduct_self] at h
  have hc : Nat.card (MulAction.orbitRel.Quotient G (X × X)) = 2 := by
    exact_mod_cast h
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  let q : X × X → MulAction.orbitRel.Quotient G (X × X) := Quotient.mk''
  have hne (x y : X) (hxy : x ≠ y) : q (x, y) ≠ q (a, a) := by
    intro heq
    obtain ⟨g, hg⟩ := Quotient.exact heq
    have h1 := congrArg Prod.fst hg
    have h2 := congrArg Prod.snd hg
    exact hxy (h1.symm.trans h2)
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (q (a, a))).mp hc
  have heq : q (c, d) = q (a, b) :=
    (hz _ (hne c d hcd)).trans (hz _ (hne a b hab)).symm
  obtain ⟨g, hg⟩ := Quotient.exact heq
  exact ⟨g, congrArg Prod.fst hg, congrArg Prod.snd hg⟩

end Representation
