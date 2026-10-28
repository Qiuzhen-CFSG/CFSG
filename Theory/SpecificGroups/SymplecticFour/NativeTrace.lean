module
public import Theory.SpecificGroups.SymplecticFour.PRegularClasses
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.TracePowers
public import Theory.Representation.PRegularTrace
public import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Polynomial.Splits
public import Theory.GroupTheory.NormalizingInvolutionSquares

/-!
# Trace-field bounds for actual symplectic four-space carriers

Every representation of Sp₄(K) in characteristic two has traces fixed by
raising to |K|. For odd-order elements, the finite-field characteristic
polynomial identity and intrinsic symplectic conjugacy identify the |K|-th
power with the original conjugacy class. Modular character values reduce
all remaining elements to odd order. A polynomial-root argument then puts
these traces in every ambient subfield of cardinality |K|.

For the actual extension N⟨t⟩ by a normalizing involution, every element
has square in N. Squaring commutes with trace, and perfectness of the finite
coefficient subfield extends the same trace bound to the whole extension.
The literal subgroup consumer supplies the input to symplectic trace-field
descent in Aschbacher--Smith G.4.1 and G.4.8, printed pp.340--342.
-/

public noncomputable section
set_option linter.style.haveILetI false
namespace Theory.SpecificGroups.SymplecticFour.NativeTrace
variable {K F V : Type*} [Field K] [Finite K] [CharP K 2]
  [Field F] [CharP F 2] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Odd-order classes of the actual matrix group are fixed by the field-cardinality power. -/
theorem isConj_pow_card_of_odd (g : Sp K) (hg : ¬2∣orderOf g) :
    IsConj (g^(Nat.card K)) g := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  apply PRegularClasses.isConj_of_charpoly_eq
  · intro h
    exact hg (h.trans (orderOf_pow_dvd _))
  · exact hg
  · have hh := FiniteField.Matrix.charpoly_pow_card g.val
    simpa only [Nat.card_eq_fintype_card, ←SubmonoidClass.coe_pow] using hh

/-- Odd-order character values are fixed by the model-field Frobenius. -/
theorem character_pow_card_of_odd {k : ℕ} (hK : Nat.card K=2^k)
    (ρ : Representation F (Sp K) V) (g : Sp K) (hg : ¬2∣orderOf g) :
    ρ.character g ^ Nat.card K = ρ.character g := by
  have hc := isConj_pow_card_of_odd g hg
  obtain ⟨c,hc⟩ := isConj_iff.mp hc
  have ht : ρ.character (g^Nat.card K)=ρ.character g := by
    calc
      ρ.character (g^Nat.card K) = ρ.character (c*(g^Nat.card K)*c⁻¹) :=
        (Representation.char_conj ρ (g^Nat.card K) c).symm
      _ = ρ.character g := congrArg ρ.character hc
  rw [hK, Representation.character_two_pow_charTwo] at ht
  rwa [hK]

/-- All character values are fixed by the model-field Frobenius. -/
theorem character_pow_card {k : ℕ} (hK : Nat.card K=2^k)
    (ρ : Representation F (Sp K) V) (g : Sp K) :
    ρ.character g ^ Nat.card K = ρ.character g := by
  obtain ⟨h,hh,hchar⟩ := Representation.exists_pRegular_same_character
    (F := F) 2 g
  rw [hchar V ρ]
  exact character_pow_card_of_odd hK ρ h hh

omit [CharP F 2] in
/-- The roots of X^|L|−X in an extension field are precisely the elements of L. -/
theorem mem_subfield_of_pow_card (L : Subfield F) [Finite L] {x : F}
    (hx : x ^ Nat.card L=x) : x∈L := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  apply Polynomial.Splits.mem_subfield_of_isRoot L
    (f := Polynomial.X^Fintype.card L-Polynomial.X)
  · simpa only [Nat.card_eq_fintype_card] using Polynomial.splits_X_pow_nat_card_sub_X (K := L)
  · exact FiniteField.X_pow_card_sub_X_ne_zero _ (Fintype.one_lt_card)
  · simpa [Polynomial.IsRoot.def, Nat.card_eq_fintype_card, sub_eq_zero] using hx
end Theory.SpecificGroups.SymplecticFour.NativeTrace

namespace Theory.SpecificGroups.SymplecticFour.NativeTrace
variable {F K G V : Type*} [Field F] [CharP F 2]
  [Field K] [Finite K] [CharP K 2] [Group G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- An actual symplectic carrier puts every restricted trace in the model subfield. -/
theorem subgroup_character_mem {k : ℕ} (hK : Nat.card K=2^k)
    (N : Subgroup G) (e : N ≃* Sp K) (ρ : Representation F G V)
    (L : Subfield F) [Finite L] (hL : Nat.card L=Nat.card K) (x : N) :
    ρ.character x.val∈L := by
  apply mem_subfield_of_pow_card L
  rw [hL]
  let σ := ρ.comp (N.subtype.comp e.symm.toMonoidHom)
  have ht := character_pow_card hK σ (e x)
  simpa only [σ, Representation.character, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, Subgroup.subtype_apply] using ht

/-- A square lying in the given actor suffices to descend its trace. -/
theorem character_mem_of_square_mem (ρ : Representation F G V)
    (L : Subfield F) [Finite L] (N : Subgroup G)
    (htrace : ∀x:N, ρ.character x.val∈L) (x : G) (hx : x^2∈N) :
    ρ.character x∈L := by
  have ht : ρ.character x ^ 2∈L := by
    rw [←Representation.character_sq_charTwo]
    exact htrace ⟨x^2,hx⟩
  obtain ⟨a,ha⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := L))
    (⟨ρ.character x ^ 2,ht⟩:L)
  have he : (a:F)^2=ρ.character x^2 := congrArg (fun z:L => (z:F)) ha
  exact (CharTwo.sq_injective he) ▸ a.property
end Theory.SpecificGroups.SymplecticFour.NativeTrace


namespace Theory.SpecificGroups.SymplecticFour.NativeTrace
variable {F K : Type*} [Field F] [CharP F 2]
  [Field K] [Finite K] [CharP K 2]

/-- The literal normalized involutory extension has traces in the same model field. -/
theorem join_character_mem {k : ℕ} (hK : Nat.card K=2^k)
    (N : Subgroup (Sp F)) (e : N ≃* Sp K)
    (L : Subfield F) [Finite L] (hL : Nat.card L=Nat.card K)
    (t : Sp F) (ht : t^2=1) (hn : t∈Subgroup.normalizer (N:Set (Sp F)))
    (x : ↥(N⊔Subgroup.zpowers t)) :
    Representation.character ((Representation.symplecticNatural 2).comp
      (N⊔Subgroup.zpowers t).subtype) x∈L := by
  let ρ := Representation.symplecticNatural (k := F) 2
  change ρ.character x.val∈L
  apply character_mem_of_square_mem ρ L N
  · intro n
    exact subgroup_character_mem hK N e ρ L hL n
  · exact Subgroup.square_mem_of_mem_sup_zpowers_involution N t ht hn x.property
end Theory.SpecificGroups.SymplecticFour.NativeTrace
