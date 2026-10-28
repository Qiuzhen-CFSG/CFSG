module

public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Disjoint irreducible images and the noninvariant diagonal

Distinct members of `Irr⁺(X,V)` have disjoint images in the literal quotient
`V / C_V(X)`. For an invariant subspace J, irreducibility first gives either
I ≤ J or I ∩ (J + C_V(X)) ≤ C_V(X). In the first branch, taking commutators
removes the fixed summand; the antichain theorem then separates distinct
members.

If A fixes a diagonal and X preserves it, the commutator group [X,A] fixes it.
Thus when [X,A] = X, a diagonal between distinct Irr⁺ members cannot be
X-invariant: its two images in the quotient would coincide, contradicting
disjointness. An additional linear lemma shows that an operator commuting
with X and trivial modulo C_V(X) fixes [V,X]. These are geometric steps of B.7.2, not the full
invariance theorem; the conjugate's membership in Irr⁺ remains explicit.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.7.2, printed p. 119 (PDF p. 130).
-/

@[expose] public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

set_option backward.isDefEq.respectTransparency false in
/-- Irreducibility separates an invariant subspace from I, up to fixed vectors. -/
theorem IsIrrPlus.le_or_inf_sup_fixedSpace_le {X : Subgroup G} {I J : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) (hJ : X ≤ subspaceStabilizer ρ J) :
    I ≤ J ∨ I ⊓ (J ⊔ fixedSpace ρ X) ≤ fixedSpace ρ X := by
  obtain ⟨hsI, hcI, hiI⟩ := hI
  let S : Subrepresentation (invariantSubspace ρ X I hsI).toRepresentation :=
    ⟨(J ⊔ fixedSpace ρ X).comap I.subtype, by
      intro x v hv
      obtain ⟨j, hj, z, hz, he⟩ := Submodule.mem_sup.mp hv
      change ρ x (v : V) ∈ J ⊔ fixedSpace ρ X
      change j + z = (v : V) at he
      have hzx : ρ x z = z := hz x
      rw [← he, map_add, hzx]
      exact Submodule.mem_sup.mpr ⟨ρ x j, (hJ x.property j).2 hj, z, hz, rfl⟩⟩
  let C := centralSubspace ρ X I hsI
  let : IsIrreducible C.quotientRepresentation := hiI
  rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient C S with h | h
  · right
    intro v hv
    exact h (show (⟨v, hv.1⟩ : I) ∈ S from hv.2)
  · left
    rw [← hcI]
    apply subspaceCommutator_le_of_le_sup_fixedSpace ρ hJ
    intro v hv
    have hm : (⟨v, hv⟩ : I) ∈ C.toSubmodule ⊔ S.toSubmodule := by rw [h]; trivial
    obtain ⟨c, hc, j, hj, he⟩ := Submodule.mem_sup.mp hm
    have hc' : (c : V) ∈ J ⊔ fixedSpace ρ X := Submodule.mem_sup_right hc
    have hj' : (j : V) ∈ J ⊔ fixedSpace ρ X := hj
    have he' := congrArg (fun i : I => (i : V)) he
    change (c : V) + (j : V) = v at he'
    exact he' ▸ (J ⊔ fixedSpace ρ X).add_mem hc' hj'

/-- Distinct Irr⁺ members have disjoint images modulo the fixed space. -/
theorem IsIrrPlus.disjoint_quotientImages {X : Subgroup G} {I J : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) (hJ : IsIrrPlus ρ X J) (hne : I ≠ J) :
    Disjoint (I.map (fixedSpace ρ X).mkQ) (J.map (fixedSpace ρ X).mkQ) := by
  have hle : I ⊓ (J ⊔ fixedSpace ρ X) ≤ fixedSpace ρ X :=
    (IsIrrPlus.le_or_inf_sup_fixedSpace_le ρ hI hJ.choose).resolve_left
      (fun h => hne (hI.eq_of_le ρ hJ h))
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro q hq
  obtain ⟨i, hi, rfl⟩ := hq.1
  obtain ⟨j, hj, heq⟩ := hq.2
  have hdiff : i - j ∈ fixedSpace ρ X := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (fixedSpace ρ X).mkQ (i - j) = 0
    rw [map_sub, heq, sub_self]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply hle
  refine ⟨hi, Submodule.mem_sup.mpr ⟨j, hj, i - j, hdiff, ?_⟩⟩
  abel
end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
open scoped commutatorElement

/-- If X preserves D and A fixes D, then [X,A] fixes D. -/
theorem le_fixedSpace_commutator_of_invariant {X A : Subgroup G} {D : Submodule (ZMod 2) V}
    (hX : X ≤ subspaceStabilizer ρ D) (hA : D ≤ fixedSpace ρ A) :
    D ≤ fixedSpace ρ ⁅X, A⁆ := by
  have hker : ⁅X, A⁆ ≤ subspaceKernel ρ D ⊤ := by
    apply Subgroup.commutator_le.mpr
    intro x hx a ha
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    have haiv : ρ a⁻¹ v = v := hA hv ⟨a⁻¹, A.inv_mem ha⟩
    have hxiv : ρ x⁻¹ v ∈ D := (hX (X.inv_mem hx) v).2 hv
    have haxiv : ρ a (ρ x⁻¹ v) = ρ x⁻¹ v := hA hxiv ⟨a, ha⟩
    simp only [commutatorElement_def, map_mul, Module.End.mul_apply, haiv, haxiv]
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Module.End.one_apply]
  intro v hv x
  exact (hker x.property).2 v hv

/-- The subspace of action differences on I. -/
def diagonalSubspace (I : Submodule (ZMod 2) V) (a : G) : Submodule (ZMod 2) V :=
  I.map (ρ a - LinearMap.id)

/-- Pointwise fixation of all a-differences fixes the diagonal on any subspace. -/
theorem diagonalSubspace_le_fixedSpace {A : Subgroup G} {I : Submodule (ZMod 2) V} {a : G}
    (ha : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v) :
    diagonalSubspace ρ I a ≤ fixedSpace ρ A := by
  rintro _ ⟨i, hi, rfl⟩ b
  exact ha b b.property i

/-- The diagonal between distinct Irr⁺ members is not invariant under X. -/
theorem IsIrrPlus.diagonal_not_invariant {X A : Subgroup G} {I : Submodule (ZMod 2) V} {a : G}
    (hI : IsIrrPlus ρ X I) (hIa : IsIrrPlus ρ X (I.map (ρ a)))
    (hne : I ≠ I.map (ρ a)) (hXA : ⁅X, A⁆ = X)
    (ha : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v) :
    ¬ X ≤ subspaceStabilizer ρ (diagonalSubspace ρ I a) := by
  intro hstab
  have hfix : diagonalSubspace ρ I a ≤ fixedSpace ρ X := by
    rw [← hXA]
    exact le_fixedSpace_commutator_of_invariant ρ hstab (diagonalSubspace_le_fixedSpace ρ ha)
  have hdis := IsIrrPlus.disjoint_quotientImages ρ hI hIa hne
  apply hI.not_le_fixedSpace ρ
  intro i hi
  have hd : ρ a i - i ∈ fixedSpace ρ X := hfix ⟨i, hi, rfl⟩
  have he : (fixedSpace ρ X).mkQ (ρ a i) = (fixedSpace ρ X).mkQ i := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hd
  apply (Submodule.Quotient.mk_eq_zero _).mp
  have hm : (fixedSpace ρ X).mkQ i ∈
      I.map (fixedSpace ρ X).mkQ ⊓ (I.map (ρ a)).map (fixedSpace ρ X).mkQ :=
    ⟨⟨i, hi, rfl⟩, ⟨ρ a i, ⟨i, hi, rfl⟩, he⟩⟩
  rwa [hdis.eq_bot] at hm
end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- An operator commuting with X and acting trivially modulo C_V(X) fixes
[V,X]. This closes the linear part of the stabilizer argument. -/
theorem fixes_commutatorSubspace_of_commutes_of_displacement_fixed {X : Subgroup G} {b : G}
    (hc : ∀ x ∈ X, Commute b x)
    (hd : ∀ v : V, ρ b v - v ∈ fixedSpace ρ X)
    (v : V) (hv : v ∈ subspaceCommutator ρ ⊤ X) : ρ b v = v := by
  have hle : subspaceCommutator ρ ⊤ X ≤ LinearMap.ker (ρ b - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, w, _, rfl⟩
    change ρ b (ρ x w - w) - (ρ x w - w) = 0
    apply sub_eq_zero.mpr
    have hbc : ρ b (ρ x w) = ρ x (ρ b w) := by
      change (ρ b * ρ x) w = (ρ x * ρ b) w
      rw [← map_mul, ← map_mul, (hc x hx).eq]
    have hdx : ρ x (ρ b w - w) = ρ b w - w := hd w ⟨x, hx⟩
    rw [map_sub] at hdx ⊢
    rw [hbc]
    exact (sub_eq_sub_iff_sub_eq_sub).mp hdx
  exact sub_eq_zero.mp (hle hv)
end Representation.BinaryOffender
