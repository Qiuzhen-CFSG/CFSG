module

public import Theory.GroupAction.FourPointSylowFixed
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A normal cubic line detected by a Sylow subgroup

The elementary nine-group has four cubic subgroups, counted by its ternary
projective line. An actual automorphism action on those subgroups preserves
their cardinality. A Sylow-fixed cubic subgroup therefore gives a globally
fixed cubic subgroup by the four-point orbit argument. Applying this to the
literal conjugation action on a normal elementary three-subgroup gives a
normal cubic subgroup of the original ambient group.

Source: Aschbacher--Smith 15.4.9, printed p.1159. Neither irreducibility
classification nor faithful action is assumed.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise LinearAlgebra.Projectivization
namespace IsElementaryAbelian.TernarySylowLine
variable {E D : Type*} [Group E] [Group D] [Finite E] [Finite D]
  [IsElementaryAbelian 3 E]

private noncomputable def subspaceEquiv : Subgroup E ≃o Submodule (ZMod 3) (Additive E) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 3)

private theorem card_iff (L : Subgroup E) :
    Nat.card L = 3 ↔ Module.finrank (ZMod 3) (subspaceEquiv L) = 1 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := subspaceEquiv L)
  change Nat.card L = _ at hc
  rw [Nat.card_zmod] at hc
  rw [hc]
  exact (Nat.pow_right_injective (by decide : 2 ≤ 3)).eq_iff (a := _) (b := 1)

/-- The actual elementary nine-group has four subgroups of order three. -/
theorem card_cubic_subgroups (hE : Nat.card E = 9) :
    Nat.card {L : Subgroup E // Nat.card L = 3} = 4 := by
  let e := (Equiv.subtypeEquiv subspaceEquiv.toEquiv (card_iff (E := E))).trans
    (Projectivization.equivSubmodule (ZMod 3) (Additive E)).symm
  have hc := Projectivization.card' (ZMod 3) (Additive E)
  change Nat.card E = _ at hc
  rw [hE, Nat.card_zmod, ← Nat.card_congr e] at hc
  omega

@[instance_reducible] private def cubicAction (ρ : D →* MulAut E) :
    MulAction D {L : Subgroup E // Nat.card L = 3} where
  smul d L := ⟨L.val.map (ρ d).toMonoidHom,
    (Subgroup.card_map_of_injective (ρ d).injective).trans L.property⟩
  one_smul L := by
    apply Subtype.ext
    change L.val.map (ρ 1).toMonoidHom = L.val
    rw [show (ρ 1).toMonoidHom = MonoidHom.id E from MonoidHom.ext (fun x => by simp),
      Subgroup.map_id]
  mul_smul d e L := by
    apply Subtype.ext
    change L.val.map (ρ (d * e)).toMonoidHom =
      (L.val.map (ρ e).toMonoidHom).map (ρ d).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [map_mul, MulAut.mul_apply]

/-- A Sylow-invariant cubic subgroup gives an invariant cubic subgroup for
the entire specified automorphism action. The action need not be faithful. -/
theorem exists_invariant_cubic (ρ : D →* MulAut E) (hE : Nat.card E = 9)
    (S : Sylow 2 D) (L : Subgroup E) (hL : Nat.card L = 3)
    (hSL : ∀ d ∈ (S : Subgroup D), L.map (ρ d).toMonoidHom = L) :
    ∃ A : Subgroup E, Nat.card A = 3 ∧ ∀ d : D, A.map (ρ d).toMonoidHom = A := by
  let := cubicAction ρ
  obtain ⟨A, hA⟩ := MulAction.exists_fixed_of_card_four_of_sylow_fixed
    (card_cubic_subgroups hE) S (⟨L, hL⟩ : {L : Subgroup E // Nat.card L = 3})
    (fun d hd => Subtype.ext (hSL d hd))
  exact ⟨A.val, A.property, fun d => congrArg Subtype.val (hA d)⟩

end IsElementaryAbelian.TernarySylowLine

namespace Subgroup
variable {Q : Type*} [Group Q] [Finite Q]

/-- A normal elementary three-subgroup of order three or nine contains an
actual ambient-normal cubic subgroup if a Sylow two-subgroup preserves one. -/
theorem exists_normal_cubic_le_of_sylow_invariant
    (P : Subgroup Q) [P.Normal] [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 3 ∨ Nat.card P = 9)
    (S : Sylow 2 Q) (B : Subgroup Q) (hBP : B ≤ P) (hB : Nat.card B = 3)
    (hSB : (S : Subgroup Q) ≤ normalizer (B : Set Q)) :
    ∃ A : Subgroup Q, A ≤ P ∧ A.Normal ∧ Nat.card A = 3 := by
  rcases hP with hP | hP
  · exact ⟨P, le_rfl, inferInstance, hP⟩
  let ρ : Q →* MulAut P := MulAut.conjNormal
  let L := B.subgroupOf P
  have hL : Nat.card L = 3 := (Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv).trans hB
  have hcompat (g : Q) : P.subtype.comp (ρ g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp P.subtype := by ext x; rfl
  have hSL : ∀ g ∈ (S : Subgroup Q), L.map (ρ g).toMonoidHom = L := by
    intro g hg
    apply map_injective P.subtype_injective
    rw [map_map, hcompat, ← map_map]
    change ((B.subgroupOf P).map P.subtype).map (MulAut.conj g).toMonoidHom =
      (B.subgroupOf P).map P.subtype
    rw [map_subgroupOf_eq_of_le hBP]
    exact mem_normalizer_iff_map_conj_eq.mp (hSB hg)
  obtain ⟨A, hA, hfix⟩ := IsElementaryAbelian.TernarySylowLine.exists_invariant_cubic
    ρ hP S L hL hSL
  refine ⟨A.map P.subtype, map_subtype_le _, ?_,
    (card_map_of_injective P.subtype_injective).trans hA⟩
  refine ⟨?_⟩
  intro x hx g
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨ρ g a, ?_, rfl⟩
  have h := mem_map_of_mem (ρ g).toMonoidHom ha
  rwa [hfix g] at h

end Subgroup
