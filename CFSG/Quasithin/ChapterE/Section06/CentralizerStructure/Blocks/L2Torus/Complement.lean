module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Diagonal
public import Theory.GroupTheory.OddSubgroupLift

/-!
# A compatible diagonal section for an even rank-one block

The diagonal image of Fˣ has odd order. Its inverse image under the marked
quotient map has a normal two-group kernel, so Schur–Zassenhaus gives a
complement on which that map is injective and has exactly the diagonal image.
Inverting this restricted map constructs a homomorphism Fˣ → L lifting each
specified diagonal matrix, hence a `DiagonalSection`.

The cyclicity, order and Borel factorization of its range are already proved
in `Diagonal`. No assertion about the block-center module is used here.

Source: Aschbacher–Smith, E.6.7, printed p.246, the construction of Xᵢ in
the L₂(2ⁿ)-block case. The Schur–Zassenhaus step is supplied by
`MonoidHom.exists_odd_subgroup_lift`.
-/

namespace CFSG.Quasithin.ChapterE.Section06.L2Torus

open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable {L : Type*} [Group L] [Finite L]
  {F : Type*} [Field F] [Finite F] [CharP F 2] {B : Subgroup L}

/-- The marked quotient map admits a homomorphic lift of the diagonal torus. -/
public theorem exists_diagonalSection (a : MarkedBlockModel L B F) :
    Nonempty (DiagonalSection a) := by
  classical
  let := Fintype.ofFinite F
  let δ : Fˣ →* SL(2, F) := (rankOneBorel F).subtype.comp borelDiagonalHom
  have heven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
  have hodd : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units]
    exact Nat.Even.sub_odd (Nat.card_pos (α := F)) heven odd_one
  have hδodd : Odd (Nat.card δ.range) := hodd.of_dvd_nat (card_range_dvd δ)
  have hker : IsPGroup 2 a.linearMap.ker := by
    rw [a.linearMap_ker]
    exact pCore_isPGroup
  obtain ⟨D, hD, hinj, _, _⟩ := a.linearMap.exists_odd_subgroup_lift
    a.linearMap_surjective hker δ.range hδodd
  let q : D →* δ.range := (a.linearMap.comp D.subtype).codRestrict δ.range (by
    intro x
    rw [← hD]
    exact ⟨x, x.property, rfl⟩)
  have hq : Function.Bijective q := by
    constructor
    · intro x y h
      exact hinj (congrArg Subtype.val h)
    · intro y
      have hy : (y : SL(2, F)) ∈ D.map a.linearMap := hD.symm ▸ y.property
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : D ≃* δ.range := MulEquiv.ofBijective q hq
  refine ⟨⟨D.subtype.comp (e.symm.toMonoidHom.comp δ.rangeRestrict), ?_⟩⟩
  intro u
  exact congrArg Subtype.val (e.apply_symm_apply (δ.rangeRestrict u))

end CFSG.Quasithin.ChapterE.Section06.L2Torus
