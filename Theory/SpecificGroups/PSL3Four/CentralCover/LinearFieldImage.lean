module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FieldType
public import Theory.SpecificGroups.PSL3Four.FieldExtension.SemilinearInclusion
import all Theory.SpecificGroups.PSL3Four.OuterPlane.FieldOccurrence
import all Theory.SpecificGroups.PSL3.ExtensionBorel

/-! The whole linear-field actor group has the expected size bound, and
preservation of an actual elementary sixty-four in a four-cover forces
linear-field descent for every actor, without an order restriction. -/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Four

/-- A preserved elementary sixty-four descends to an actual root plane,
so the induced projective automorphism preserves parabolic type. -/
theorem FourCover.stabilizes_sixtyfour_linearField
    {E : Type*} [Group E] [Finite E] (c : FourCover E)
    (Q : Subgroup E) [IsElementaryAbelian 2 Q]
    (hZQ : center E ≤ Q) (hQ : Nat.card Q = 64)
    (a : MulAut E) (ha : Q.map a.toMonoidHom = Q) :
    c.toCover.autMap c.ker_eq_center a ∈ PSL3.ExtensionBorel.linearField F := by
  let f := c.toMonoidHom
  let b := c.toCover.autMap c.ker_eq_center a
  let R := Q.map f
  let := c.center_isKleinFour
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.map _
  have hR : Nat.card R = 16 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map Q f
    rw [inf_eq_right.mpr (c.ker_eq_center ▸ hZQ), c.ker_eq_center,
      IsKleinFour.card_four, hQ] at hh
    change 4 * Nat.card R = 64 at hh
    omega
  apply stabilizes_elementary_sixteen_linearField R hR b
  calc
    _ = (Q.map a.toMonoidHom).map f := by
      change (Q.map f).map b.toMonoidHom = _
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      exact c.toCover.autMap_apply c.ker_eq_center a x
    _ = R := by rw [ha]

/-- The actual linear-field automorphism subgroup is covered by its two
linear cosets, each of cardinality 60480. -/
theorem linearField_card_le : Nat.card (PSL3.ExtensionBorel.linearField F) ≤ 120960 := by
  let D := PSL3.OuterSolvable.innerDiagonal F
  let A := PSL3.ExtensionBorel.linearField F
  have hd : Nat.card D = 60480 :=
    (Nat.card_congr OuterThreeStructure.pglEquiv.symm.toEquiv).trans card_PGL
  have hf : pslFrobenius ∈ A := by
    rw [OuterPlane.FieldOccurrence.frobenius_eq_fieldAction]
    exact (show (PSL3.OuterSolvable.fieldAction F).range ≤ A from le_sup_right) ⟨_,rfl⟩
  let f : D × Bool → A := fun x =>
    ⟨x.1 * (if x.2 then pslFrobenius else 1),
      A.mul_mem ((show D ≤ A from le_sup_left) x.1.property)
        (by split <;> first | exact hf | exact A.one_mem)⟩
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨g,σ,hg⟩ := PSL3.ExtensionBorel.linearField_factorization F a a.property
    rcases OuterPlane.FieldOccurrence.coefficient_eq_one_or_frobenius σ with hσ | hσ
    · refine ⟨(⟨_,⟨g,rfl⟩⟩,false), Subtype.ext ?_⟩
      change PSL3.OuterSolvable.linearConj F g * 1 = (a : MulAut PSL)
      simpa only [hσ, map_one] using hg.symm
    · refine ⟨(⟨_,⟨g,rfl⟩⟩,true), Subtype.ext ?_⟩
      change PSL3.OuterSolvable.linearConj F g * pslFrobenius = (a : MulAut PSL)
      simpa only [hσ, ← OuterPlane.FieldOccurrence.frobenius_eq_fieldAction] using hg.symm
  have hh := Nat.card_le_card_of_surjective f hs
  rw [Nat.card_prod, hd] at hh
  simpa using hh

end Matrix.PSL3Four
