module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.Stabilizer
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.BinaryOrders

/-!
# The binary short-root centralizer quotient

The literal short-root centralizer has order 96. Its central short-root
line has order two, while the invariant symmetric-matrix subgroup has
order eight. The actual quotient by the marked central line therefore
has order 48 and contains a normal elementary four-group.

These are the original marked local data used by I.8.5 in the binary
unitary branch of Aschbacher–Smith F.4.42, printed pp.295–296.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.ShortRoot
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => L2Matrix 1 hn
local notation "X" => shortCentralizer F σ hσ
local notation "V" => orthogonalRadical F σ hσ
local notation "t" => shortLocal F σ hσ

theorem centralizer_card : Nat.card X = 96 := by
  rw [shortCentralizer_card, Atlas.card_sl_two]
  have hf : Nat.card (FixedBy.subfield F σ) = 2 := PointLocal.fixedField_card 1 hn
  have hq : Nat.card (radical F σ hσ) = 16 := L2MatrixRadical_card 1 hn
  rw [hf,hq]
  norm_num

theorem orthogonal_card : Nat.card V = 8 := by
  rw [orthogonalRadical_card]
  have hf : Nat.card (FixedBy.subfield F σ) = 2 := PointLocal.fixedField_card 1 hn
  rw [hf]
  norm_num

/-- The central short-root involution as an element of its own centralizer. -/
def mark : X := ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩

theorem mark_order : orderOf mark = 2 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    exact congrArg (fun q : radical F σ hσ => q.val) (radical_sq F σ hσ
      (radicalEquiv F σ hσ (Multiplicative.ofAdd (shortParameter F σ))))
  · intro he
    have h := congrArg (fun g : X => g.val.val.val.val 0 2) he
    exact one_ne_zero h

theorem mark_central : mark ∈ center X := by
  apply mem_center_iff.mpr
  intro g
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp g.property

def centralLine : Subgroup X := zpowers mark

instance centralLine_normal : centralLine.Normal := by
  constructor
  intro n hx g
  have hc : n ∈ center X := (zpowers_le.mpr mark_central) hx
  have he : g * n * g⁻¹ = n := by
    rw [mem_center_iff.mp hc g, mul_inv_cancel_right]
  rw [he]
  exact hx

theorem centralLine_card : Nat.card centralLine = 2 :=
  (Nat.card_zpowers mark).trans mark_order

theorem centralizer_quotient_card : Nat.card (X ⧸ centralLine) = 48 := by
  have h := centralLine.card_mul_index
  rw [centralLine_card, centralizer_card, index_eq_card] at h
  omega

def orthogonalInCentralizer : Subgroup X := (V).subgroupOf X

instance orthogonal_elementary : IsElementaryAbelian 2 orthogonalInCentralizer := by
  let f : orthogonalInCentralizer →* radical F σ hσ :=
    ((X).subtype.comp orthogonalInCentralizer.subtype).codRestrict _
      (fun x => orthogonalRadical_le_radical F σ hσ x.property)
  exact IsElementaryAbelian.of_injective f (by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : radical F σ hσ => q.val) he)

theorem orthogonal_in_card : Nat.card orthogonalInCentralizer = 8 :=
  (Nat.card_congr (subgroupOfEquivOfLe (orthogonalRadical_le_shortCentralizer F σ hσ)).toEquiv).trans orthogonal_card

theorem centralLine_le_orthogonal : centralLine ≤ orthogonalInCentralizer := by
  apply zpowers_le.mpr
  refine ⟨Multiplicative.ofAdd (shortParameter F σ),?_,rfl⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [shortParameter]

def quotientFour : Subgroup (X ⧸ centralLine) :=
  orthogonalInCentralizer.map (QuotientGroup.mk' centralLine)

instance quotientFour_normal : quotientFour.Normal := by
  let : orthogonalInCentralizer.Normal := orthogonalRadical_normal F σ hσ
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

instance quotientFour_elementary : IsElementaryAbelian 2 quotientFour :=
  IsElementaryAbelian.map (QuotientGroup.mk' centralLine)

theorem quotientFour_card : Nat.card quotientFour = 4 := by
  let N := centralLine.subgroupOf orthogonalInCentralizer
  have hcN : Nat.card N = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe centralLine_le_orthogonal).toEquiv).trans centralLine_card
  let f := (QuotientGroup.mk' centralLine).comp orthogonalInCentralizer.subtype
  have he : f.ker = N := by
    ext x
    change QuotientGroup.mk' centralLine x.val = 1 ↔ x.val ∈ centralLine
    exact QuotientGroup.eq_one_iff _
  have hr : f.range = quotientFour := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker, he, hcN, hr, orthogonal_in_card] at h
  omega

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.ShortRoot
