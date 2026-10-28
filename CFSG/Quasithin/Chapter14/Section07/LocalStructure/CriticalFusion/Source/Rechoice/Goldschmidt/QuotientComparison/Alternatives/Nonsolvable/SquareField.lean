module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SquareField

/-!
# The actual square-field component is too large for the D comparison

For either defining-prime congruence three or five modulo eight, the
square field has odd order at least nine. Its PSL₂ component therefore
has order at least 360, whereas the retained original small subnormal
subgroup forces the generalized Fitting subgroup to have order at most
168. The second theorem applies this to the actual bang quotient and
its literal retained subgroup image.

Source: Aschbacher–Smith, F.6.18(8) and 14.7.70, pp.309–310 and1075.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open FSource

/-- Both genuine square-field congruence branches exceed the actual small component bound. -/
theorem not_square_field_extension {D : Type*} [Group D] [Finite D]
    (K : Subgroup D) (hK : K.IsSubnormal) (hm : SmallModel K)
    {S : Sylow 2 D} (r : SquareFieldExtensionRow S) : False := by
  have hp : 3 ≤ r.field.prime := by have := r.congruence; omega
  have ho : Odd r.field.prime := by rw [Nat.odd_iff]; have := r.congruence; omega
  have hodd : Odd (Nat.card r.field.Carrier) := by rw [r.field.card]; exact ho.pow
  have hb : 9 ≤ Nat.card r.field.Carrier := by
    rw [r.field.card,r.degree]
    nlinarith
  have hl := pslTwo_order_ge_360 hodd hb
  have hu := fitting_card_le K hK hm r.quasisimple
  rw [Nat.card_congr r.componentEquiv.toEquiv] at hu
  omega

open Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} (c : CriticalPath (L := L) F)

/-- The original retained subgroup excludes this row on the actual bang quotient. -/
theorem not_square_field_bang (small : SmallSubnormal c)
    (S : Sylow 2 ((I c) ⧸ pPrimeCore 3 (I c))) :
    ¬ Nonempty (SquareFieldExtensionRow S) := by
  rintro ⟨r⟩
  obtain ⟨K,_,_,hN,hmN⟩ := retained_small_image c small
  exact not_square_field_extension (K.map (plusToBang c)) hN hmN r

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
