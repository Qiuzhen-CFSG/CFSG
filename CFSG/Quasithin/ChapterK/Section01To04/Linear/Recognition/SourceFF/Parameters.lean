module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.Preparation
public import CFSG.Quasithin.ClassicalModels
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Retaining the original projective linear parameter

An actual PSL₃(2ʳ) quotient identification supplies its finite binary matrix
field. The scalar-cover constructor then keeps that field, exponent and
projective quotient map in the exact action consumed by the module sieve.

Source: Aschbacher–Smith K.3.2 and I.1.3, printed pp.454 and 407.
-/

public section
open Subgroup Representation Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.SourceFF
open ChapterB.QuasisimpleSource

universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V]
  [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
  {K : GroupClass.{u}} {L : Subgroup G}

/-- The original family alternative constructs the binary field and the
literal scalar covering, commuting with the retained quotient equivalence. -/
theorem exists_binaryField_cover (h : SourceHypothesis K ρ L)
    (r : ℕ) (hr : 0 < r)
    (hquot : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ r)) :
    ∃ B : BinaryField, B.degree = r ∧
      ∃ e : L ⧸ center L ≃* PSL(3,B.Carrier),
      ∃ C : LinearCover B 3 L,
        (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).comp C.projection =
          Matrix.PSL3.projection B.Carrier := by
  obtain ⟨F, hField, hFinite, hF, ⟨e⟩⟩ := hquot
  let : Field F := hField
  let : Finite F := hFinite
  let : Fintype F := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let B : BinaryField := { Carrier := F, degree := r, degree_pos := hr, card_eq := hF }
  obtain ⟨C, hC⟩ := exists_linearCover h B e
  exact ⟨B, rfl, e, C, hC⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition.SourceFF
