module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.FinalOrdinary
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Central

/-!
# The original module in the surviving field-four configurations

The actual full quotient and field order distinguish the SL₃ marking from
the symplectic and G₂ markings. The proved SL₃ cohomology calculation kills
the original central fixed subspace, making its quotient projection bijective.
Thus the original V itself has order 64, rather than only its quotient.

The endpoint applies this to both remaining J₄/Ru configurations of the
literal Hall kernel. The full SL₃(4) quotient and its cubic center are retained.
Source: Aschbacher--Smith 11.0.3(3), p.760, and 4.4.6, 4.4.10--12, pp.620--622.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The order comparison recovers the original linear action marking. -/
theorem linear_marking_of_field_four (hf : S.field.degree = 2)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) :
    Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) := by
  cases S.natural with
  | sl3 hm => exact hm
  | sp4 hm =>
    have hc := Nat.card_congr (e.symm.trans hm.some.groupEquiv).toEquiv
    rw [linear_three_order,Theory.SpecificGroups.SymplecticFour.card_sp] at hc
    norm_num [S.field.card_eq,hf] at hc
  | g2 hm =>
    have hc := Nat.card_congr (e.symm.trans hm.some.groupEquiv).toEquiv
    rw [linear_three_order,Atlas.G2.card_Model] at hc
    norm_num [S.field.card_eq,hf] at hc

/-- In the actual field-four linear row the original central fixed subspace
vanishes, and the original module has order 64. -/
theorem original_module_card_of_field_four (hf : S.field.degree = 2)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) :
    V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64 := by
  obtain ⟨m⟩ := linear_marking_of_field_four D S hf e
  have hz := Preliminary.sl3_centralizer_eq_bot D S m
  refine ⟨hz,?_⟩
  have hq : Function.Bijective D.toCentralQuotient := by
    refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_,D.toCentralQuotient_surjective⟩
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact mem_bot.mp (hz ▸
      (show (v : G) ∈ V ⊓ centralizer (L : Set G) from
        ⟨v.property,(quotient_eq_one_iff D v).mp hv⟩))
  have hV : Nat.card V = Nat.card (Fin 3 → S.field.Carrier) :=
    (Nat.card_congr (MulEquiv.ofBijective D.toCentralQuotient hq).toEquiv).trans
      (Nat.card_congr m.linearEquiv.toEquiv)
  rw [hV,Nat.card_fun,Nat.card_fin,S.field.card_eq,hf]
  decide

/-- The already constructed pushing-up configuration discharges the field-four
premises on the original chosen module. -/
theorem PushingUpFieldFourCase.original_module {A : Subgroup G}
    (h : PushingUpFieldFourCase D S A) :
    V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64 := by
  obtain ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,hVB,he,hno,hsize,hVW,
    hf,⟨e⟩,hz,hK⟩ := h
  exact original_module_card_of_field_four D S hf e

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
