module
public import CFSG.Quasithin.ChapterJ.Section03.Involutions
public import CFSG.Quasithin.ChapterJ.Section03.CentralizerCount
public import CFSG.Quasithin.ChapterJ.Section03.OddNormalizer
public import CFSG.Quasithin.ChapterJ.Section03.Numerics
public import CFSG.Quasithin.ChapterJ.Section03.OrderEstimate
/-!
# The source order argument of J.3

This assembles the actual class-product closure, the455 and1391 commuting
counts, the A.6.5 estimate, and the literal Sylow-thirteen normalizer congruence.
The original two-Sylow is retained throughout. The displayed premises are only
the independent J.2 conclusions: Suzuki residual, two involution classes,
the480 middle-layer count, a Sylow three-group of order27 and a subgroup of
order125. Their source completion owns the unconditional TypeRu endpoint.

Source: Aschbacher--Smith J.3.1--5, printed pp.438--439.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open ChapterA.Section05To06 Centralizers
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

theorem index_bound_of_source_inputs (c : Choices d) (r : c.SuzukiSourceConclusion)
    (h : TwoInvolutionClasses c.z c.s)
    (h480 : Nat.card {x : G // IsConj c.z x ∧ x ∈ d.toTypeRuSetup.K ∧
      x ∉ d.toTypeRuSetup.Q} = 480) :
    d.toTypeRuSetup.H.index ≤ 455*1846 ∧
      d.toTypeRuSetup.H.index < (3^2*5^2*7*13)*42 :=
  index_bound_of_class_counts c h (class_closed_of_suzuki c r h)
    (count_commuting_s_of_suzuki c r) (count_commuting_z_of_middle_count c h480)

/-- The J.3.1 order argument, with precisely the independent J.2 inputs retained. -/
theorem order_of_source_inputs (c : Choices d) (r : c.SuzukiSourceConclusion)
    (h : TwoInvolutionClasses c.z c.s)
    (h480 : Nat.card {x : G // IsConj c.z x ∧ x ∈ d.toTypeRuSetup.K ∧
      x ∉ d.toTypeRuSetup.Q} = 480)
    (P3 : Sylow 3 G) (h3 : Nat.card P3 = 27)
    (P5 : Subgroup G) (h5 : Nat.card P5 = 125) :
    Nat.card G = 2^14 * 3^3 * 5^3 * 7 * 13 * 29 := by
  have hb := (index_bound_of_source_inputs c r h h480).1
  have hH : Nat.card d.toTypeRuSetup.H = 2^14*3*5 := d.ru2.card_H d.card_Z
  have hbG := Nat.mul_le_mul_left (Nat.card d.toTypeRuSetup.H) hb
  rw [d.toTypeRuSetup.H.card_mul_index,hH] at hbG
  have hT : Nat.card d.T = 2^14 := d.toTypeRuSetup.card_T_of_card_Z d.card_Z
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact order_of_sylow_data d.T hT P3 h3 P5 h5
    (prime_dvd_card c r (Or.inl rfl)) (prime_dvd_card c r (Or.inr rfl))
    hbG (card_mod_thirteen_square c r)

end CFSG.Quasithin.ChapterJ.Section03
