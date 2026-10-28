module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.FixedCentralizer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair.LocalGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair.SubfieldMaximality

/-!
# The generating subfield-centralizer pair

The local geometry constructs a common Sylow and a nontrivial linear twist,
and projective descent supplies the actual centralizer isomorphism. The
pure-field centralizer is maximal, so the two centralizers generate: otherwise
the second lies in the first and their equal orders force equality. Their
common center would then contain the nontrivial linear twist, contradicting
the center-freeness of the fixed-field PGL₂ factor.

Dickson's classification proves the required maximality for the actual
fixed-field embedding. The final assembly supplies the pair premise of
`InnerEscape.escape_of_pair_and_prime_geometry` for every odd prime,
including 3 and 5, without requiring perfectness of the smaller PGL₂.
Source: Aschbacher--Smith, E.1.8 and E.1.14(6), printed pp.210--211 and 214,
and the latter's reference to Aschbacher (1982), Lemma 4.10.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair
variable {F : Type*} [Field F] [Finite F]

/-- Actual consumer of Sylow placement and projective descent. The final
assembly below discharges its subfield-maximality premise. -/
theorem hasPair_of_pureCentralizer_isCoatom {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    [Finite (innerModel F σ)]
    (hmax : IsCoatom (centralizer ({pure σ} : Set (innerModel F σ)))) :
    HasSubfieldCentralizerPair σ := by
  obtain ⟨T, z, hz, hzr, hzs, hTC, hTD, hzC⟩ :=
    exists_central_twist hp hodd hF σ hσ
  have hr : ((z * pure σ : innerModel F σ) : PGammaL2 F).right = σ := by
    change (z : PGammaL2 F).right * σ = σ
    rw [hzr, one_mul]
  obtain ⟨e⟩ := centralizer_equiv_of_field_involution hp hodd hF σ hσ (z * pure σ) hzs hr
  refine ⟨T, z, hzs, hTC, hTD, ?_, ⟨e⟩⟩
  let C := centralizer ({pure σ} : Set (innerModel F σ))
  let D := centralizer ({z * pure σ} : Set (innerModel F σ))
  apply (hmax.ne_iff_eq_top le_sup_left).mp
  intro heq
  have hDC : D ≤ C := (le_sup_right : D ≤ C ⊔ D).trans_eq heq
  have hCD : C = D := (eq_of_le_of_card_ge hDC (Nat.card_congr e.toEquiv).ge).symm
  have hzcomm : C ≤ centralizer ({z} : Set (innerModel F σ)) := by
    intro x hx
    have hc := mem_centralizer_singleton_iff.mp hx
    have hd := mem_centralizer_singleton_iff.mp (hCD ▸ hx)
    rw [mem_centralizer_singleton_iff]
    apply mul_right_cancel (b := pure σ)
    calc
      x * z * pure σ = x * (z * pure σ) := mul_assoc _ _ _
      _ = (z * pure σ) * x := hd
      _ = z * (x * pure σ) := by rw [mul_assoc, ← hc]
      _ = z * x * pure σ := (mul_assoc _ _ _).symm
  have hz1 := linear_central_eq_one hp hodd hF σ hσ z hzC hzr hzcomm
  simp [hz1] at hz

/-- The two literal involution centralizers contain a common Sylow,
generate the canonical inner model, and are isomorphic. This discharges
the pair premise of `InnerEscape.escape_of_pair_and_prime_geometry`;
the geometric construction also covers characteristic five. -/
theorem hasSubfieldCentralizerPair {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    [Finite (innerModel F σ)] : HasSubfieldCentralizerPair σ :=
  hasPair_of_pureCentralizer_isCoatom hp hodd hF σ hσ
    (pureCentralizer_isCoatom hp hodd hF σ hσ)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair
