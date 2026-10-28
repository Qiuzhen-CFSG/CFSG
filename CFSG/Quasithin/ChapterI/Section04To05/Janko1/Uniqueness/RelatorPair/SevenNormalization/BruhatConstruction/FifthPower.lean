module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.Normalizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CountingData
public import Theory.GroupTheory.CubicCentralizerInvolutionProduct

/-!
# The fifth-power relation in Janko's local configuration

An involution w which centralizes u and inverts y automatically normalizes
H = ⟨y,u⟩. Moreover, if |C_G(u)| divides thirty, the dihedral product lemma
proves (xw)^5 = 1, since the marked involution x also centralizes u. Thus
such an inverter extends the actual marked normalizer to a BruhatFrame.
Bender's odd-prime centralizer data supplies the required divisibility for
both values of its parameter; no choice between these values is needed.

These are conditional constructions. The inverter and BenderPrimeData
remain explicit premises of the final theorem below. Its source assembly
must construct both from the original hypotheses before asserting existence
of a BruhatFrame. Neither a representation nor a recognition theorem is
used in the fifth-power deduction.

Source: Gorenstein, *Finite Groups*, §16.6, pp.482–483, equation (6.2);
Z. Janko, J. Algebra 3 (1966), 147–186. The bound on odd-prime centralizers
is Bender (1974), §4, (4.1). The original-paper access limitation is recorded
in RelatorPair/Source/README.md.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
open Subgroup
variable {G : Type*} [Group G] [Finite G] {h : Janko1CentralizerData G}

/-- The marked fixed involution centralizes the literal cubic generator. -/
public theorem NormalizerFrame.fixed_involution_commutes (D : NormalizerFrame h) :
    Commute D.x D.u := by
  have hxC : D.x ∈ centralizer (zpowers D.u : Set G) :=
    ((D.fixed ▸ mem_zpowers D.x) : D.x ∈ (h.sylow : Subgroup G) ⊓
      centralizer (zpowers D.u : Set G)).2
  exact (mem_centralizer_iff.mp hxC D.u (mem_zpowers D.u)).symm

/-- Fixing u and inverting y preserves their actual generated subgroup H. -/
public theorem NormalizerFrame.inverter_normalizes (D : NormalizerFrame h) (w : G)
    (hcomm : Commute w D.u) (hinv : w * D.y * w⁻¹ = D.y⁻¹) :
    w ∈ normalizer (D.H : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, ← D.generated, Subgroup.map_sup,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  change zpowers (w * D.y * w⁻¹) ⊔ zpowers (w * D.u * w⁻¹) =
    zpowers D.y ⊔ zpowers D.u
  rw [hinv, zpowers_inv, mul_inv_eq_iff_eq_mul.mpr hcomm.eq]

/-- The numerical cubic-centralizer bound supplies the fifth-power identity
for every involution commuting with the marked u. -/
public theorem NormalizerFrame.product_fifth_of_centralizer_card
    (D : NormalizerFrame h) (w : G) (hw : orderOf w = 2)
    (hcomm : Commute w D.u)
    (hcard : Nat.card (centralizer ({D.u} : Set G)) ∣ 30) :
    (D.x * w) ^ 5 = 1 :=
  involution_product_pow_eq_one_of_cubic_centralizer_card_dvd D.u D.x w 5
    D.order_u D.order_x hw D.fixed_involution_commutes hcomm hcard

/-- Extend the marked normalizer using an inverter and the numerical
centralizer bound. The fifth-power relation is proved, not a premise. -/
public theorem exists_bruhatFrame_of_inverter (D : NormalizerFrame h) (w : G)
    (hw : orderOf w = 2) (hcomm : Commute w D.u)
    (hinv : w * D.y * w⁻¹ = D.y⁻¹)
    (hcard : Nat.card (centralizer ({D.u} : Set G)) ∣ 30) :
    Nonempty (BruhatFrame h) :=
  ⟨{ toNormalizerFrame := D
     w := w
     order_w := hw
     w_normalizes := D.inverter_normalizes w hcomm hinv
     w_centralizes := hcomm
     w_inverts := hinv
     product_fifth := D.product_fifth_of_centralizer_card w hw hcomm hcard }⟩

/-- Conditional assembly from the independently produced odd-prime data
and an existential choice of normalizer and inverter. No extension of every
fixed normalizer frame is required. -/
public theorem exists_bruhatFrame_of_benderPrimeData {d : ℕ}
    (b : Janko1CentralizerData.BenderPrimeData G d)
    (hinverter : ∃ (D : NormalizerFrame h) (w : G), orderOf w = 2 ∧
      Commute w D.u ∧ w * D.y * w⁻¹ = D.y⁻¹) :
    Nonempty (BruhatFrame h) := by
  obtain ⟨D, w, hw, hcomm, hinv⟩ := hinverter
  apply exists_bruhatFrame_of_inverter D w hw hcomm hinv
  rw [b.centralizer_three D.u D.order_u]
  split_ifs <;> decide

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
