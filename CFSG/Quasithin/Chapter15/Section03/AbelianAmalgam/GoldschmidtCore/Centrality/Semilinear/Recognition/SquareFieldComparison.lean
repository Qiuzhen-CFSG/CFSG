module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SquareField

/-!
# The square-field source branch in the rank-one comparison

The actual component has order at least 360 for either allowed defining-prime
congruence. The full B-side classification places it in a binary degree-two,
binary degree-three or alternating-five model. The first comparison forces
alternating-five, and the remaining two are excluded by their exact orders.
This uses the actual component and Sylow; no local-generator shape is needed.
Source: Aschbacher–Smith, F.6.18 and 15.3.68, printed pp.309–310,1154–1155.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] [Finite D]

/-- The genuine full B-side source excludes either square-field congruence
in the rank-one semilinear comparison. -/
theorem square_field_classification_impossible
    {S : Sylow 2 D} (r : FSource.SquareFieldExtensionRow S)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (hne : offenderSubgroup ρ ≠ ⊥)
    (hcore : pCore 2 D = ⊥)
    (hb : SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)) : False := by
  have hm := r.congruence
  have ho : Odd r.field.prime := Nat.odd_iff.mpr (by omega)
  have hodd : Odd (Nat.card r.field.Carrier) := by rw [r.field.card]; exact ho.pow
  have hc : 9 ≤ Nat.card r.field.Carrier := by
    rw [r.field.card, r.degree]
    have h3 : 3 ≤ r.field.prime := by omega
    nlinarith
  have hl := pslTwo_order_ge_360 hodd hc
  have hs : Nat.card S ≤ 128 := by
    obtain ⟨es⟩ := r.sylow
    rw [Nat.card_congr es.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num [FSource.C]
  have noA (a : generalizedFitting D ≃* alternatingGroup (Fin 5)) : False := by
    rw [Nat.card_congr (r.componentEquiv.symm.trans a).toEquiv,
      nat_card_alternatingGroup] at hl
    norm_num [Nat.factorial] at hl
  have hb' := fitting_source_rank_one ρ hr hne hcore r.quasisimple S hs hb
  rcases hb' with ⟨_, B, _, he⟩ | ⟨_, he⟩ | ⟨_, he⟩
  · obtain ⟨e⟩ := he
    obtain ⟨a⟩ := odd_linearTwo_binary_alternatingFive B
      ⟨r.field.prime, r.field.degree, r.field.prime_isPrime, ho,
        r.field.degree_pos, r.field.card⟩ e r.componentEquiv
    exact noA a
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr (r.componentEquiv.symm.trans e).toEquiv,
      Matrix.PSL3Two.card_SL] at hl
    omega
  · exact noA he.some

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
