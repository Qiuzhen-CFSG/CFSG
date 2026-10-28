module

public import Theory.SpecificGroups.Rudvalis.Multiplier.OddLocal.Three.Inversion
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddLocal.Five.Inversion
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.GroupTheory.PerfectCentralCoverSylowNine.OddInversion

/-!
# Marked odd Sylow configurations in the actual Rudvalis group

The two retained subgroups have orders 27 and 125. The certified ambient
order proves their indices prime to 3 and 5, respectively, so they are
actual Sylow subgroups. The checked inverters act on these literal generators.
These configurations discharge the concrete local premises of the odd-primary
central-cover calculation; neither a semipresentation nor a subgroup-family
tag is used. Sources: ATLAS RuG1-p4060B0, GLS3 Table 5.3r, p.279, and
Aschbacher–Smith I.1.3(1), printed p.407.
-/

namespace Rudvalis.Multiplier.OddLocal
open Subgroup
open scoped commutatorElement

public theorem exists_three_configuration :
    ∃ (Q : Sylow 3 Model) (x y r : Model),
      closure ({x, y} : Set Model) = (Q : Subgroup Model) ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute x ⁅x, y⁆ ∧ Commute y ⁅x, y⁆ ∧
      r * x * r⁻¹ = x⁻¹ ∧ r * y * r⁻¹ = y⁻¹ ∧ Commute r ⁅x, y⁆ := by
  have hi : ¬ 3 ∣ ThreeCertificate.P.index := by
    have h := ThreeCertificate.P.card_mul_index
    rw [ThreeCertificate.card_P, model_card] at h
    have he : ThreeCertificate.P.index = 5404672000 := by omega
    rw [he]
    decide
  let hp : IsPGroup 3 ThreeCertificate.P :=
    IsPGroup.of_card (n := 3) ThreeCertificate.card_P
  refine ⟨hp.toSylow hi, ThreeCertificate.x, ThreeCertificate.y, ThreeCertificate.r,
    ?_, ThreeCertificate.x_pow, ThreeCertificate.y_pow,
    ThreeCertificate.commutator_ne_one, ThreeCertificate.x_commute_commutator,
    ThreeCertificate.y_commute_commutator, ThreeCertificate.r_inverts_x,
    ThreeCertificate.r_inverts_y, ThreeCertificate.r_commute_commutator⟩
  change closure _ = closure (Set.range ThreeCertificate.generators)
  congr 1
  ext x
  simp [ThreeCertificate.generators, or_comm]

public theorem exists_five_configuration :
    ∃ (Q : Sylow 5 Model) (x y r : Model),
      closure ({x, y} : Set Model) = (Q : Subgroup Model) ∧
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute x ⁅x, y⁆ ∧ Commute y ⁅x, y⁆ ∧
      r * x * r⁻¹ = x⁻¹ ∧ r * y * r⁻¹ = y⁻¹ ∧ Commute r ⁅x, y⁆ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hi : ¬ 5 ∣ FiveCertificate.P.index := by
    have h := FiveCertificate.P.card_mul_index
    rw [FiveCertificate.card_P, model_card] at h
    have he : FiveCertificate.P.index = 1167409152 := by omega
    rw [he]
    decide
  let hp : IsPGroup 5 FiveCertificate.P :=
    IsPGroup.of_card (n := 3) FiveCertificate.card_P
  refine ⟨hp.toSylow hi, FiveCertificate.x, FiveCertificate.y, FiveCertificate.r,
    ?_, FiveCertificate.x_pow, FiveCertificate.y_pow,
    FiveCertificate.commutator_ne_one, FiveCertificate.x_commute_commutator,
    FiveCertificate.y_commute_commutator, FiveCertificate.r_inverts_x,
    FiveCertificate.r_inverts_y, FiveCertificate.r_commute_commutator⟩
  change closure _ = closure (Set.range FiveCertificate.generators)
  congr 1
  ext x
  simp [FiveCertificate.generators, or_comm]

end Rudvalis.Multiplier.OddLocal
