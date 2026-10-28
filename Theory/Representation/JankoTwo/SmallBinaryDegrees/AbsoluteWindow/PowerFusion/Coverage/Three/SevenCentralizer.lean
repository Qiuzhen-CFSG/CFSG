module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Base
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Three.SevenCentralizer.Checks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Three.Sylow
import Mathlib.Data.Fintype.Perm

/-!
# Odd orders in the second literal cubic centralizer

Representative 7 fixes exactly four points. Its centralizer permutes those
points, so its 24th powers fix them individually. Conjugating their pointwise
fixer to the fixer of 0, 78, 36 and 84 allows the exhaustive normal-form check
in `SevenCentralizer.Checks` to prove that these 24th powers have sixth power
one. Thus odd element orders divide nine. The certified Sylow fusion then
gives the required coverage, without additional centralizer or fusion premises.

Source: retained ATLAS `J2G1-p100B0` data and the proved four-transversal
normal forms. See `SevenCentralizer/source/README.md` for attribution,
reproduction and the relation between the action and the finite checks.
-/

namespace Sporadic.LeechRelated.J2.PowerFusionCertificate
open GeneratorPair.SecondOrbitCertificate SevenCentralizerCertificates

set_option Elab.async false

private def sevenFixed : Finset (Fin 100) := {6, 52, 71, 89}

private theorem seven_fixed_iff : ∀ x : Fin 100,
    inclusion (representative 7) x = x ↔ x ∈ sevenFixed := by
  apply allFin
  decide +kernel

private theorem card_sevenFixed : Fintype.card sevenFixed = 4 := by decide +kernel

private theorem centralizer_pow_fixes (g : Carrier)
    (hg : g ∈ Subgroup.centralizer ({representative 7} : Set Carrier)) :
    ∀ x ∈ sevenFixed, inclusion (g ^ 24) x = x := by
  have hc (x : Fin 100) : inclusion (representative 7) (inclusion g x) =
      inclusion g (inclusion (representative 7) x) := by
    exact (congrArg (fun y : Carrier => inclusion y x)
      (Subgroup.mem_centralizer_singleton_iff.mp hg)).symm
  have hi (x : Fin 100) : inclusion g x ∈ sevenFixed ↔ x ∈ sevenFixed := by
    rw [← seven_fixed_iff, ← seven_fixed_iff, hc, (inclusion g).injective.eq_iff]
  let p : Equiv.Perm sevenFixed := (inclusion g).subtypePerm hi
  have hp : p ^ 24 = 1 := by
    have h := pow_card_eq_one (x := p)
    simpa only [Fintype.card_perm, card_sevenFixed, Nat.factorial] using h
  intro x hx
  have h := congrArg (fun q : Equiv.Perm sevenFixed => (q ⟨x, hx⟩ : Fin 100)) hp
  simpa only [p, Equiv.Perm.subtypePerm_pow, Equiv.Perm.subtypePerm_apply,
    Equiv.Perm.one_apply, map_pow] using h

private def sevenTransporter : Carrier := element (96, 0, 0, 0)

private theorem transported_points : inclusion sevenTransporter 0 ∈ sevenFixed ∧
    inclusion sevenTransporter 78 ∈ sevenFixed ∧
    inclusion sevenTransporter 36 ∈ sevenFixed ∧
    inclusion sevenTransporter 84 ∈ sevenFixed := by decide +kernel

private theorem seven_fixer_pow_six (g : Carrier)
    (hg : ∀ x ∈ sevenFixed, inclusion g x = x) : g ^ 6 = 1 := by
  have hf (x : Fin 100) (hx : inclusion sevenTransporter x ∈ sevenFixed) :
      inclusion (MulAut.conj (sevenTransporter⁻¹) g) x = x := by
    change inclusion (sevenTransporter⁻¹ * g * (sevenTransporter⁻¹)⁻¹) x = x
    simp only [inv_inv, map_mul, map_inv, Equiv.Perm.mul_apply]
    rw [hg _ hx]
    exact (inclusion sevenTransporter).symm_apply_apply x
  have hp := transformed_fixer_pow_six (MulAut.conj (sevenTransporter⁻¹) g)
    (hf 0 transported_points.1) (hf 78 transported_points.2.1)
    (hf 36 transported_points.2.2.1) (hf 84 transported_points.2.2.2)
  apply (MulAut.conj (sevenTransporter⁻¹)).injective
  simpa only [map_pow, map_one] using hp

/-- Odd orders in the literal centralizer of the second cubic representative
 divide nine. The pointwise-fixer and permutation-action premises are discharged. -/
public theorem orderOf_dvd_nine_of_odd_seven_centralizer (g : Carrier)
    (hg : g ∈ Subgroup.centralizer ({representative 7} : Set Carrier))
    (h2 : ¬2 ∣ orderOf g) : orderOf g ∣ 9 := by
  have hp : g ^ 144 = 1 := by
    have h := seven_fixer_pow_six (g ^ 24) (centralizer_pow_fixes g hg)
    simpa only [← pow_mul] using h
  have hd : orderOf g ∣ 144 := orderOf_dvd_of_pow_eq_one hp
  have hc : Nat.Coprime (orderOf g) (2 ^ 4) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm).pow_right _
  exact hc.dvd_of_dvd_mul_left hd

/-- Coverage in the second literal cubic centralizer. This discharges the
 second premise of `covered_odd_of_three_dvd_of_centralizers`; in fact the
 odd-order bound does not require the additional divisibility hypothesis. -/
public theorem covered_odd_three_centralizer_seven (g : Carrier)
    (hg : g ∈ Subgroup.centralizer ({representative 7} : Set Carrier))
    (h2 : ¬2 ∣ orderOf g) (h3 : 3 ∣ orderOf g) :
    ∃ i : Fin 21, IsConj (representative i) g := by
  have hd : orderOf g ∣ 3 ^ 2 := orderOf_dvd_nine_of_odd_seven_centralizer g hg h2
  obtain ⟨n, _, hn⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hd
  have hne : g ≠ 1 := by
    intro he
    subst g
    norm_num at h3
  rcases three_power_fusion g hn hne with h | h
  · exact ⟨1, h⟩
  · exact ⟨7, h⟩

end Sporadic.LeechRelated.J2.PowerFusionCertificate
