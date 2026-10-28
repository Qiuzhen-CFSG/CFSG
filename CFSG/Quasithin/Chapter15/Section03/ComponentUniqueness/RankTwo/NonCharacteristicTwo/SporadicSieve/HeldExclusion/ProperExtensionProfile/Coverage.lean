module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Candidates
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.OuterSylow
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.NormalizerInclusions

/-!
# The proper Held extension local cover

The fixed full automorphism stabilizer is a Sylow two-subgroup, under the
independent realization and normalizer-quotient inputs. Conjugate an arbitrary
Sylow-containing two-local to this marking. Its characteristic elementary
witness is normal in the same Sylow. The checked elementary catalogue identifies
that witness with one of the four literal rows. The full normalizer inclusions
place it in a candidate, and conjugating back proves the requested inclusion.

This module assembles both concrete certificates, leaving only realization and
the independent normalizer-quotient bound explicit. The retained GAP evidence
in `Coverage/source` is not a premise of any theorem.
The additional pure-pair normalizer is retained as `candidate true`; the inner
max3/max4/max5 catalogue alone cannot discharge these outer obligations.

Source: Aschbacher--Smith 15.3.41--42, printed p.1138, and GLS3 Table 5.3p.
The profile owner uses maximality subject to F*=O2 after this covering step.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
open CoverageData

private theorem map_conj_mul (C : Subgroup (MulAut Held.He)) (a b : MulAut Held.He) :
    (C.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      C.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

/-- Finite normal-elementary exhaustion and four ambient normalizer inclusions
suffice for the actual outer local cover. This conditional interface retains
both certificates explicitly; `twoLocal_le_candidate_conjugate` supplies them.
Maximality and characteristic two are unnecessary for this containment step. -/
theorem local_cover_of_elementary_certificates
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (henum : ∀ E : Subgroup (MulAut Held.He), E ≠ ⊥ → E ≤ outerRepresentative →
      (E.subgroupOf outerRepresentative).Normal → IsElementaryAbelian 2 E →
      ∃ j : Fin 4, E = ambientRow j)
    (hnormalizers : ∀ j : Fin 4, ∃ (i : Bool) (g : MulAut Held.He),
      normalizer (ambientRow j : Set (MulAut Held.He)) ≤
        (candidate i).map (MulAut.conj g).toMonoidHom)
    (T : Sylow 2 (MulAut Held.He)) (D : Subgroup (MulAut Held.He))
    (hlocal : IsTwoLocal D) (hTD : (T : Subgroup (MulAut Held.He)) ≤ D) :
    ∃ (i : Bool) (g : MulAut Held.He),
      D ≤ (candidate i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨P, hP⟩ := outerRepresentative_sylow hreal hbound
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut Held.He) T P
  have hTP : (T : Subgroup (MulAut Held.He)).map (MulAut.conj g).toMonoidHom = P :=
    congrArg Sylow.toSubgroup hg
  have hPD : (P : Subgroup (MulAut Held.He)) ≤ D.map (MulAut.conj g).toMonoidHom := by
    rw [← hTP]
    exact map_mono hTD
  obtain ⟨E, hE, hEP, hEn, hEe, hDE⟩ := exists_normal_elementary_sylow_overgroup P
    (D.map (MulAut.conj g).toMonoidHom)
    (Theory.Quasithin.isTwoLocal_map (MulAut.conj g) hlocal) hPD
  rw [hP] at hEP hEn
  obtain ⟨j, rfl⟩ := henum E hE hEP hEn hEe
  obtain ⟨i, a, ha⟩ := hnormalizers j
  have hb := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hDE.trans ha)
  rw [map_conj_mul, map_conj_mul, inv_mul_cancel] at hb
  have hid : (MulAut.conj (1 : MulAut Held.He)).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  rw [hid, Subgroup.map_id] at hb
  exact ⟨i, g⁻¹ * a, hb⟩

/-- Every Sylow-containing two-local in the actual automorphism group lies in
a conjugate of one of the two literal normalizers. The concrete four-row
catalogue and full ambient normalizer inclusions discharge both finite inputs;
neither local characteristic two nor maximality is needed for containment. -/
theorem twoLocal_le_candidate_conjugate
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (T : Sylow 2 (MulAut Held.He)) (D : Subgroup (MulAut Held.He))
    (hlocal : IsTwoLocal D) (hTD : (T : Subgroup (MulAut Held.He)) ≤ D) :
    ∃ (i : Bool) (g : MulAut Held.He),
      D ≤ (candidate i).map (MulAut.conj g).toMonoidHom :=
  local_cover_of_elementary_certificates hreal hbound
    (normal_elementary_eq_ambientRow hreal hbound)
    (four_normalizer_inclusions hreal) T D hlocal hTD

/-- The covering input used by the proper-extension profile at the two-local
in source 15.3.41(2). Its F*=O₂ assumption is retained to match the profile's
literal interface. Candidate characteristic two and the quotient calculations
belong to the profile assembly, not to this containment theorem. -/
theorem local_cover
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (T : Sylow 2 (MulAut Held.He)) (D : Subgroup (MulAut Held.He))
    (hlocal : IsTwoLocal D) (hTD : (T : Subgroup (MulAut Held.He)) ≤ D)
    (_hF : generalizedFitting D = pCore 2 D) :
    ∃ (i : Bool) (g : MulAut Held.He),
      D ≤ (candidate i).map (MulAut.conj g).toMonoidHom :=
  twoLocal_le_candidate_conjugate hreal hbound T D hlocal hTD

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile
