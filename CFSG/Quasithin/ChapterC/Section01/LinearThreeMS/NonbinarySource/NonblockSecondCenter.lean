module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SecondCenterSections
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockDoubledCenter

/-!
# The original nonblock upper commutator section at field four

The original nonabelian configuration already supplies a natural or doubled
model of its whole center, at one full SL₃ marking. Use that model to put
coordinates on the actual commutator pairing
Z₂(Q)/Z(Q) × Q/Φ(Q) → Z(Q). It is injective in the first variable and
simultaneously equivariant, with the whole target center at the same marking.

The original Q is a two-group normalized by KS. Hence the upper section is
nonzero, elementary, and normal under KS. Its numerator has exponent at most
four and lies in the literal C_Q(Φ(Q)) of the source fourth row. This supplies
an actual upper-section object for the remaining recognition, using the same
c, ChosenModule D, constrained hf, field and quotient. The center-model premise
is discharged by the checked original reconstruction; no Hypothesis1223 is used.

This does not identify Z₂(Q) with Q, recognize Q/Z(Q) as doubled dual, or
exclude the doubled nonabelian center. Those steps and the arbitrary-degree
fixed-factor branch remain with the full C.1.34 classification owner.
Source: Aschbacher–Smith original 4.3.8–10, printed pp.616–617, and
C.1.34, pp.136–137.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SecondCenterSections
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSections
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1<n) (hF : Nat.card F=2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
include D hf hn hF e
local notation "Z₂" => Subgroup.upperCentralSeries (Q c) 2

/-- The original nonabelian field-four core has a nonzero elementary second
central quotient, inside its Frattini centralizer and normal under the whole KS.
Its faithful commutator pairing uses the same marking as its whole center. -/
theorem source_nonabelian_upper_pairing (hfour : Nat.card F=4) (hna : ¬IsMulCommutative (Q c)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      IsElementaryAbelian 2 (center (Q c)) ∧
      U c < secondCenterIn (Q c) ∧
      secondCenterIn (Q c) ≤ Q c ⊓ centralizer (frattiniIn (Q c) : Set G) ∧
      K c ⊔ S c ≤ normalizer (secondCenterIn (Q c) : Set G) ∧
      IsElementaryAbelian 2 (Z₂ ⧸ (center (Q c)).subgroupOf Z₂) ∧
      (∀ x∈secondCenterIn (Q c), x^4=1) ∧
      (HasCommutatorCoordinates (K c) (Q c) (linearThreeActor mark)
          (specialLinearNatural (k := F) 3) ∨
        HasCommutatorCoordinates (K c) (Q c) (linearThreeActor mark)
          ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) := by
  let hp := msPair_of_quotient c D hf n (by omega) hF e
  have hmodels := DoubledCenter.source_nonabelian_center_models c D hf n hn hF e hfour hna
  obtain ⟨mark,hU,_,_,hm⟩ := hmodels
  have hpair : IsElementaryAbelian 2 (center (Q c)) ∧
      (HasCommutatorCoordinates (K c) (Q c) (linearThreeActor mark)
          (specialLinearNatural (k := F) 3) ∨
        HasCommutatorCoordinates (K c) (Q c) (linearThreeActor mark)
          ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) := by
    rcases hm with hm|hm
    · have hmo : HasSectionModel (K c)
          (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
            (msQ (K c) (c.I.pCoreIn 2))) ⊥ (linearThreeActor mark)
          (specialLinearNatural (k := F) 3) := by
        simpa only [ms_commutator_eq,←hU] using hm.1
      have hh := ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSections.ms_natural_upper_pairing
        hp hn mark hmo
      rw [ms_commutator_eq] at hh
      exact ⟨hh.1,Or.inl hh.2⟩
    · have hmo : HasSectionModel (K c)
          (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
            (msQ (K c) (c.I.pCoreIn 2))) ⊥ (linearThreeActor mark)
          ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
        simpa only [ms_commutator_eq,←hU] using hm
      have hh := ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSections.ms_doubled_upper_pairing
        hp hn mark hmo
      rw [ms_commutator_eq] at hh
      exact ⟨hh.1,Or.inr hh.2⟩
  let := hpair.1
  have hQ : IsPGroup 2 (Q c) := T.isPGroup'.to_le ((core_le_sylow c).trans inf_le_left)
  obtain ⟨hlt,hcent,hel,hpow⟩ := upper_structure hQ hna
  have hnorm : K c ⊔ S c ≤ normalizer (secondCenterIn (Q c) : Set G) :=
    ((sup_le (map_subtype_le _) inf_le_right).trans (core_normalized c)).trans
      (normalizer_le_normalizer_characteristic_image (Q c) (Subgroup.upperCentralSeries (Q c) 2))
  exact ⟨mark,hpair.1,hlt,hcent,hnorm,hel,hpow,hpair.2⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SecondCenterSections
