module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.BadCentralizers.Balance
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.BadCentralizers.Sieve
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.FamilyToLocal
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.OmegaNormalizer
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The conditional earlier-source assembly of the bad-centralizer branch

The actual source setup constructs the maximal component and its aligned
Sylow. The full six-case 1.1.5 implication selects its model through the
proved inspection, and the universal I.3.1(1),(2) projection supplies the
balance orbit. The proved U-normalization collapses that orbit, so the
existing maximal-component contradiction applies.

The two earlier-source implications remain obligations of qt-1-01 and
qt-i-03, discharged by the existing Bender parent qt-2-01-03-bender. This
module proves their application, not either earlier theorem or recognition
of the good-centralizer branch. The full KnownSimple class is retained.
Source: Proposition 2.2.2, printed pp.519--520.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter2.BenderFusion
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

namespace BadCentralizers

/-- Exactly the component-action clause of the universal earlier-source
1.1.5, including all six alternatives. This is an input proposition, not
a classification proof. Its producer is qt-1-01 and its quasisimple owner. -/
@[expose] def ComponentSource115 (G : Type*) [Group G] : Prop :=
  ∀ (H : Subgroup G) (S : Sylow 2 H) (M : Subgroup G) (z : G),
    Chapter1.Lemma115Hypotheses H S M z →
      ∀ D : Subgroup H, IsComponent H D → HasModelAction115 D z

end BadCentralizers

/-- The source bad-centralizer branch is contradictory once its two genuine
earlier-source implications are supplied. Model choice, original-z innerness,
odd-core vanishing, Sylow placement and the selected balance are all proved. -/
theorem LocalControlWitness.false_of_bad_centralizer_of_earlier_source
    (w : LocalControlWitness T M)
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (source115 : BadCentralizers.ComponentSource115 G)
    (source13 : BadCentralizers.OrdinaryBalance13.{u} CFSG.KnownSimple.IsKnownSimple)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M) : False := by
  have hchar : HasCharacteristicTwo M := hG.evenCharacteristic T M hM hTM
  obtain ⟨u, hu, hu1, S, hUS, hST, hcore, L, hL, hmax⟩ :=
    w.exists_maximal_bad_centralizer_data hchar hTM hbad
  have h115 := w.lemma115_of_aligned_element_centralizer hG hM hu hu1 S hST
  obtain ⟨hmodel, hzin⟩ := w.bender_model_of_source115 _ S hUS hST hcore L hL hmax.1.1
    (source115 _ S M w.z h115 (L.subgroupOf _) hL.2)
  exact w.false_of_bender_model_component hG hTM _ S hUS hST hcore L hL hmax
    (fun v hv hv1 => w.balance_at_maximal_bad_component hG hchar hbad source13 hmax hv hv1)
    hmodel hzin

/-- The bad branch is eliminated in the form consumed by the existing
good-centralizer/Shult recognition branch. -/
theorem LocalControlWitness.centralizers_le_of_earlier_source
    (w : LocalControlWitness T M)
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (source115 : BadCentralizers.ComponentSource115 G)
    (source13 : BadCentralizers.OrdinaryBalance13.{u} CFSG.KnownSimple.IsKnownSimple) :
    ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M := by
  intro u hu hu1
  by_contra hn
  exact w.false_of_bad_centralizer_of_earlier_source hG hM hTM source115 source13
    ⟨u, hu, hu1, hn⟩

/-- Actual empty-delta source application. The local-control data and every
centralizer containment are constructed; only the two earlier universal
theorems remain explicit before the parent applies recognition. -/
theorem source_local_control_with_centralizers_of_delta_empty
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅)
    (source115 : BadCentralizers.ComponentSource115 G)
    (source13 : BadCentralizers.OrdinaryBalance13.{u} CFSG.KnownSimple.IsKnownSimple) :
    ∃ w : LocalControlWitness T M,
      ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M := by
  obtain ⟨_, ⟨w⟩⟩ := source_local_control_of_delta_empty hG T M hM hTM hunique hdelta
  exact ⟨w, w.centralizers_le_of_earlier_source hG hM hTM source115 source13⟩

end CFSG.Quasithin.Chapter2.BenderFusion
