module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Orbit
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.OddNoncentral
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Containment.Rows
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Endpoint
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Normalizer
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.CharacteristicTwo.Core
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.CharacteristicTwo

/-!
# Assembly of the reducible component-normalizer branch

The source preparation uses C.2.3 only to supply the SQTK structure of the
literal involution centralizer. It constructs the exchanged T_u-orbit and
retains the actual four-model quotient sieve. The final reduction feeds the
order-p pair obstruction into the existing centralizer-containment and TI
consumers.

Orbit containment, the elementary plane, the complement factorization, the
literal Sylow product equality, and all source model restrictions are proved.
Both component geometries and the actual normalizer permutation are proved.
The point core supplies the genuine C.2.7 setup and its Sylow condition in
the characteristic-two Borel rows; the odd-linear row is excluded through
its actual star image. The final swapped exclusion has no additional
geometric premise. OrbitFacts and Control retain their original independent
producers, qt-d-1317-module-orbits and qt-d-1317-centralizer-control; the
separate irreducible exclusion belongs to the centralizer assembly owner
qt-d-1317-centralizer-sieve. Earlier conditional APIs are preserved.

Source: Aschbacher--Smith, 13.1.12(3)--13, printed pp.874--875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- Apply the orbit and model deductions to the actual C.2.3 source setup. -/
theorem Context.swapped_preparation (h : Context T L p) (o : OrbitFacts T L p)
    (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) :
    ((componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G))).subgroupOf
      (centralizer ({u} : Set G))).Normal ∧
    ⁅componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)),XiP p L⁆ =
      componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ∧
    NonnormalCComponentModel (XiQuotient K) ∧
    ∃ t ∈ (T : Subgroup G) ⊓ centralizer ({u} : Set G),
      t ∉ normalizer (K : Set G) ∧ K.conjBy t ≠ K ∧
      componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) =
        K ⊔ K.conjBy t ∧
      ∀ g ∈ centralizer ({u} : Set G), K.conjBy g = K ∨ K.conjBy g = K.conjBy t := by
  have hH := (c.pushing_up u s hnt).sqtk
  exact ⟨e.orbit_normal hH,h.component_orbit_commutator s e hH,
    h.reducible_component_model o s e hH hr,h.exists_component_exchange o s e hH hr⟩

/-- Both literal component geometries feed the same proved normalizer-action
contradiction. Their pair constructions and the sieve are still required. -/
theorem Context.swapped_false_of_geometry (h : Context T L p)
    {u : G} {K : Subgroup G}
    (hsieve : ∃ P : Sylow p (XiP p L),
      SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hchar : ∀ P : Sylow p (XiP p L),
      SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      generalizedFitting K = pCore 2 K →
      Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p))
    (hordinary : ∀ P : Sylow p (XiP p L),
      SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      generalizedFitting K ≠ pCore 2 K →
      Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p)) : False := by
  obtain ⟨P,d⟩ := hsieve
  by_cases hf : generalizedFitting K = pCore 2 K
  · exact h.false_of_swapped_line_pair P d (hchar P d hf).some
  · exact h.false_of_swapped_line_pair P d (hordinary P d hf).some

/-- The proved complement geometry feeds the actual reducible-branch
contradiction once quotient containment, the model row, and the two source
pair constructions have been supplied. -/
theorem Context.swapped_false_of_quotient_row (h : Context T L p)
    (o : OrbitFacts T L p) {u : G} (s : Selected T L u)
    {K : Subgroup G} (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L))
    (hquot : Chapter1.XiEmbedding.quotientImage (centralizer ({u} : Set G))
        ((P : Subgroup (XiP p L)).map (XiP p L).subtype) ≤
      Chapter1.XiEmbedding.quotientImage (centralizer ({u} : Set G))
        (componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G))))
    (hrow : SwappedRow p (XiQuotient K))
    (hchar : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      generalizedFitting K = pCore 2 K →
      Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p))
    (hordinary : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      generalizedFitting K ≠ pCore 2 K →
      Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p)) : False := by
  have d := h.swapped_data_of_quotient_row o s e hr P hquot hrow
  by_cases hf : generalizedFitting K = pCore 2 K
  · exact h.false_of_swapped_line_pair P d (hchar d hf).some
  · exact h.false_of_swapped_line_pair P d (hordinary d hf).some

/-- The containment theorem removes the quotient premise from the actual
classification contradiction. Only the row and the two pair producers remain. -/
theorem Context.swapped_false_of_row (h : Context T L p)
    (o : OrbitFacts T L p) {u : G} (s : Selected T L u)
    {K : Subgroup G} (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L))
    (hrow : SwappedRow p (XiQuotient K))
    (hchar : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      generalizedFitting K = pCore 2 K →
      Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p))
    (hordinary : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      generalizedFitting K ≠ pCore 2 K →
      Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p)) : False :=
  h.swapped_false_of_quotient_row o s e hr P
    (h.swapped_quotient_containment o s e hr P) hrow hchar hordinary

/-- Actual 13.1.12(3) consumer, conditional on construction of the swapped
sieve and both pairs, with the separate irreducible branch retained. -/
theorem Context.centralizer_le_of_swapped_geometry (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p)
    (hirr : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u → False)
    (hsieve : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u →
      ∃ P : Sylow p (XiP p L),
        SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hpairs : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u →
      ∀ P : Sylow p (XiP p L),
      SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      (generalizedFitting K = pCore 2 K →
        Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p)) ∧
      (generalizedFitting K ≠ pCore 2 K →
        Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p)))
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  apply h.centralizer_le_of_component_exclusions o c hirr _ hu hne
  intro v sv hv K e hr
  exact h.swapped_false_of_geometry (hsieve v sv hv K e hr)
    (fun P d => (hpairs v sv hv K e hr P d).1)
    (fun P d => (hpairs v sv hv K e hr P d).2)

/-- The complete sieve feeds either literal component-pair construction into
the actual normalizer-action contradiction. -/
theorem Context.swapped_false_of_line_geometry (h : Context T L p)
    (o : OrbitFacts T L p) {u : G} (s : Selected T L u)
    {K : Subgroup G} (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L))
    (hchar : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      generalizedFitting K = pCore 2 K →
      Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p))
    (hordinary : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      generalizedFitting K ≠ pCore 2 K →
      Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p)) : False :=
  h.swapped_false_of_row o s e hr P (h.swapped_row o s e hr P) hchar hordinary

/-- The literal classification consumer with its exchanged-orbit sieve proved.
The separate irreducible branch and the two geometric pair producers remain
with the source-theorem assembly owner. -/
theorem Context.centralizer_le_of_swapped_pairs (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p)
    (hirr : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u → False)
    (hpairs : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u →
      ∀ P : Sylow p (XiP p L),
      SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      (generalizedFitting K = pCore 2 K →
        Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p)) ∧
      (generalizedFitting K ≠ pCore 2 K →
        Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p)))
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  apply h.centralizer_le_of_swapped_geometry o c hirr _ hpairs hu hne
  intro v sv _ K e hr
  exact h.exists_swapped_data o sv e hr


/-- The ordinary branch is excluded with no additional geometric premise. -/
theorem Context.characteristic_two_of_swapped (h : Context T L p)
    (o : OrbitFacts T L p) {u : G} (s : Selected T L u)
    {K : Subgroup G} (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) :
    generalizedFitting K = pCore 2 K := by
  by_contra hf
  obtain ⟨P,d⟩ := h.exists_swapped_data o s e hr
  exact h.swapped_ordinary_false e P d hf

/-- A conditional adapter for the literal C.2.7 input. The final theorem
`Context.swapped_false` below supplies the characteristic-two construction. -/
theorem Context.swapped_false_of_characteristic_two_geometry (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u)
    (hchar : ∀ P : Sylow p (XiP p L),
      SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
        KnownSimple.IsKnownSimple (centralizer ({u} : Set G)) (centralizerCore T L p u)
        (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) K →
      Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p)) : False := by
  obtain ⟨P,d⟩ := h.exists_swapped_data o s e hr
  have hi := h.swapped_characteristic_two_input o c s hnt e hr P d
    (h.characteristic_two_of_swapped o s e hr)
  exact h.false_of_swapped_line_pair P d (hchar P d hi).some

/-- Conditional centralizer-containment adapter for characteristic-two
geometry. The final consumer below discharges this geometric premise. -/
theorem Context.centralizer_le_of_characteristic_two_swapped_geometry (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p)
    (hirr : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u → False)
    (hchar : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ¬ ComponentNormalizerIrreducible L K p u →
      ∀ P : Sylow p (XiP p L),
      SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) →
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
        KnownSimple.IsKnownSimple (centralizer ({u} : Set G)) (centralizerCore T L p u)
        (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) K →
      Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p))
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  apply h.centralizer_le_of_component_exclusions o c hirr _ hu hne
  intro v sv hv K e hr
  exact h.swapped_false_of_characteristic_two_geometry o c sv hv e hr (hchar v sv hv K e hr)


/-- Original 13.1.12(3), the complete reducible component-normalizer branch.
The literal exchanged orbit and both component geometries have been proved;
only the original earlier-source OrbitFacts and Control inputs remain explicit. -/
theorem Context.swapped_false (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p) {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) : False := by
  obtain ⟨P,d⟩ := h.exists_swapped_data o s e hr
  by_cases hf : generalizedFitting K = pCore 2 K
  · exact h.false_of_swapped_line_pair P d
      (h.characteristic_two_line_pair o c s hnt e hr P d hf).some
  · exact h.swapped_ordinary_false e P d hf

/-- The actual 13.1.12(3) centralizer-containment consumer with the entire
swapped branch discharged. Its separate irreducible exclusion remains an
input to the original centralizer theorem's assembly owner. -/
theorem Context.centralizer_le_of_irreducible_exclusion (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p)
    (hirr : ∀ u : G, Selected T L u →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
      ∀ K : Subgroup G, Escape T L p u K → ComponentNormalizerIrreducible L K p u → False)
    {u : G} (hu : u ∈ normalizerMoved L) (hne : u ≠ 1) :
    centralizer ({u} : Set G) ≤ normalizer (L : Set G) := by
  apply h.centralizer_le_of_component_exclusions o c hirr _ hu hne
  intro v sv hv K e hr
  exact h.swapped_false o c sv hv e hr

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
