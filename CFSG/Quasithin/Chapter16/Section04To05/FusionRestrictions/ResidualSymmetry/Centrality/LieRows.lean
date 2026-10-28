module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.HigherLinear
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.QuotientActions
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.LinearThree
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.Symplectic
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.TrialityRee
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.G2Complete

/-!
# Lie-family separation for the comparison in 16.5.6(4)

A central and a noncentral involutory actor have nonisomorphic modified
residuals in every surviving characteristic-two family. The comparison uses
solvability and a small odd divisor in PSL₃, two-parts for the symplectic,
higher-linear and G₂ rows, Sylow containment for genuine triality and Ree,
and five-parts for Tits. The literal O³ modification is retained throughout.

`EarlierTables` collects universal statements about actual model actions,
fixed groups, residual extensions and individual Sylow markings.
`CoveringInputs` records the familywise consequences of 16.1.2. These are
explicit earlier source inputs to this conditional comparison, not proved
source theorems or separation assumptions. The source 16.5.6 assembly must
supply them. Every rank-two constructor, central cover and derived endpoint
is retained; the binary symplectic endpoint is excluded only through its
actual A₆ equivalence and the supplied source exclusion. The PSL₅(2) j₂
row uses the corrected order-256 kernel.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.2–4,6,
printed pp.1170–1172; I.2.2, pp.409–411; and 16.5.5–6(4), p.1197.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows
open Subgroup Theory.GroupTheory
open ClassificationModels
open SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional

/-- Universal earlier tables on concrete carriers. No field compares two
actors or asserts centrality transfer from isomorphic residuals. -/
structure EarlierTables : Prop where
  linear_three : LinearThreeInvolutionTable
  symplectic : SymplecticInvolutionTable
  symplectic_markings : Symplectic.CentralityTable
  g2 : G2InvolutionTable
  g2_roots : G2Complete.RootTable
  g2_binary : BinaryG2InvolutionRows
  g2_binary_markings : G2Complete.BinaryMarkings
  triality : TrialityInvolutionTable
  triality_roots : ∀ (f : ℕ) (hf : 0 < f), TrialityRee.TrialityRootInputs f hf
  ree : ReeInvolutionTable
  ree_roots : ∀ m : ℕ, 1 ≤ m → TrialityRee.ReeRootInputs m
  tits : TitsInvolutionInputs
  tits_roots : TrialityRee.TitsRootInputs
  higher_linear : HigherLinear.InvolutionTable

variable {G : Type*} [Group G] {L : Subgroup G}

/-- The precise familywise covering clauses consumed from 16.1.2 after the
source exclusions. The G₂(4) double cover remains possible. No isomorphism
of an upstairs residual with its central image is assumed. -/
structure CoveringInputs (L : Subgroup G) : Prop where
  symplectic : ∀ f : ℕ, 2 ≤ f →
    ClassicalGroup.IsPSp (L ⧸ center L) 2 (2 ^ f) → center L = ⊥
  symplectic_binary : Nonempty ((L ⧸ center L) ≃*
    commutator (ClassicalGroup.PSp 2 (ZMod 2))) → center L = ⊥
  g2 : ∀ f : ℕ, 2 ≤ f → IsG2At (L ⧸ center L) (2 ^ f) →
    Nat.card (center L) ≤ 2
  g2_binary : Nonempty ((L ⧸ center L) ≃*
    commutator (Atlas.G2.Model (ZMod 2))) → center L = ⊥
  triality : ∀ f : ℕ, 1 ≤ f →
    Triality.Standard.IsTrialityGroupAt (2 ^ f) (L ⧸ center L) → center L = ⊥
  ree : ∀ m : ℕ, 1 ≤ m → Nonempty ((L ⧸ center L) ≃* ReeF4.Model m) → center L = ⊥
  tits : Nonempty ((L ⧸ center L) ≃* Tits.ParrottGroup) → center L = ⊥
  higher_linear : ∀ n : ℕ, n = 4 ∨ n = 5 →
    ClassicalGroup.IsPSL (L ⧸ center L) n 2 → center L = ⊥

variable [Finite G] [IsQuasisimple L]

/-- The complete surviving characteristic-two comparison, conditional only
on the displayed genuine earlier tables and covering clauses. This theorem
does not assert the four-clause source equivalence before those inputs and
the common-residual geometry have been supplied by its assembly owner. -/
theorem separation (tables : EarlierTables) (covers : CoveringInputs L)
    (hodd : pPrimeCore 2 L = ⊥) (hLie : IsEvenTypeLieComponent L)
    (hBender : ¬ ClassificationModels.IsBenderModel (L ⧸ center L))
    (hA6 : ¬ Nonempty (L ≃* alternatingGroup (Fin 6)))
    (hfour : ¬ ClassicalGroup.IsPSL (L ⧸ center L) 3 4)
    (u v : normalizer (L : Set G))
    (huAmbient : orderOf u.val = 2) (hvAmbient : orderOf v.val = 2)
    (hu2 : orderOf (actionMap le_rfl u) = 2)
    (hv2 : orderOf (actionMap le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  rcases surviving_quotient_models hodd hLie hBender with ⟨f, model⟩ | ⟨n, hn, model⟩
  · cases model with
    | linear hf model =>
      exact LinearThree.separation tables.linear_three hodd hLie hBender hA6
        hf model hfour u v huAmbient hvAmbient hu2 hv2 hu hv
    | symplectic hf model =>
      exact Symplectic.separation tables.symplectic tables.symplectic_markings
        (covers.symplectic f hf model) hf model u v hu2 hv2 hu hv
    | g2 hf model =>
      exact G2Complete.separation tables.g2 tables.g2_roots hodd
        (covers.g2 f hf model) hf model u v hu2 hv2 hu hv
    | triality hf model =>
      exact TrialityRee.triality_separation tables.triality tables.triality_roots
        (covers.triality f hf model) hf model u v hu2 hv2 hu hv
    | ree_f4 m hm _ model =>
      obtain ⟨e⟩ := model
      exact TrialityRee.ree_separation tables.ree tables.ree_roots
        (covers.ree m hm ⟨e⟩) hm e u v hu2 hv2 hu hv
    | symplectic_derived _ model =>
      obtain ⟨e⟩ := model
      exact (Symplectic.binary_derived_excluded (covers.symplectic_binary ⟨e⟩) hA6 e).elim
    | g2_derived _ model =>
      obtain ⟨e⟩ := model
      exact G2Complete.separation_binary tables.g2_binary tables.g2_binary_markings
        hodd (covers.g2_binary ⟨e⟩) e u v hu2 hv2 hu hv
    | tits _ model =>
      obtain ⟨e⟩ := model
      exact TrialityRee.tits_separation tables.tits tables.tits_roots
        (covers.tits ⟨e⟩) e u v hu2 hv2 hu hv
  · exact HigherLinear.separation tables.higher_linear (covers.higher_linear n hn model)
      hn model u v hu2 hv2 hu hv

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows
