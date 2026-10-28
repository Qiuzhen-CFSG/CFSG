module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections.RadicalGeometry.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Structures

/-!
# Constructing the actual compatible Cartan complements

The proved radical incidence and order discharge the remaining premises
of the marked-section complement constructor. The canonical variant
constructs the hyperplane and both invariant complements over exactly
extractedPlaneActions.compatibleModule, as used by the terminal weights.
Only the preceding common-core geometry and independent markings remain.

Source: Aschbacher--Smith, 11.3.8 and the complement paragraph, printed
pp.774–775. The actual sections are V₂ and P/V₂.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections
section Assembly
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) (P I : Subgroup G)
    [IsMulCommutative P] [IsMulCommutative V]
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (E : BinaryField) (d : OrthogonalMarking E P (f.Li 1 ⊔ I : Subgroup G))

include d in
/-- Construct the source complements directly from the preceding common-core
geometry and independent action marking. The literal radical incidence and order
are proved here, rather than supplied as premises. -/
theorem exists_compatible_complements
    (hcard : Nat.card E.Carrier = 2 ^ S.field.degree)
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) (hVI : V ≤ I)
    {X : Subgroup G} (hX : IsCartan T L X) (hXY : X ≤ f.Li 1 ⊔ I)
    (hTL : (T : Subgroup G) ≤ L)
    :
    let := originalModule D (.sl3 m) hfixed
    ∃ mP : Module S.field.Carrier (Additive P),
      let := mP
      ∃ ρ : Representation S.field.Carrier (f.Li 1 ⊔ I : Subgroup G) (Additive P),
      ∃ U : Submodule S.field.Carrier (Additive P),
      ∃ B : Submodule S.field.Carrier (Additive P),
      ∃ W₁ : Submodule S.field.Carrier (Additive V),
      ∃ W₂ : Submodule S.field.Carrier (Additive P),
        (∀ (y : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P),
          ((ρ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G)) ∧
        (∀ (a : S.field.Carrier) (b : Additive (P ⊓ V : Subgroup G)),
          ((a • (inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
          ((a • (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G)) ∧
        ambientSubgroup U = f.Vi 1 ∧
        U.toAddSubgroup.toSubgroup = (f.Vi 1).subgroupOf P ∧
        Module.finrank S.field.Carrier U = 2 ∧
        Module.finrank S.field.Carrier ((Additive P) ⧸ U) = 2 ∧
        U ≤ B ∧
        ambientSubgroup B = P ⊓ f.Ri 0 ∧ Module.finrank S.field.Carrier B = 3 ∧
        P ⊓ f.Ri 0 < P ∧ X ≤ normalizer (ambientSubgroup B : Set G) ∧
        IsCompl (originalPlane D (.sl3 m) hfixed f) W₁ ∧ IsCompl B W₂ ∧
        Module.finrank S.field.Carrier W₁ = 1 ∧ Module.finrank S.field.Carrier W₂ = 1 ∧
        Disjoint (f.Vi 1) (ambientSubgroup W₁) ∧ f.Vi 1 ⊔ ambientSubgroup W₁ = V ∧
        Disjoint (P ⊓ f.Ri 0) (ambientSubgroup W₂) ∧
        (P ⊓ f.Ri 0) ⊔ ambientSubgroup W₂ = P ∧
        X ≤ normalizer (ambientSubgroup W₁ : Set G) ∧
        X ≤ normalizer (ambientSubgroup W₂ : Set G) ∧
        X ≤ normalizer ((⁅ambientSubgroup W₁, ambientSubgroup W₂⁆ : Subgroup G) : Set G) := by
  obtain ⟨v,_,hinc⟩ := RadicalGeometry.exists_radical_incidence D S m f P hP hTL
  exact exists_compatible_complements_of_radical_geometry D S m f P I hfixed E d
    hcard hP hcore hPV hVI hX hXY hTL v hinc
    (RadicalGeometry.radical_intersection_card D S m f P hP hTL hcore hPV)
end Assembly
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) (P I : Subgroup G)
    [IsMulCommutative P] [IsMulCommutative V]
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (E : BinaryField) (s : OrthogonalMarking E P (f.Li 1 ⊔ I : Subgroup G))

/-- The source complements over the exact restriction field used by the terminal
weights. No radical incidence, order, or field-subspace premise is assumed. -/
theorem exists_canonical_complements
    (hcard : Nat.card E.Carrier = Nat.card S.field.Carrier)
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) (hVI : V ≤ I)
    {X : Subgroup G} (hX : IsCartan T L X) (hXY : X ≤ f.Li 1 ⊔ I)
    (hTL : (T : Subgroup G) ≤ L) :
    let := originalModule D (.sl3 m) hfixed
    let := s.moduleStructure
    let d := extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
    let := d.compatibleModule hcard
    ∃ (B : Submodule S.field.Carrier (Additive P))
      (W₁ : Submodule S.field.Carrier (Additive V))
      (W₂ : Submodule S.field.Carrier (Additive P)),
      ambientSubgroup B = P ⊓ f.Ri 0 ∧
      Module.finrank S.field.Carrier B = 3 ∧
      IsCompl (originalPlane D (.sl3 m) hfixed f) W₁ ∧ IsCompl B W₂ ∧
      Module.finrank S.field.Carrier W₁ = 1 ∧
      Module.finrank S.field.Carrier W₂ = 1 ∧
      X ≤ normalizer (ambientSubgroup W₁ : Set G) ∧
      X ≤ normalizer (ambientSubgroup W₂ : Set G) := by
  let := originalModule D (.sl3 m) hfixed
  let := s.moduleStructure
  let d := extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
  let := d.compatibleModule hcard
  let σ := d.restrictionDatum.compatibleRepresentation hcard s.action
  have hσ (y : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P) :
      ((σ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G) := s.action_conj y p
  obtain ⟨v,_,hinc⟩ := RadicalGeometry.exists_radical_incidence D S m f P hP hTL
  have hv : (v : G) ∈ f.Li 1 ⊔ I := (hVI.trans le_sup_right) v.property
  let B := radicalHyperplane D S m f P I hfixed (d.common_smul hcard) σ v hv
  have hB : ambientSubgroup B = P ⊓ f.Ri 0 :=
    ambient_radicalHyperplane D S m f P I hfixed (d.common_smul hcard) σ hσ v hv hinc
  have hdimB : Module.finrank S.field.Carrier B = 3 := by
    have hq : 1 < Nat.card S.field.Carrier := by
      rw [S.field.card_eq]
      exact Nat.one_lt_pow (Nat.ne_of_gt S.field.degree_pos) (by decide)
    have hc := Nat.card_congr (subgroupFieldCoordinates B rfl).toEquiv
    change Nat.card (ambientSubgroup B) = Nat.card B at hc
    rw [hB,RadicalGeometry.radical_intersection_card D S m f P hP hTL hcore hPV,
      Module.natCard_eq_pow_finrank (K := S.field.Carrier) (V := B),← S.field.card_eq] at hc
    exact (Nat.pow_right_injective hq hc).symm
  let σX := σ.comp (inclusion hXY)
  have hσX (x : X) (p : Additive P) :
      ((σX x p).toMul : G) = MulAut.conj (x : G) (p.toMul : G) := hσ _ p
  have hXB : X ≤ normalizer (ambientSubgroup B : Set G) := by
    rw [hB]
    exact (le_inf (hXY.trans s.normalizes) (cartan_normalizes_radical D S m f hX hTL 0)).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨W₁,W₂,hc₁,hc₂,_,_,_,_,hn₁,hn₂,_⟩ :=
    exists_source_complements D S f P X hX
      (cartanRepresentation D (.sl3 m) hfixed hX) σX
      (cartanRepresentation_conj D (.sl3 m) hfixed hX) hσX
      (originalPlane D (.sl3 m) hfixed f) B (ambient_originalPlane D (.sl3 m) hfixed f)
      hB (originalPlane_invariant D hfixed S m f hX) (invariant_of_normalizes B σX hσX hXB)
  have hd₂ : Module.finrank S.field.Carrier W₂ = 1 := by
    have hh := Submodule.finrank_add_eq_of_isCompl hc₂
    rw [hdimB,s.finrank_of_same_field S.field hcard] at hh
    omega
  exact ⟨B,W₁,W₂,hB,hdimB,hc₁,hc₂,
    original_complement_finrank D hfixed S m f W₁ hc₁,hd₂,hn₁,hn₂⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections
