module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections.RadicalGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Bilinear
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights

/-!
# The compatible-field contradiction in the linear shadow

From the preceding literal common-core geometry and ordered natural and
orthogonal action markings, construct the canonical compatible field,
the actual radical hyperplane and invariant complements. The commutator
is nonzero and bilinear by the two linear displacement formulas. The
proved Cartan generator has weights λ², λ and λ⁻¹, contradicting its
primitive order. No scalar-family, pairing, field-compatibility, radical
incidence or terminal-weight premise remains.

The parent qt-d-1222-shadow-linear-geometry retains discharge of the
preceding common-core geometry and independent action markings before
completing Proposition1132At. This theorem is the conditional source
contradiction requested of the compatible-Cartan construction.

Source: Aschbacher--Smith, 11.3.8–9 and Proposition 11.3.2, printed
pp.774–775.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
open TerminalWeights
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) {P I K X : Subgroup G}
    [IsMulCommutative P] [IsMulCommutative V]
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (E : BinaryField) (o : CommonCore.OrthogonalMarking (f.Li 1 ⊔ I) P K (f.Li 1) E)
    (hcard : Nat.card E.Carrier = Nat.card S.field.Carrier)
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) (hVI : V ≤ I)
    (hX : IsCartan T L X) (hXY : X ≤ f.Li 1 ⊔ I)
    (hodd : Odd S.field.degree)
    (hPK : P = K.pCoreIn 2) (hPT : P ≤ T)
    (hTY : (T : Subgroup G) ≤ f.Li 1 ⊔ I) (hTL : (T : Subgroup G) ≤ L)

include hfixed o hcard hP hcore hPV hVI hX hXY hodd hPK hPT hTY hTL in
/-- Source contradiction from only the preceding common-core geometry and its
independent ordered orthogonal marking. The radical geometry, compatible fields,
invariant complements, nonzero bilinear commutator and terminal weights are proved. -/
theorem false_of_ordered_source_geometry : False := by
  let := originalModule D (.sl3 m) hfixed
  let s := orderedSection o
  let := s.moduleStructure
  let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
  let := d.compatibleModule hcard
  let σ := d.restrictionDatum.compatibleRepresentation hcard s.action
  obtain ⟨B,W₁,W₂,hB,_,hc₁,hc₂,_,hd₂,hn₁,hn₂⟩ :=
    MarkedSections.exists_canonical_complements D S m f P I hfixed E s
      hcard hP hcore hPV hVI hX hXY hTL
  have hsize := MarkedSections.RadicalGeometry.radical_intersection_card D S m f P hP hTL hcore hPV
  have hq : 1 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact Nat.one_lt_pow (Nat.ne_of_gt S.field.degree_pos) (by decide)
  have hdis : Disjoint (P ⊓ f.Ri 0) (ambientSubgroup W₂) :=
    hB ▸ (ambient_complement hc₂).1
  have hs₂ : (P ⊓ f.Ri 0) ⊔ ambientSubgroup W₂ = P :=
    hB ▸ (ambient_complement hc₂).2
  have hs₁ : f.Vi 1 ⊔ ambientSubgroup W₁ = V := by
    simpa only [ambient_originalPlane] using (ambient_complement hc₁).2
  have hproper : P ⊓ f.Ri 0 < P := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hh := hsize
    rw [he,s.card,hcard,←S.field.card_eq] at hh
    have hh' := Nat.pow_right_injective hq hh
    omega
  let C := commutatorFieldSpace σ
    ((map_subtype_le _ : ambientSubgroup W₁ ≤ V).trans (hVI.trans le_sup_right)) W₂
  let := subgroupFieldModule W₁ rfl
  let := subgroupFieldModule W₂ rfl
  let := subgroupFieldModule C rfl
  have hσ (z : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P) :
      ((σ z p).toMul : G) = MulAut.conj (z : G) (p.toMul : G) := s.action_conj z p
  have hC : ambientSubgroup C = ⁅ambientSubgroup W₁, ambientSubgroup W₂⁆ :=
    ambient_commutatorFieldSpace σ hσ _ W₂
  have hfixedP := MarkedSections.fixed_plane D S m f P hP hcore
  have hc := source_complement_commutator D S f hPV hfixedP hproper hP
    (hVI.trans le_sup_right) s.normalizes hs₁ hs₂ hn₁ hn₂
  obtain ⟨y,lam,Q,_,hlam,ho,hcompl,hW₂,_,hU,hQ,_⟩ :=
    source_plane_spectrum D S m f hfixed E o hcard hP hcore hPV hVI hX hXY
      hodd hPK hPT hTY hTL W₂ hd₂ hdis hn₂
  obtain ⟨hw₁,hw₂,hw₃⟩ := source_weights_of_planes D S m f hfixed E s hcard
    hP hcore hPV hVI hX hXY W₁ W₂ C Q hc₁ hcompl hW₂
    (hC ▸ hc.2.1) hn₁ y lam⁻¹ lam hlam hU hQ
  have hPL : P ≤ L := hP ▸ (pCoreIn_le 2 (f.Li 1)).trans
    ((localResidual_le _).trans inf_le_left)
  exact false_of_compatible_linear_actions (d.common_smul hcard)
    (MarkedSections.originalRepresentation D (.sl3 m) hfixed)
    (MarkedSections.originalRepresentation_conj D (.sl3 m) hfixed) σ hσ W₁ W₂ C
    ((map_subtype_le _).trans (hVI.trans le_sup_right))
    ((map_subtype_le _).trans hPL) hC
    ((hC ▸ hc.2.1).trans (D.centralQuotientPreimage_le _))
    (hC.symm ▸ hc.1) hn₁ hn₂ S.nonbinary hlam ho ⟨y,y.property.1⟩ hw₁ hw₂ hw₃
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
