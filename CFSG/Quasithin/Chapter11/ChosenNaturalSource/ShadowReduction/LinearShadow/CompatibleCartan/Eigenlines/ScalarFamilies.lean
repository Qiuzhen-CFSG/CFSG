module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.ScalarFamilies.First
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections.RadicalGeometry

/-!
# Assembly of the two source scalar families

Both literal Cartan factors now supply their full scalar families over
the canonical compatible field. Apply them to the existing commutator
obstruction with the independently constructed terminal generator and
weights. The final theorem also constructs the actual invariant
complements and their radical hyperplane, leaving only genuine preceding
source geometry and action markings.

The parent qt-d-1222-shadow-linear-geometry must discharge those preceding
premises before completing Proposition1132At.

Source: Aschbacher--Smith, 11.3.8--9 and the final paragraph of
Proposition 11.3.2, printed pp.774--775.
-/

open Subgroup Representation
open scoped IsMulCommutative
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies
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
    (hodd : Odd S.field.degree) (hPK : P = K.pCoreIn 2)
    (hPT : P ≤ T) (hTY : (T : Subgroup G) ≤ f.Li 1 ⊔ I)
    (hTL : (T : Subgroup G) ≤ L)

include hX hXY hodd hPK hPT hTY hTL in
/-- Both constructed scalar families and the independent terminal weights
supply the actual source obstruction on the canonical compatible field. -/
theorem false_of_source_complements
    (hsize : Nat.card (P ⊓ f.Ri 0 : Subgroup G) = (2 ^ S.field.degree)^3) :
    let := originalModule D (.sl3 m) hfixed
    let s := orderedSection o
    let := s.moduleStructure
    let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
    let := d.compatibleModule hcard
    let σ := d.restrictionDatum.compatibleRepresentation hcard s.action
    ∀ (W₁ : Submodule S.field.Carrier (Additive V))
      (B W₂ : Submodule S.field.Carrier (Additive P)),
      ambientSubgroup B = P ⊓ f.Ri 0 →
      IsCompl (originalPlane D (.sl3 m) hfixed f) W₁ → IsCompl B W₂ →
      X ≤ normalizer (ambientSubgroup W₁ : Set G) →
      X ≤ normalizer (ambientSubgroup W₂ : Set G) →
    let C := commutatorFieldSpace σ
      ((map_subtype_le _ : ambientSubgroup W₁ ≤ V).trans (hVI.trans le_sup_right)) W₂
    let := subgroupFieldModule W₁ rfl
    let := subgroupFieldModule W₂ rfl
    let := subgroupFieldModule C rfl
    False := by
  let := originalModule D (.sl3 m) hfixed
  let s := orderedSection o
  let := s.moduleStructure
  let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
  let := d.compatibleModule hcard
  let σ := d.restrictionDatum.compatibleRepresentation hcard s.action
  dsimp only
  intro W₁ B W₂ hB hc₁ hc₂ hn₁ hn₂
  let C := commutatorFieldSpace σ
    ((map_subtype_le _ : ambientSubgroup W₁ ≤ V).trans (hVI.trans le_sup_right)) W₂
  let := subgroupFieldModule W₁ rfl
  let := subgroupFieldModule W₂ rfl
  let := subgroupFieldModule C rfl
  have hq : 1 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact Nat.one_lt_pow (Nat.ne_of_gt S.field.degree_pos) (by decide)
  have hdB : Module.finrank S.field.Carrier B = 3 := by
    have hb := Nat.card_congr (subgroupFieldCoordinates B rfl).toEquiv
    change Nat.card (ambientSubgroup B) = Nat.card B at hb
    rw [hB,hsize,Module.natCard_eq_pow_finrank (K := S.field.Carrier) (V := B),
      ←S.field.card_eq] at hb
    exact (Nat.pow_right_injective hq hb).symm
  have hd₂ : Module.finrank S.field.Carrier W₂ = 1 := by
    have hh := Submodule.finrank_add_eq_of_isCompl hc₂
    rw [hdB,s.finrank_of_same_field S.field hcard] at hh
    omega
  apply false_of_source_complements_of_first_family D S m f hfixed E o hcard
    hP hcore hPV hVI hX hXY hodd hPK hPT hTY hTL hsize W₁ B W₂ hB hc₁ hc₂ hn₁ hn₂
  intro r hr
  obtain ⟨x,hx,hxw⟩ := source_first_scalar_family D S m f hfixed E o hcard hP hcore hPV hVI
    hX hXY hodd hPK hPT hTY hTL W₁ W₂ hc₁ hd₂
    (hB ▸ (ambient_complement hc₂).1) hn₁ hn₂ r hr
  exact ⟨x,hx.1,hxw⟩

include hfixed o hcard hP hcore hPV hVI hX hXY hodd hPK hPT hTY hTL in
/-- All first-family, second-family, terminal-spectrum and complement premises
are discharged. Only the preceding source geometry and its markings remain;
qt-d-1222-shadow-linear-geometry owns their final source discharge. -/
theorem false_of_source_geometry : False := by
  let := originalModule D (.sl3 m) hfixed
  let s := orderedSection o
  let := s.moduleStructure
  let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
  let := d.compatibleModule hcard
  obtain ⟨B,W₁,W₂,hB,_,hc₁,hc₂,_,_,hn₁,hn₂⟩ :=
    MarkedSections.exists_canonical_complements D S m f P I hfixed E s
      hcard hP hcore hPV hVI hX hXY hTL
  exact false_of_source_complements D S m f hfixed E o hcard hP hcore hPV hVI
    hX hXY hodd hPK hPT hTY hTL
    (MarkedSections.RadicalGeometry.radical_intersection_card D S m f P hP hTL hcore hPV)
    W₁ B W₂ hB hc₁ hc₂ hn₁ hn₂

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies
