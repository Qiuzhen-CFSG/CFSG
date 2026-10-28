module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights.GeneratorSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights.CommonPlane
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights.Spectrum
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights.PlaneSource
/-!
# Terminal application to the actual commutator obstruction

The literal radical hyperplane and its invariant field complement determine
W2's dimension. The constructed generator and eigenspaces supply the terminal
weights: square on W1, direct on W2, and inverse on their actual nonzero
commutator W3. This discharges every terminal argument of
false_of_source_complements using exactly the canonical compatible field.

The two scalar families from 11.3.9 remain explicit independent inputs. The
preceding common-core and marked-section geometry retain their authorized
source owners; qt-d-1222-shadow-compatible-cartan retains final assembly and
discharge of these earlier inputs and the two scalar families. This is the
terminal theorem-family consumer, not an unconditional proof of 11.3.2.

Source: Aschbacher--Smith, Proposition 11.3.2, final paragraph, printed p.775.
-/

open Subgroup Representation
open scoped IsMulCommutative
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
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

include hX hXY hodd hPK hPT hTY hTL in
/-- Terminal source contradiction from the genuine ordered markings and
actual field complements. Only the two independently owned scalar families
remain as terminal action inputs. -/
theorem false_of_ordered_source_complements
    (hsize : Nat.card (P ⊓ f.Ri 0 : Subgroup G) = (2 ^ S.field.degree) ^ 3) :
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
    (∀ r : S.field.Carrier, r ≠ 0 → ∃ x ∈ X,
      ScalarConjugation (ambientSubgroup W₁) x r ∧
      ScalarConjugation (ambientSubgroup W₂) x (1 : S.field.Carrier) ∧
      ScalarConjugation (ambientSubgroup C) x r) →
    (∀ r : S.field.Carrier, r ≠ 0 → ∃ x ∈ X,
      ScalarConjugation (ambientSubgroup W₁) x (1 : S.field.Carrier) ∧
      ScalarConjugation (ambientSubgroup W₂) x r ∧
      ScalarConjugation (ambientSubgroup C) x r) → False := by
  let := originalModule D (.sl3 m) hfixed
  let s := orderedSection o
  let := s.moduleStructure
  let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
  let := d.compatibleModule hcard
  let σ := d.restrictionDatum.compatibleRepresentation hcard s.action
  dsimp only
  intro W₁ B W₂ hB hc₁ hc₂ hn₁ hn₂
  have hq : 1 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact Nat.one_lt_pow (Nat.ne_of_gt S.field.degree_pos) (by decide)
  have hdB : Module.finrank S.field.Carrier B = 3 := by
    have hcardB := Nat.card_congr (subgroupFieldCoordinates B rfl).toEquiv
    change Nat.card (ambientSubgroup B) = Nat.card B at hcardB
    rw [hB,hsize,Module.natCard_eq_pow_finrank (K := S.field.Carrier) (V := B),
      ← S.field.card_eq] at hcardB
    exact (Nat.pow_right_injective hq hcardB).symm
  have hd₂ : Module.finrank S.field.Carrier W₂ = 1 := by
    have hh := Submodule.finrank_add_eq_of_isCompl hc₂
    rw [hdB,s.finrank_of_same_field S.field hcard] at hh
    omega
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
  intro hleft hright
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
  exact false_of_source_complements D S f hPV hfixedP hproper hP
    (hVI.trans le_sup_right) s.normalizes W₁ W₂ C hC hs₁ hs₂ hn₁ hn₂
    hleft hright lam hlam ho ⟨y,y.property.1⟩ hw₁ hw₂ hw₃
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
