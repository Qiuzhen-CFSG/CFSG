module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights.Models
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights.Linear
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Obstruction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Fields
/-!
# Terminal weights over the canonical compatible field

The original SL3 marking and the independent orthogonal marking both have
linear determinant one. The two scalar planes in P therefore have inverse
weights in characteristic two. Agreement on the literal P intersect V
transfers its weight to V2 in the original V; determinant one on V then
gives the square weight on its invariant complementary line. The actual
commutator inherits the inverse weight from V2.

Every scalar on P uses exactly extractedPlaneActions.compatibleModule.
The obstruction application transports the independent orthogonal
coefficients through restrictionDatum.fieldEquiv and constructs the actual
commutator subspace. The two scalar families and the primitive two-plane
spectrum remain explicit. Constructing that spectrum from the ordered
product action remains with this terminal-weight task; these conditional
applications do not complete Proposition 11.3.2.

Source: Aschbacher--Smith, Proposition 11.3.2, final paragraph, printed p.775.
-/

open Subgroup Representation
open scoped IsMulCommutative
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
section Original
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    [IsMulCommutative V] (hfixed : V ⊓ centralizer (L : Set G) = ⊥)

theorem original_det (l : L) :
    let := originalModule D (.sl3 m) hfixed
    LinearMap.det (MarkedSections.originalRepresentation D (.sl3 m) hfixed l) = 1 := by
  let := originalModule D (.sl3 m) hfixed
  let e := (originalCoordinates D (.sl3 m) hfixed).linearEquiv S.field.Carrier
  have he : MarkedSections.originalRepresentation D (.sl3 m) hfixed l =
      e.symm.toLinearMap ∘ₗ (Matrix.toLin' ((Coordinates.sl3 m).quotientMap l).val) ∘ₗ e.toLinearMap := rfl
  dsimp only
  have hd := LinearMap.det_conj (Matrix.toLin' ((Coordinates.sl3 m).quotientMap l).val) e.symm
  simp only [LinearEquiv.symm_symm] at hd
  rw [he,hd,LinearMap.det_toLin']
  exact ((Coordinates.sl3 m).quotientMap l).det_coe
end Original

section Orthogonal
variable {G : Type*} [Group G] [Finite G]
    {E : BinaryField} {P Y : Subgroup G} [IsMulCommutative P]
    (o : MarkedSections.OrthogonalMarking E P Y)

omit [Finite G] in
theorem orthogonal_det (y : Y) :
    let := o.moduleStructure
    LinearMap.det (o.action y) = 1 := by
  let := o.moduleStructure
  let e := o.coordinates.linearEquiv E.Carrier
  have he : o.action y = e.symm.toLinearMap ∘ₗ
      ClassicalOrthogonal.FourPlusMatrix.representation (o.actors y) ∘ₗ e.toLinearMap := rfl
  dsimp only
  have hd := LinearMap.det_conj (ClassicalOrthogonal.FourPlusMatrix.representation (o.actors y)) e.symm
  simp only [LinearEquiv.symm_symm] at hd
  rw [he,hd,matrix_action_det]
end Orthogonal

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) {P I K X : Subgroup G}
    [IsMulCommutative P] [IsMulCommutative V]
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (E : BinaryField) (o : MarkedSections.OrthogonalMarking E P (f.Li 1 ⊔ I : Subgroup G))
    (hcard : Nat.card E.Carrier = Nat.card S.field.Carrier)
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) (hVI : V ≤ I)
    (hX : IsCartan T L X) (hXY : X ≤ f.Li 1 ⊔ I)

include hX

/-- Conditional terminal calculation: the product-action producer supplies the
actor and its two scalar planes. No terminal weight is included in those inputs.
Both determinants and the scalar transport to the original V are proved here. -/
theorem source_weights_of_planes :
    let := originalModule D (.sl3 m) hfixed
    let := o.moduleStructure
    let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E o hP hcore hPV hVI
    let := d.compatibleModule hcard
    let σ := d.restrictionDatum.compatibleRepresentation hcard o.action
    let U := SeparatePlaneActions.fixedPlane (V := V) σ
    ∀ (W₁ : Submodule S.field.Carrier (Additive V))
      (W₂ C Q : Submodule S.field.Carrier (Additive P)),
    IsCompl (originalPlane D (.sl3 m) hfixed f) W₁ → IsCompl U Q → W₂ ≤ Q →
    ambientSubgroup C ≤ f.Vi 1 →
    X ≤ normalizer (ambientSubgroup W₁ : Set G) →
    ∀ (y : (X ⊓ K : Subgroup G)) (a b : S.field.Carrier), b ≠ 0 →
    (∀ p ∈ U, σ ⟨y, hXY y.property.1⟩ p = a • p) →
    (∀ p ∈ Q, σ ⟨y, hXY y.property.1⟩ p = b • p) →
    let := subgroupFieldModule W₁ rfl
    let := subgroupFieldModule W₂ rfl
    let := subgroupFieldModule C rfl
    ScalarConjugation (ambientSubgroup W₁) (y : G) (b ^ 2) ∧
    ScalarConjugation (ambientSubgroup W₂) (y : G) b ∧
    ScalarConjugation (ambientSubgroup C) (y : G) b⁻¹ := by
  let := originalModule D (.sl3 m) hfixed
  let := o.moduleStructure
  let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E o hP hcore hPV hVI
  let := d.compatibleModule hcard
  let σ := d.restrictionDatum.compatibleRepresentation hcard o.action
  let U := SeparatePlaneActions.fixedPlane (V := V) σ
  dsimp only
  intro W₁ W₂ C Q hc₁ hc₂ hW₂ hC hn₁ y a b hb ha hq
  let yp : (f.Li 1 ⊔ I : Subgroup G) := ⟨y,hXY y.property.1⟩
  have hσ (z : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P) :
      ((σ z p).toMul : G) = MulAut.conj (z : G) (p.toMul : G) := o.action_conj z p
  obtain ⟨hU, _, hdU, _⟩ := MarkedSections.common_plane_sections D S m f P I σ hσ
    hP hcore hPV hVI (o.finrank_of_same_field S.field hcard)
  have hdQ : Module.finrank S.field.Carrier Q = 2 := by
    have h := Submodule.finrank_add_eq_of_isCompl hc₂
    rw [hdU,o.finrank_of_same_field S.field hcard] at h
    omega
  have hdetP : LinearMap.det (σ yp) = 1 := by
    change LinearMap.det (d.restrictionDatum.compatibleEnd hcard (o.action yp)) = 1
    rw [compatible_det,orthogonal_det, map_one]
  have hab : a = b⁻¹ := inverse_plane_weight (σ yp) U Q hc₂ hdU hdQ hdetP a b ha hq
  subst a
  let xv : X := ⟨y,y.property.1⟩
  let τ := MarkedSections.cartanRepresentation D (.sl3 m) hfixed hX
  have hτ (v : Additive V) : ((τ xv v).toMul : G) = MulAut.conj (y : G) (v.toMul : G) :=
    MarkedSections.cartanRepresentation_conj D (.sl3 m) hfixed hX xv v
  have hplane : ∀ v ∈ originalPlane D (.sl3 m) hfixed f, τ xv v = b⁻¹ • v := by
    intro v hv
    have hvflag := (mem_originalPlane D (.sl3 m) hfixed f v).mp hv
    have hvP : (v.toMul : G) ∈ P := (hPV.symm ▸ hvflag).1
    let z : Additive (P ⊓ V : Subgroup G) := Additive.ofMul ⟨v.toMul,hvP,v.toMul.property⟩
    let p : Additive P := (inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive z
    have hp : p ∈ U := (mem_ambientSubgroup U p.toMul).mp (hU.symm ▸ hvflag)
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hτ]
    calc
      _ = ((σ yp p).toMul : G) := (hσ yp p).symm
      _ = ((b⁻¹ • p).toMul : G) := congrArg (fun w : Additive P => (w.toMul : G)) (ha p hp)
      _ = ((b⁻¹ • v).toMul : G) := d.common_smul hcard b⁻¹ z
  have hdetV : LinearMap.det (τ xv) = 1 :=
    original_det D S m hfixed (inclusion (hX.1.trans inf_le_left) xv)
  have hi₁ := MarkedSections.invariant_of_normalizes W₁ τ
    (MarkedSections.cartanRepresentation_conj D (.sl3 m) hfixed hX) hn₁ xv
  have hw₁ := square_line_weight (τ xv) (originalPlane D (.sl3 m) hfixed f) W₁ hc₁
    (MarkedSections.originalPlane_finrank D hfixed S m f)
    (MarkedSections.original_complement_finrank D hfixed S m f W₁ hc₁)
    hdetV b hb hplane hi₁
  refine ⟨(scalarConjugation_iff W₁ rfl _ _).mpr ?_,
    (scalarConjugation_iff W₂ rfl _ _).mpr ?_,
    (scalarConjugation_iff C rfl _ _).mpr ?_⟩
  · intro w hw
    rw [←hτ, hw₁ w hw]
  · intro w hw
    rw [←hσ yp, hq w (hW₂ hw)]
  · intro w hw
    have hp : w ∈ U := (mem_ambientSubgroup U w.toMul).mp
      (hU.symm ▸ hC ((mem_ambientSubgroup C w.toMul).mpr hw))
    rw [←hσ yp, ha w hp]
/-- Apply the terminal calculation to the actual commutator obstruction.
The two independent scalar families and the geometric plane spectrum remain
explicit. The eigenvalue is transported from the separate orthogonal field. -/
theorem false_of_source_separate_planes
    (hproper : P ⊓ f.Ri 0 < P) :
    let := originalModule D (.sl3 m) hfixed
    let := o.moduleStructure
    let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E o hP hcore hPV hVI
    let := d.compatibleModule hcard
    let σ := d.restrictionDatum.compatibleRepresentation hcard o.action
    let U := SeparatePlaneActions.fixedPlane (V := V) σ
    ∀ (W₁ : Submodule S.field.Carrier (Additive V))
      (W₂ Q : Submodule S.field.Carrier (Additive P)),
    IsCompl (originalPlane D (.sl3 m) hfixed f) W₁ → IsCompl U Q → W₂ ≤ Q →
    (P ⊓ f.Ri 0) ⊔ ambientSubgroup W₂ = P →
    X ≤ normalizer (ambientSubgroup W₁ : Set G) →
    X ≤ normalizer (ambientSubgroup W₂ : Set G) →
    ∀ (y : (X ⊓ K : Subgroup G)) (a b : E.Carrier), b ≠ 0 →
    orderOf b = 2 ^ S.field.degree - 1 →
    (∀ p ∈ U, o.action ⟨y, hXY y.property.1⟩ p = a • p) →
    (∀ p ∈ Q, o.action ⟨y, hXY y.property.1⟩ p = b • p) →
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
  let := o.moduleStructure
  let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E o hP hcore hPV hVI
  let := d.compatibleModule hcard
  let σ := d.restrictionDatum.compatibleRepresentation hcard o.action
  let U := SeparatePlaneActions.fixedPlane (V := V) σ
  dsimp only
  intro W₁ W₂ Q hc₁ hc₂ hW₂ hs₂ hn₁ hn₂ y a b hb horder ha hq
  let C := commutatorFieldSpace σ
    ((map_subtype_le _ : ambientSubgroup W₁ ≤ V).trans (hVI.trans le_sup_right)) W₂
  let := subgroupFieldModule W₁ rfl
  let := subgroupFieldModule W₂ rfl
  let := subgroupFieldModule C rfl
  intro hleft hright
  have hσ (z : (f.Li 1 ⊔ I : Subgroup G)) (p : Additive P) :
      ((σ z p).toMul : G) = MulAut.conj (z : G) (p.toMul : G) := o.action_conj z p
  have hC : ambientSubgroup C = ⁅ambientSubgroup W₁, ambientSubgroup W₂⁆ :=
    ambient_commutatorFieldSpace σ hσ _ W₂
  have hs₁ : f.Vi 1 ⊔ ambientSubgroup W₁ = V := by
    simpa only [ambient_originalPlane] using (ambient_complement hc₁).2
  have hfixedP := MarkedSections.fixed_plane D S m f P hP hcore
  have hc := source_complement_commutator D S f hPV hfixedP hproper hP
    (hVI.trans le_sup_right) o.normalizes hs₁ hs₂ hn₁ hn₂
  let e := d.restrictionDatum.fieldEquiv hcard
  have hb' : e b ≠ 0 := (map_ne_zero e).mpr hb
  have ho' : orderOf (e b) = 2 ^ S.field.degree - 1 :=
    (compatible_orderOf d.restrictionDatum hcard b).trans horder
  have ha' : ∀ p ∈ U, σ ⟨y,hXY y.property.1⟩ p = e a • p := by
    intro p hp
    exact compatible_eigenvalue d.restrictionDatum hcard _ a p (ha p hp)
  have hq' : ∀ p ∈ Q, σ ⟨y,hXY y.property.1⟩ p = e b • p := by
    intro p hp
    exact compatible_eigenvalue d.restrictionDatum hcard _ b p (hq p hp)
  obtain ⟨hw₁,hw₂,hw₃⟩ := source_weights_of_planes D S m f hfixed E o hcard
    hP hcore hPV hVI hX hXY W₁ W₂ C Q hc₁ hc₂ hW₂
    (hC ▸ hc.2.1) hn₁ y (e a) (e b) hb' ha' hq'
  exact false_of_source_complements D S f hPV hfixedP hproper hP
    (hVI.trans le_sup_right) o.normalizes W₁ W₂ C hC hs₁ hs₂ hn₁ hn₂
    hleft hright (e b) hb' ho' ⟨y,y.property.1⟩ hw₁ hw₂ hw₃
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
