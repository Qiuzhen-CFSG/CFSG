module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.FixedComplements
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Eigenspaces
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections.RadicalGeometry.Transport


/-!
# The full scalar family in the second source Cartan factor

The original Cartan has order (q - 1)². Its injection into the product of
rank-one Borel quotients is therefore onto; exchanging the factors in the
proved torus-lifting theorem supplies a primitive actor in X intersect L₂.
Right multiplication in the marked orthogonal matrix module gives reciprocal
primitive eigenvalues. Restriction-field transport preserves their orders,
so every nonzero scalar occurs on the invariant field line W₂.

The literal natural action proves [V,L₂] ≤ V₂. Thus X intersect L₂ fixes
the invariant complement W₁, and its scalar on W₂ passes to the actual
commutator W₃ by the displacement formula. All subgroup modules inherit
the canonical compatible field. The final application supplies this family
to the existing obstruction and discharges the independently proved terminal
weights, leaving the first scalar family with qt-d-1222-shadow-compatible-cartan.
The parent qt-d-1222-shadow-linear-geometry retains discharge of the genuine
preceding common-core geometry and independent action markings.

Source: Aschbacher--Smith, Lemma 11.3.9 and the final paragraph of
Proposition 11.3.2, printed p.775; compatible fields are from 11.3.8.
-/

open Subgroup Representation Matrix
open ClassicalOrthogonal.FourPlusMatrix
open scoped MatrixGroups IsMulCommutative
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies
open TerminalWeights

variable {A F : Type*} [Group A] [Finite A] [Field F] [Finite F] [CharP F 2]
local notation "J" => SL(2,F)

/-- The second factor of the actual product torus contains a primitive split actor. -/
theorem exists_split_second_actor
    (q : A →* (J × J)) (hq : Function.Surjective q)
    (R : Sylow 2 A) (hk : q.ker ≤ (R : Subgroup A))
    (X : Subgroup A) (hn : X ≤ normalizer (R : Set A))
    (ho : Odd (Nat.card X)) (hcard : Nat.card X = (Nat.card F - 1)^2)
    (hF : 2 < Nat.card F) :
    ∃ x : X, (q x).1 = 1 ∧ ∃ b : J, ∃ a : F,
      a ≠ 0 ∧ orderOf a = Nat.card F - 1 ∧
      (b * (q x).2 * b⁻¹).val = !![a,0;0,a⁻¹] := by
  let q' := (MulEquiv.prodComm (M := J) (N := J)).toMonoidHom.comp q
  have hq' : Function.Surjective q' := (MulEquiv.prodComm (M := J) (N := J)).surjective.comp hq
  have hk' : q'.ker ≤ (R : Subgroup A) := by
    intro x hx
    apply hk
    have hh : q' x = 1 := hx
    exact Prod.ext (congrArg Prod.snd hh) (congrArg Prod.fst hh)
  obtain ⟨x,hx,_,horder,_⟩ := exists_primitive_first_factor q' hq' R hk' X hn ho hcard
  let q₂ := (MonoidHom.snd J J).comp q
  have hq₂ : Function.Surjective q₂ := by
    intro g
    obtain ⟨y,hy⟩ := hq (1,g)
    exact ⟨y,congrArg Prod.snd hy⟩
  let R₂ := R.mapSurjective hq₂
  have hxn : q₂ x ∈ normalizer (R₂ : Set J) :=
    (R : Subgroup A).le_normalizer_map q₂ (mem_map_of_mem q₂ (hn x.property))
  have hxo : Odd (orderOf (q₂ x)) :=
    ho.of_dvd_nat ((orderOf_map_dvd (q₂.comp X.subtype) x).trans (orderOf_dvd_natCard x))
  have hxne : q₂ x ≠ 1 := by
    intro he
    change orderOf (q₂ x) = Nat.card F - 1 at horder
    rw [he,orderOf_one] at horder
    omega
  obtain ⟨b,a,ha,hao,hab⟩ := split_odd_actor R₂ (q₂ x) hxn hxo hxne
  exact ⟨x,hx,b,a,ha,hao.trans horder,hab⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies
open TerminalWeights Matrix.SpecialLinearGroup
open CFSG.Quasithin.ChapterB.QuasisimpleSource
section Split
variable {G F : Type*} [Group G] [Field F] [Finite F]
    {E : BinaryField} {P Y : Subgroup G} [IsMulCommutative P]
    (o : MarkedSections.OrthogonalMarking E P Y)
    (N : let := o.moduleStructure; NaturalPlane (E := E.Carrier) (F := F) (A := Additive P))
    (hc : Nat.card E.Carrier = Nat.card F)

/-- The right-factor eigenvalues are transported through the canonical restriction field. -/
theorem compatible_second_split_coordinates (y : Y) (hy : (o.actors y).1 = 1)
    (b : SL(2,E.Carrier)) (a : E.Carrier) (ha : a ≠ 0)
    (hdiag : (b * (o.actors y).2 * b⁻¹).val = !![a,0;0,a⁻¹]) :
    let := o.moduleStructure
    let := N.compatibleModule hc
    let φ := N.fieldEquiv hc
    ∃ e : Additive P ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F)),
      ∀ p, e (N.compatibleRepresentation hc o.action y p) =
        ((φ a)⁻¹ • (e p).1, φ a • (e p).2) := by
  let := o.moduleStructure
  let e₀ := o.coordinates.linearEquiv E.Carrier
  let e₁ := e₀.trans (matrixAction (1,b))
  have he₁ (p : Additive P) : e₁ p = e₀ p * b⁻¹.val := by
    change (1 : SL(2,E.Carrier)).val * e₀ p * b⁻¹.val = _
    simp
  have he₀ (p : Additive P) : e₀ (o.action y p) = e₀ p * (o.actors y).2⁻¹.val := by
    have hh : e₀ (o.action y p) = representation (o.actors y) (e₀ p) := e₀.apply_symm_apply _
    rw [hh,representation_apply,hy]
    simp
  have hdg : b * (o.actors y).2 * b⁻¹ = diag2 a ha :=
    Subtype.ext (hdiag.trans (diag2_coe' ha).symm)
  have hdgi : b * (o.actors y).2⁻¹ * b⁻¹ = diag2 a⁻¹ (inv_ne_zero ha) := by
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc, diag2_inv] using congrArg Inv.inv hdg
  have hd : (o.actors y).2⁻¹.val * b⁻¹.val = b⁻¹.val * !![a⁻¹,0;0,a] := by
    have hh := congrArg (fun g : SL(2,E.Carrier) => (b⁻¹ * g).val) hdgi
    simpa only [mul_assoc,inv_mul_cancel_left,Matrix.SpecialLinearGroup.coe_mul,diag2_coe',inv_inv] using hh
  have he (p : Additive P) : e₁ (o.action y p) = e₁ p * !![a⁻¹,0;0,a] := by
    rw [he₁,he₀,mul_assoc,hd,←mul_assoc,←he₁]
  let et := e₁.trans (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) E.Carrier E.Carrier)
  let := N.compatibleModule hc
  let φ := N.fieldEquiv hc
  let ec := compatibleCoordinates N hc et
  let e := ec.trans (LinearEquiv.finTwoArrow F (Fin 2 → F))
  refine ⟨e,fun p => ?_⟩
  apply Prod.ext <;> ext j
  · change φ (e₁ (o.action y p) j 0) = (φ a)⁻¹ * φ (e₁ p j 0)
    rw [he]
    simp [Matrix.mul_apply,Fin.sum_univ_two,mul_comm]
  · change φ (e₁ (o.action y p) j 1) = φ a * φ (e₁ p j 1)
    rw [he]
    simp [Matrix.mul_apply,Fin.sum_univ_two,mul_comm]
end Split

section Line
variable {F M N A : Type*} [Field F] [Finite F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] [Group A]

private theorem exists_power_of_primitive (a : F) (ha : a ≠ 0)
    (ho : orderOf a = Nat.card F - 1) (r : F) (hr : r ≠ 0) :
    ∃ n : ℕ, a^n = r := by
  let u := Units.mk0 a ha
  have ht : zpowers u = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top (zpowers u)).mp
    rw [Nat.card_zpowers,←orderOf_units,Nat.card_units]
    exact ho
  have hm : Units.mk0 r hr ∈ zpowers u := ht ▸ mem_top _
  obtain ⟨n,hn⟩ := (isOfFinOrder_of_finite u).mem_powers_iff_mem_zpowers.mpr hm
  exact ⟨n,congrArg (fun v : Fˣ => (v : F)) hn⟩

/-- An invariant line in two primitive reciprocal eigenspaces has the full scalar spectrum. -/
theorem full_scalars_on_line (ρ : Representation F A M) (x : A)
    (e : M ≃ₗ[F] (N × N)) (a : F) (ha : a ≠ 0)
    (ho : orderOf a = Nat.card F - 1)
    (he : ∀ p, e (ρ x p) = (a⁻¹ • (e p).1, a • (e p).2))
    (W : Submodule F M) (hd : Module.finrank F W = 1)
    (hi : ∀ w ∈ W, ρ x w ∈ W) :
    ∀ r : F, r ≠ 0 → ∃ n : ℕ, ∀ w ∈ W, ρ (x^n) w = r • w := by
  obtain ⟨c,hc,_⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd ((ρ x).restrict hi)
  have hscalar (w : M) (hw : w ∈ W) : ρ x w = c • w :=
    congrArg Subtype.val (LinearMap.congr_fun hc ⟨w,hw⟩)
  obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show W ≠ ⊥ from by
    intro h
    rw [h,finrank_bot] at hd
    omega)
  have hcval : c = a⁻¹ ∨ c = a := by
    have hh := (he w).symm.trans (congrArg e (hscalar w hw))
    rw [map_smul] at hh
    by_cases h₁ : (e w).1 = 0
    · right
      have h₂ : (e w).2 ≠ 0 := by
        intro h₂
        apply hw0
        apply e.injective
        simpa using (Prod.ext h₁ h₂ : e w = 0)
      exact (smul_left_injective F h₂ (congrArg Prod.snd hh)).symm
    · left
      exact (smul_left_injective F h₁ (congrArg Prod.fst hh)).symm
  have hc0 : c ≠ 0 := hcval.elim (fun h => h ▸ inv_ne_zero ha) (fun h => h ▸ ha)
  have hco : orderOf c = Nat.card F - 1 := by
    rcases hcval with rfl | rfl
    · exact (orderOf_units (y := (Units.mk0 a ha)⁻¹)).trans
        ((orderOf_inv (Units.mk0 a ha)).trans ((orderOf_units (y := Units.mk0 a ha)).symm.trans ho))
    · exact ho
  intro r hr
  obtain ⟨n,hn⟩ := exists_power_of_primitive c hc0 hco r hr
  refine ⟨n,fun w hw => ?_⟩
  rw [←hn]
  clear hn
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',map_mul,Module.End.mul_apply,ih,map_smul,hscalar w hw,smul_smul]
    rw [pow_succ,mul_comm]
end Line
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies
open TerminalWeights
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open MarkedSections.RadicalGeometry
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m))

/-- The actual second residual acts trivially on V/V₂. -/
theorem second_residual_movement : ⁅V,f.Li 1⁆ ≤ f.Vi 1 := by
  apply commutator_le.mpr
  intro v hv l hl
  let l' : L := ⟨l,(localResidual_le _ hl).1⟩
  have hq : SL3.PlaneAction.alignedQuotient D S m l' ∈
      Matrix.PSL3.LinearThree.lineLocalSL S.field.Carrier := by
    change SL3.PlaneAction.alignedQuotient D S m l' ∈ SL3.PlaneAction.localGroup 1
    rw [←SL3.PlaneAction.local_image D S m 1]
    apply mem_map_of_mem
    change l ∈ (SL3.flag D S m).Li 1
    simpa only [MarkedSections.flag_eq D S m f] using hl
  obtain ⟨h20,h21,h22⟩ := (Matrix.PSL3.LinearThree.mem_lineLocalSL_iff _ _).mp hq
  obtain ⟨w,hw,he⟩ := alignedVectors_commutator D S m l' ⟨v,hv⟩
  rw [←hw,mem_flag_aligned D S m f 1 w,he]
  change (alignedVectors D S m (Additive.ofMul ⟨v,hv⟩) -
    (SL3.PlaneAction.alignedQuotient D S m l').val.mulVec
      (alignedVectors D S m (Additive.ofMul ⟨v,hv⟩))) 2 = 0
  simp [mulVec,dotProduct,Fin.sum_univ_three,h20,h21,h22]

variable {P I K X : Subgroup G} [IsMulCommutative P] [IsMulCommutative V]
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (E : BinaryField) (o : CommonCore.OrthogonalMarking (f.Li 1 ⊔ I) P K (f.Li 1) E)
    (hcard : Nat.card E.Carrier = Nat.card S.field.Carrier)
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) (hVI : V ≤ I)
    (hX : IsCartan T L X) (hXY : X ≤ f.Li 1 ⊔ I)
    (hPT : P ≤ T) (hTY : (T : Subgroup G) ≤ f.Li 1 ⊔ I)
    (hTL : (T : Subgroup G) ≤ L)

include hX hXY hPT hTY hTL in
/-- Every nonzero scalar occurs on the actual W₂ and W₃ under an element
of X intersect L₂, while that same element fixes W₁. The scalar structure
on P is exactly the one constructed from the restriction field. -/
theorem source_second_scalar_family :
    let := originalModule D (.sl3 m) hfixed
    let s := orderedSection o
    let := s.moduleStructure
    let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
    let := d.compatibleModule hcard
    let σ := d.restrictionDatum.compatibleRepresentation hcard s.action
    ∀ (W₁ : Submodule S.field.Carrier (Additive V))
      (W₂ : Submodule S.field.Carrier (Additive P)),
      IsCompl (originalPlane D (.sl3 m) hfixed f) W₁ →
      Module.finrank S.field.Carrier W₂ = 1 →
      X ≤ normalizer (ambientSubgroup W₁ : Set G) →
      X ≤ normalizer (ambientSubgroup W₂ : Set G) →
    let C := commutatorFieldSpace σ
      ((map_subtype_le _ : ambientSubgroup W₁ ≤ V).trans (hVI.trans le_sup_right)) W₂
    let := subgroupFieldModule W₁ rfl
    let := subgroupFieldModule W₂ rfl
    let := subgroupFieldModule C rfl
    ∀ r : S.field.Carrier, r ≠ 0 → ∃ x ∈ X ⊓ f.Li 1,
      ScalarConjugation (ambientSubgroup W₁) x (1 : S.field.Carrier) ∧
      ScalarConjugation (ambientSubgroup W₂) x r ∧
      ScalarConjugation (ambientSubgroup C) x r := by
  let := originalModule D (.sl3 m) hfixed
  let s := orderedSection o
  let := s.moduleStructure
  let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
  let := d.compatibleModule hcard
  let σ := d.restrictionDatum.compatibleRepresentation hcard s.action
  dsimp only
  intro W₁ W₂ hc₁ hd₂ hn₁ hn₂
  let Y := f.Li 1 ⊔ I
  let R := T.subtype hTY
  let X' := X.subgroupOf Y
  have hk : o.projection.ker ≤ (R : Subgroup Y) := by
    rw [o.kernel]
    exact comap_mono hPT
  have hXT : X ≤ normalizer ((T : Subgroup G) : Set G) := by
    have ht : sourceTL T L = T := inf_eq_left.mpr (hTL.trans le_sup_left)
    simpa only [cartanNormalizer,ht] using hX.1.trans inf_le_right
  have hn : X' ≤ normalizer (R : Set Y) := by
    change X.subgroupOf Y ≤ normalizer ((T : Subgroup G).subgroupOf Y : Set Y)
    rw [←subgroupOf_normalizer_eq hTY]
    exact comap_mono hXT
  have ho : Odd (Nat.card X') := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXY).toEquiv]
    exact hX.odd
  have hcx : Nat.card X' = (Nat.card E.Carrier-1)^2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXY).toEquiv,
      (Coordinates.sl3 m).cartan_card hX,hcard,S.field.card_eq]
  have hE : 2 < Nat.card E.Carrier := by
    rw [hcard]
    have hh := SL3.PlaneAction.field_card D S
    omega
  obtain ⟨x,hx,b,a,ha,hao,hdiag⟩ := exists_split_second_actor o.projection o.surjective
    R hk X' hn ho hcx hE
  have hxL : (x.val : G) ∈ f.Li 1 := by
    have him : o.projection x.val ∈ ((f.Li 1).subgroupOf Y).map o.projection := by
      rw [o.second_factor]
      exact hx
    have hker : o.projection.ker ≤ (f.Li 1).subgroupOf Y := by
      rw [o.kernel]
      exact comap_mono (hP ▸ pCoreIn_le 2 (f.Li 1))
    have hh : x.val ∈ (((f.Li 1).subgroupOf Y).map o.projection).comap o.projection := him
    rwa [comap_map_eq_self hker] at hh
  obtain ⟨e,he⟩ := compatible_second_split_coordinates s d.restrictionDatum hcard
    x.val hx b a ha hdiag
  let φ := d.restrictionDatum.fieldEquiv hcard
  have hφ : φ a ≠ 0 := fun hz => ha (φ.injective (hz.trans φ.map_zero.symm))
  have hφo : orderOf (φ a) = Nat.card S.field.Carrier-1 := by
    exact (orderOf_injective φ.toMonoidHom φ.injective a).trans
      (hao.trans (congrArg (fun n : ℕ => n-1) hcard))
  have hσ (z : Y) (p : Additive P) :
      ((σ z p).toMul : G) = MulAut.conj (z : G) (p.toMul : G) := s.action_conj z p
  have hi : ∀ w ∈ W₂, σ x.val w ∈ W₂ := by
    intro w hw
    apply (mem_ambientSubgroup W₂ (σ x.val w).toMul).mp
    rw [hσ]
    exact (mem_normalizer_iff.mp (hn₂ x.property) _).mp
      ((mem_ambientSubgroup W₂ w.toMul).mpr hw)
  let C := commutatorFieldSpace σ
    ((map_subtype_le _ : ambientSubgroup W₁ ≤ V).trans (hVI.trans le_sup_right)) W₂
  let := subgroupFieldModule W₁ rfl
  let := subgroupFieldModule W₂ rfl
  let := subgroupFieldModule C rfl
  intro r hr
  obtain ⟨n,hnr⟩ := full_scalars_on_line σ x.val e (φ a) hφ hφo he W₂ hd₂ hi r hr
  let z : Y := x.val ^ n
  have hzX : (z : G) ∈ X := X.pow_mem x.property n
  have hzL : (z : G) ∈ f.Li 1 := (f.Li 1).pow_mem hxL n
  have hdis : Disjoint (f.Vi 1) (ambientSubgroup W₁) := by
    simpa only [ambient_originalPlane] using (ambient_complement hc₁).1
  have hcentral := source_second_cartan_centralizes D S f hdis (map_subtype_le _) hn₁
    (second_residual_movement D S m f)
  have hzcomm (w : ambientSubgroup W₁) : Commute (z : G) (w : G) :=
    (hcentral ⟨hzX,hzL⟩ w w.property).symm
  refine ⟨z,⟨hzX,hzL⟩,?_,?_,?_⟩
  · apply (scalarConjugation_iff W₁ rfl _ _).mpr
    intro w hw
    simp only [one_smul,MulAut.conj_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hzcomm ⟨w.toMul,(mem_ambientSubgroup W₁ _).mpr hw⟩).eq
  · apply (scalarConjugation_iff W₂ rfl _ _).mpr
    intro w hw
    rw [←hσ,hnr w hw]
  · exact scalarConjugation_commutatorFieldSpace σ hσ _ W₂ z r hzcomm hnr
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies

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
/-- The actual second scalar family supplies the right-family argument of the
source obstruction; the independently proved terminal weights are also discharged.
The first-family construction remains with this same compatible-Cartan owner. -/
theorem false_of_source_complements_of_first_family
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
    (∀ r : S.field.Carrier, r ≠ 0 → ∃ x ∈ X,
      ScalarConjugation (ambientSubgroup W₁) x r ∧
      ScalarConjugation (ambientSubgroup W₂) x (1 : S.field.Carrier) ∧
      ScalarConjugation (ambientSubgroup C) x r) → False := by
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
  intro hleft
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
  apply false_of_ordered_source_complements D S m f hfixed E o hcard hP hcore hPV hVI
    hX hXY hodd hPK hPT hTY hTL hsize W₁ B W₂ hB hc₁ hc₂ hn₁ hn₂ hleft
  intro r hr
  obtain ⟨x,hx,hxw⟩ := source_second_scalar_family D S m f hfixed E o hcard hP hcore hPV hVI
    hX hXY hPT hTY hTL W₁ W₂ hc₁ hd₂ hn₁ hn₂ r hr
  exact ⟨x,hx.1,hxw⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.ScalarFamilies
