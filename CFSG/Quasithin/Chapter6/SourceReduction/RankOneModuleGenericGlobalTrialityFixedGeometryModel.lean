module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityPositiveAction
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers
import all Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Unipotent.MatrixEntries
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterFixed
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterTorus

/-!
# Fixed-root geometry for the triality outer involution

The actual torus--coefficient action is diagonal on the six folded positive
roots and on the arms radical. Its fixed parameters span the radical's
parameter space over the base field: a coefficient involution restricts
nontrivially through the odd cubic extension, and the two fixed vectors
v + rho(v) and b v + sigma(b) rho(v) recover every v. This includes q=4.

A nonzero fixed central-simple parameter kills the first arm coordinate
of a commuting positive element, using the existing Geck matrix entry.
The alternating cubic-trace commutator is base-field bilinear, so its
kernel contains every radical parameter once it contains the fixed ones.
Thus the positive centralizer of the fixed subgroup lies in the highest
root. Two nonzero fixed singleton parameters have nonzero commutator,
proving the fixed subgroup nonabelian. Only involutivity on U is required.

Source: Aschbacher--Smith F.4.37, printed pp.293--294
(`refs/quasithin.pdf`); GLS3 §§2.4--2.6 for the genuine folded root coordinates.
The source companion transports this geometry through the original right
parabolic map. Internal imports reuse the existing scalar matrix entry and
torus weights without enlarging their public boundaries.
-/

open Subgroup Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.PositiveCoordinates
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.OuterOdd Triality.Standard.OuterOdd.Coverage
open Triality.Standard.CentralCovers.TwoPrimary
open CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityFixedGeometry

private theorem fixed_span {k V : Type*} [Field k] [CharP k 2]
    [AddCommGroup V] [Module k V]
    (σ : k ≃+* k) (hσ : Function.Involutive σ)
    (b : k) (hb : b ≠ σ b)
    (ρ : V →+ V) (hρ : Function.Involutive ρ)
    (hsemi : ∀ c x, ρ (c • x) = σ c • ρ x)
    (W : Submodule k V) (hW : ∀ x, ρ x = x → x ∈ W) : W = ⊤ := by
  apply top_unique
  intro x _
  have hu : x + ρ x ∈ W := hW _ (by rw [map_add,hρ]; exact add_comm _ _)
  have hw : b • x + σ b • ρ x ∈ W := hW _ (by
    rw [map_add,hsemi,hsemi,hσ,hρ]; exact add_comm _ _)
  have hsum : (b + σ b) • x ∈ W := by
    have hh := W.add_mem hw (W.smul_mem (σ b) hu)
    have he : b • x + σ b • ρ x + σ b • (x + ρ x) = (b + σ b) • x := by
      rw [smul_add,add_smul]
      have hzero : σ b • ρ x + σ b • ρ x = 0 := by
        rw [←add_smul,CharTwo.add_self_eq_zero,zero_smul]
      calc
        _ = (b • x + σ b • x) + (σ b • ρ x + σ b • ρ x) := by abel
        _ = _ := by rw [hzero,add_zero]
    exact he ▸ hh
  have hne : b + σ b ≠ 0 := by
    intro he
    exact hb ((eq_neg_of_add_eq_zero_left he).trans (CharTwo.neg_eq _))
  simpa only [smul_smul,inv_mul_cancel₀ hne,one_smul] using W.smul_mem (b + σ b)⁻¹ hsum

private theorem commuting_arm_entry (F : Type*) [Field F] [CharP F 2]
    (A : Matrix Index Index F) (b : F) (hb : b ≠ 0)
    (h : Commute A (matrixCurve 13 b)) : A (.inl 0) (.inr 2) = 0 := by
  have hr (r : Index) : matrixCurve 13 b (.inl 0) r =
      (1 : Matrix Index Index F) (.inl 0) r := by
    obtain ⟨hl, hq⟩ := UnipotentMatrices.central_row_check r
    simp [matrixCurve, RingHom.mapMatrix_apply, hl, hq]
  have hc (r : Index) : matrixCurve 13 b r (.inr 6) =
      (1 : Matrix Index Index F) r (.inr 6) + if r = .inr 2 then b else 0 := by
    obtain ⟨hl, hq⟩ := UnipotentMatrices.central_column_check r
    simp [matrixCurve, RingHom.mapMatrix_apply, hl, hq, mul_ite]
  have he := congrFun₂ h.eq (.inl 0) (.inr 6)
  simp only [Matrix.mul_apply, hr, hc, mul_add, Finset.sum_add_distrib] at he
  simp only [← Matrix.mul_apply, mul_one, one_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at he
  exact (mul_eq_zero.mp (add_eq_left.mp he)).resolve_right hb

private theorem first_coordinate_zero (P : Parameters) (hp : P.prime = 2)
    (v : Coordinates P) (b : ExtensionField P) (hb : b ≠ 0)
    (h : Commute (orderedProduct P v) (curve P 3 b)) : v 0 = 0 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  have he := h.map (UnipotentMatrices.matrixHom P)
  rw [UnipotentMatrices.matrixHom_curve P hp] at he
  exact (UnipotentMatrices.product_arm_entry P hp v).symm.trans
    (commuting_arm_entry _ _ b hb he)



private theorem fixed_positive_commutant_le_arms (P : Parameters) (hp : P.prime = 2)
    (g : SplitGroup P) (hg : g ∈ positiveSubgroup P)
    (hfix : graphFieldAutomorphism P g = g)
    (b : ExtensionField P) (hb : b ≠ 0) (hc : Commute g (curve P 3 b)) :
    g ∈ rootSubgroup P .arms := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  obtain ⟨v, rfl⟩ := (show g ∈ Set.range (orderedProduct (binaryParameters n hn)) by
    rw [range_orderedProduct_binary]; exact hg)
  have hv := (orderedProduct_mem_fixedSubgroup_iff_binary n hn v).mp hfix
  have h0 := first_coordinate_zero _ rfl v b hb hc
  have h1 : v 1 = 0 := by simpa only [show diagram 0 = 1 from rfl, h0, map_zero] using hv 0
  have h2 : v 2 = 0 := by simpa only [show diagram 1 = 2 from rfl, h1, map_zero] using hv 1
  apply orderedProduct_mem_rootSubgroup _ .arms ⟨v, ?_⟩
  intro i hi
  have hi' : i.val < 3 := by simpa only [rootSupport, not_le] using hi
  fin_cases i <;> first | exact h0 | exact h1 | exact h2 | norm_num at hi'

private theorem positive_value (m : ℕ) (hm : 0<m) (v : OrbitParameters (binaryParameters m hm)) :
    FixedDescent.carrierToSplit _ rfl (positiveEquiv m hm v).val =
      orderedProduct _ (expand _ v) := by
  rw [positiveEquiv_val,baseProduct_toSplit]

private theorem coordinates_action (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.OrbitParameters P) (σ : CoefficientAut P)
    (x : Carrier P) (v : OrbitParameters P)
    (hv : FixedDescent.carrierToSplit P hp x = orderedProduct P (expand P v)) :
    FixedDescent.carrierToSplit P hp
      ((TorusCoordinates.torusMulEquiv P hp a).val * coefficientAction P σ x *
        (TorusCoordinates.torusMulEquiv P hp a).val⁻¹) =
      orderedProduct P (fun i => TrialityOuterTorus.rootWeight P (TorusCoordinates.expand P a) i *
        σ (expand P v i)) := by
  have hg : FixedDescent.carrierToSplit P hp (TorusCoordinates.torusMulEquiv P hp a).val =
      TorusCoordinates.product P (TorusCoordinates.expand P a) := by
    rw [TorusCoordinates.torusMulEquiv_val,FixedDescent.carrierToSplit_toCarrier]
    exact TorusCoordinates.inclusion_orbitElementary P hp a
  have hcx := (Triality.Standard.EvenField.NormalForm.UnipotentCocycle.carrierToSplit_coefficient P hp σ x).trans
    ((congrArg (coefficientSplit P σ) hv).trans
      (Triality.Standard.EvenField.NormalForm.UnipotentCocycle.coefficientSplit_orderedProduct P σ (expand P v)))
  exact ((TrialityOuterFixed.map_conjugate (FixedDescent.carrierToSplit P hp)
    (TorusCoordinates.torusMulEquiv P hp a).val (coefficientAction P σ x)).trans
      (TrialityOuterFixed.conjugation_congr hg hcx)).trans
        (TrialityOuterTorus.product_orderedProduct P hp _ _)

private def positiveAction (m : ℕ) (hm : 0<m)
    (g : torus (binaryParameters m hm)) (σ : CoefficientAut (binaryParameters m hm))
    (v : OrbitParameters (binaryParameters m hm)) : OrbitParameters (binaryParameters m hm) :=
  (positiveEquiv m hm).symm ⟨g.val * coefficientAction _ σ (positiveEquiv m hm v).val * g.val⁻¹,
    (mem_normalizer_iff.mp (borel_le_normalizer_unipotent _ rfl (torus_le_borel _ g.property)) _).mp
      ((coefficient_unipotent _ σ).le (mem_map_of_mem _ (positiveEquiv m hm v).property))⟩

private theorem positiveAction_value (m : ℕ) (hm : 0<m)
    (g : torus (binaryParameters m hm)) (σ : CoefficientAut (binaryParameters m hm))
    (v : OrbitParameters (binaryParameters m hm)) :
    (positiveEquiv m hm (positiveAction m hm g σ v)).val =
      g.val * coefficientAction _ σ (positiveEquiv m hm v).val * g.val⁻¹ :=
  congrArg Subtype.val ((positiveEquiv m hm).apply_symm_apply _)

private theorem positiveAction_coordinates (m : ℕ) (hm : 0<m)
    (a : TorusCoordinates.OrbitParameters (binaryParameters m hm))
    (σ : CoefficientAut (binaryParameters m hm)) (v : OrbitParameters (binaryParameters m hm)) :
    expand _ (positiveAction m hm (TorusCoordinates.torusMulEquiv _ rfl a) σ v) =
      fun i => TrialityOuterTorus.rootWeight _ (TorusCoordinates.expand _ a) i * σ (expand _ v i) := by
  apply orderedProduct_injective
  rw [←positive_value,positiveAction_value]
  exact coordinates_action _ rfl a σ _ v (positive_value m hm v)

private theorem expand_long (P : Parameters) (v : OrbitParameters P) (i : Fin 3) :
    expand P v (![3,10,11] i) = (v.2 i).val := by
  fin_cases i <;> rfl

private theorem positiveAction_diagonal (m : ℕ) (hm : 0<m)
    (g : torus (binaryParameters m hm)) (σ : CoefficientAut (binaryParameters m hm)) :
    ∃ (c : Fin 3 → ExtensionField (binaryParameters m hm))
      (d : Fin 3 → fixedField (binaryParameters m hm)),
      ∀ v, positiveAction m hm g σ v =
        (fun i => c i * σ (v.1 i),fun i => d i * coefficientFixedField _ σ (v.2 i)) := by
  let P := binaryParameters m hm
  obtain ⟨a,rfl⟩ := (TorusCoordinates.torusMulEquiv P rfl).surjective g
  let w := TrialityOuterTorus.rootWeight P (TorusCoordinates.expand P a)
  let c := fun i => w (![0,4,7] i)
  let d := (positiveAction m hm (TorusCoordinates.torusMulEquiv P rfl a) σ (0,fun _ => 1)).2
  have hd (i : Fin 3) : (d i).val = w (![3,10,11] i) := by
    have hh := congrFun (positiveAction_coordinates m hm a σ (0,fun _ => 1)) (![3,10,11] i)
    rw [expand_long,expand_long] at hh
    exact (hh.trans (by rw [Subfield.coe_one,map_one,mul_one]))
  refine ⟨c,d,?_⟩
  intro v
  apply Prod.ext
  · funext i
    have hh := congrFun (positiveAction_coordinates m hm a σ v) (![0,4,7] i)
    fin_cases i <;> exact hh
  · funext i
    apply Subtype.ext
    change _ = (d i).val * σ (v.2 i).val
    rw [hd]
    have hh := congrFun (positiveAction_coordinates m hm a σ v) (![3,10,11] i)
    fin_cases i <;> exact hh

private theorem descended_split (P : Parameters) (hp : P.prime = 2)
    (a : Node) (g : (rootSubgroup P a).comap (fixedSubgroup P).subtype) :
    FixedDescent.carrierToSplit P hp (descendedRootEquiv P hp a g).val = g.val.val :=
  (congrArg (FixedDescent.carrierToSplit P hp) (descendedRootEquiv_val P hp a g)).trans
    (FixedDescent.carrierToSplit_toCarrier P hp _)

private theorem arms_split (P : Parameters) (hp : P.prime = 2)
    (v : ArmsParameters P) :
    FixedDescent.carrierToSplit P hp (armsEquiv P hp v).val =
      orderedProduct P (expand P (extendOrbit P .arms v)) :=
  (descended_split P hp .arms (fixedRootEquiv P hp .arms (rootOrbitEquiv P .arms v))).trans
    (fixedRootEquiv_val P hp .arms (rootOrbitEquiv P .arms v))

private theorem arms_positive (m : ℕ) (hm : 0<m)
    (v : ArmsParameters (binaryParameters m hm)) :
    (positiveEquiv m hm (extendOrbit _ .arms v)).val =
      (armsEquiv (binaryParameters m hm) rfl v).val :=
  FixedDescent.carrierToSplit_injective _ rfl
    ((positive_value m hm _).trans (arms_split _ rfl v).symm)

private def diagonal (P : Parameters) (c : Fin 2 → ExtensionField P)
    (d : Fin 3 → fixedField P) (σ : CoefficientAut P) (v : ArmsParameters P) : ArmsParameters P :=
  (fun i => c i * σ (v.1 i),fun i => d i * coefficientFixedField P σ (v.2 i))

private theorem arms_action (m : ℕ) (hm : 0<m)
    (g : torus (binaryParameters m hm)) (σ : CoefficientAut (binaryParameters m hm)) :
    ∃ (c : Fin 2 → ExtensionField (binaryParameters m hm))
      (d : Fin 3 → fixedField (binaryParameters m hm)),
      ∀ v, g.val * coefficientAction _ σ (armsEquiv _ rfl v).val * g.val⁻¹ =
        (armsEquiv _ rfl (diagonal _ c d σ v)).val := by
  obtain ⟨c,d,hd⟩ := positiveAction_diagonal m hm g σ
  refine ⟨![c 1,c 2],d,fun v => ?_⟩
  rw [←arms_positive,←positiveAction_value,hd]
  have he : (fun i => c i * σ ((extendOrbit (binaryParameters m hm) .arms v).1 i),
      fun i => d i * coefficientFixedField _ σ ((extendOrbit _ .arms v).2 i)) =
      extendOrbit _ .arms (diagonal _ ![c 1,c 2] d σ v) := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [extendOrbit,diagonal]
    · rfl
  rw [he,arms_positive]

private def diagonalAdd (P : Parameters) (c : Fin 2 → ExtensionField P)
    (d : Fin 3 → fixedField P) (σ : CoefficientAut P) : ArmsParameters P →+ ArmsParameters P where
  toFun := diagonal P c d σ
  map_zero' := by
    apply Prod.ext <;> funext i <;> simp [diagonal]
  map_add' v w := by
    apply Prod.ext <;> funext i <;> simp [diagonal,mul_add]

private theorem diagonal_smul (P : Parameters) (c : Fin 2 → ExtensionField P)
    (d : Fin 3 → fixedField P) (σ : CoefficientAut P)
    (b : fixedField P) (v : ArmsParameters P) :
    diagonalAdd P c d σ (b • v) = coefficientFixedField P σ b • diagonalAdd P c d σ v := by
  apply Prod.ext
  · funext i
    change c i * σ (b.val * v.1 i) = σ b.val * (c i * σ (v.1 i))
    rw [map_mul]
    ring
  · funext i
    change d i * coefficientFixedField P σ (b * v.2 i) =
      coefficientFixedField P σ b * (d i * coefficientFixedField P σ (v.2 i))
    rw [map_mul]
    ring

private theorem pairing_smul_left (P : Parameters) (b : fixedField P) (x y : ExtensionField P) :
    armsPairing P (b • x) y = b * armsPairing P x y := by
  apply Subtype.ext
  have hb : fieldFrobenius P b.val = b.val := b.property
  change (armsPairing P (b.val*x) y).val = b.val * (armsPairing P x y).val
  simp only [armsPairing_coe,map_mul,hb]
  ring

private theorem pairing_smul_right (P : Parameters) (b : fixedField P) (x y : ExtensionField P) :
    armsPairing P x (b • y) = b * armsPairing P x y := by
  apply Subtype.ext
  have hb : fieldFrobenius P b.val = b.val := b.property
  change (armsPairing P x (b.val*y)).val = b.val * (armsPairing P x y).val
  simp only [armsPairing_coe,map_mul,hb]
  ring

private def commutatorLinear (P : Parameters) (v : ArmsParameters P) :
    ArmsParameters P →ₗ[fixedField P] fixedField P where
  toFun := armsCommutator P v
  map_add' x y := by
    simp only [armsCommutator,armsCocycle,Prod.fst_add,Prod.snd_add,Pi.add_apply,
      armsPairing_add_left,armsPairing_add_right,mul_add,add_mul]
    abel
  map_smul' b w := by
    change v.2 1 * (b * w.2 0) + armsPairing P (b • w.1 0) (v.1 1) +
      ((b * w.2 1) * v.2 0 + armsPairing P (v.1 0) (b • w.1 1)) =
        b * (v.2 1 * w.2 0 + armsPairing P (w.1 0) (v.1 1) +
          (w.2 1 * v.2 0 + armsPairing P (v.1 0) (w.1 1)))
    rw [pairing_smul_left,pairing_smul_right]
    ring

private theorem diagonal_fixed_span (P : Parameters) (hp : P.prime = 2)
    (c : Fin 2 → ExtensionField P) (d : Fin 3 → fixedField P) (σ : CoefficientAut P)
    (hσ : orderOf σ = 2) (hi : Function.Involutive (diagonal P c d σ))
    (V : Submodule (fixedField P) (ArmsParameters P))
    (hV : ∀ v, diagonal P c d σ v = v → v ∈ V) : V = ⊤ := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  have hs : Function.Involutive σ := fun x =>
    DFunLike.congr_fun (show σ^2=1 from (orderOf_eq_prime_iff.mp hσ).1) x
  have hb : ∃ b : fixedField P, b ≠ coefficientFixedField P σ b := by
    by_contra hn
    push Not at hn
    apply TwoRank.FourSemilinear.coefficient_not_fixed_base_of_parameters P σ (by rw [hσ])
    exact fun x => (congrArg Subtype.val (hn x)).symm
  obtain ⟨b,hb⟩ := hb
  exact fixed_span (coefficientFixedField P σ) (fun x => Subtype.ext (hs x.val)) b hb
    (diagonalAdd P c d σ) hi (diagonal_smul P c d σ) V hV

private theorem nonzero_fixed {F : Type*} [Field F] [CharP F 2]
    (ρ : F →+ F) (hρ : Function.Involutive ρ) : ∃ r : F, r≠0 ∧ ρ r=r := by
  by_cases h : ρ 1=1
  · exact ⟨1,one_ne_zero,h⟩
  · refine ⟨1+ρ 1,?_,?_⟩
    · intro hh
      exact h ((CharTwo.add_eq_zero.mp hh).symm)
    · rw [map_add,hρ]
      exact add_comm _ _

private def singleton (P : Parameters) (i : Fin 3) (b : fixedField P) : ArmsParameters P :=
  (0,Pi.single i b)

private theorem diagonal_singleton (P : Parameters) (c : Fin 2 → ExtensionField P)
    (d : Fin 3 → fixedField P) (σ : CoefficientAut P) (i : Fin 3) (b : fixedField P) :
    diagonal P c d σ (singleton P i b) = singleton P i (d i * coefficientFixedField P σ b) := by
  classical
  apply Prod.ext
  · funext j
    simp [diagonal,singleton]
  · funext j
    by_cases h : j=i
    · subst j; simp [diagonal,singleton]
    · simp [diagonal,singleton,Pi.single_apply,h]

private theorem fixed_singleton (P : Parameters) (hp : P.prime = 2)
    (c : Fin 2 → ExtensionField P) (d : Fin 3 → fixedField P) (σ : CoefficientAut P)
    (hi : Function.Involutive (diagonal P c d σ)) (i : Fin 3) :
    ∃ b : fixedField P, b ≠ 0 ∧ diagonal P c d σ (singleton P i b) = singleton P i b := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  let ρ : fixedField P →+ fixedField P :=
    { toFun := fun x => d i * coefficientFixedField P σ x
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add] }
  have hρ : Function.Involutive ρ := by
    intro x
    have hh := hi (singleton P i x)
    rw [diagonal_singleton,diagonal_singleton] at hh
    change d i * coefficientFixedField P σ (d i * coefficientFixedField P σ x) = x
    simpa only [singleton,Pi.single_eq_same] using congrArg (fun v : ArmsParameters P => v.2 i) hh
  obtain ⟨b,hb,hfix⟩ := nonzero_fixed ρ hρ
  refine ⟨b,hb,?_⟩
  rw [diagonal_singleton]
  exact congrArg (singleton P i) hfix

private theorem singleton_split (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (b : fixedField P) :
    FixedDescent.carrierToSplit P hp (armsEquiv P hp (singleton P i b)).val =
      curve P (![3,10,11] i) b.val := by
  change FixedDescent.carrierToSplit P hp (toCarrier P (LeviCommutators.longElementary P hp i b)) = _
  rw [FixedDescent.carrierToSplit_toCarrier,LeviCommutators.longElementary_val]
  rfl

open scoped commutatorElement
private theorem commutator_zero_of_commute (P : Parameters) (hp : P.prime = 2)
    (v w : ArmsParameters P)
    (h : Commute (armsEquiv P hp v).val (armsEquiv P hp w).val) : armsCommutator P v w = 0 := by
  apply (armsEquiv_central_eq_one_iff P hp _).mp
  rw [←armsEquiv_commutator]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subtype.ext h.eq)

private theorem fixed_geometry_of_diagonal (P : Parameters) (hp : P.prime = 2)
    (σ : CoefficientAut P) (hσ : orderOf σ = 2) (a : MulAut (Carrier P))
    (c : Fin 2 → ExtensionField P) (d : Fin 3 → fixedField P)
    (ha : ∀ v, a (armsEquiv P hp v).val = (armsEquiv P hp (diagonal P c d σ v)).val)
    (hi : ∀ x ∈ unipotent P, a (a x) = x) :
    unipotent P ⊓ centralizer ((unipotent P ⊓ a.fixedSubgroup : Subgroup (Carrier P)) : Set (Carrier P)) ≤ highestRoot P ∧
      _root_.commutator ↥(unipotent P ⊓ a.fixedSubgroup) ≠ ⊥ := by
  let U := unipotent P ⊓ a.fixedSubgroup
  have hQU : armsSubgroup P ≤ unipotent P :=
    descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .arms)
  have hd : Function.Involutive (diagonal P c d σ) := by
    intro v
    apply (armsEquiv P hp).injective
    apply Subtype.ext
    have hh := hi (armsEquiv P hp v).val (hQU (armsEquiv P hp v).property)
    rw [ha,ha] at hh
    exact hh
  have hfixed (v) (hv : diagonal P c d σ v = v) : (armsEquiv P hp v).val ∈ U :=
    ⟨hQU (armsEquiv P hp v).property,(MulAut.mem_fixedSubgroup _ _).mpr (by rw [ha,hv])⟩
  obtain ⟨b,hb,hbf⟩ := fixed_singleton P hp c d σ hd 0
  have hcentral : unipotent P ⊓ centralizer (U : Set (Carrier P)) ≤ highestRoot P := by
    intro x hx
    have hcomm : Commute x (armsEquiv P hp (singleton P 0 b)).val :=
      (mem_centralizer_iff.mp hx.2 _ (hfixed _ hbf)).symm
    have hxQ : x ∈ armsSubgroup P := by
      apply (FixedDescent.mem_descend_iff P hp (rootSubgroup P .arms) x).mpr
      apply fixed_positive_commutant_le_arms P hp _
        ((FixedDescent.mem_descend_iff P hp (positiveSubgroup P) x).mp hx.1)
        (FixedDescent.carrierToSplit_mem_fixed P hp x) b.val
        (fun hz => hb (Subtype.ext hz))
      have hh := hcomm.map (FixedDescent.carrierToSplit P hp)
      rw [singleton_split] at hh
      exact hh
    obtain ⟨v,hv⟩ := (armsEquiv P hp).surjective ⟨x,hxQ⟩
    have hxv : (armsEquiv P hp v).val = x := congrArg Subtype.val hv
    let W := (commutatorLinear P v).ker
    have hW : W = ⊤ := diagonal_fixed_span P hp c d σ hσ hd W (fun w hw => by
      change armsCommutator P v w = 0
      apply commutator_zero_of_commute P hp v w
      rw [hxv]
      exact (mem_centralizer_iff.mp hx.2 _ (hfixed _ hw)).symm)
    have hvC : v = centralParameters P (v.2 2) := armsCommutator_radical P hp v (fun w => by
      change w ∈ W
      rw [hW]
      trivial)
    rw [←hxv,hvC,armsEquiv_centralParameters,←highestHom_range P hp]
    exact ⟨_,rfl⟩
  refine ⟨hcentral,?_⟩
  obtain ⟨e,he,hef⟩ := fixed_singleton P hp c d σ hd 1
  intro hbot
  have hmul := (commutator_eq_bot_iff U).mp hbot
  let : IsMulCommutative U := hmul
  have hcomm : Commute (armsEquiv P hp (singleton P 1 e)).val
      (armsEquiv P hp (singleton P 0 b)).val :=
    congrArg Subtype.val (mul_comm' (⟨_,hfixed _ hef⟩ : U) ⟨_,hfixed _ hbf⟩)
  have hz := commutator_zero_of_commute P hp _ _ hcomm
  have heq : armsCommutator P (singleton P 1 e) (singleton P 0 b) = e*b := by
    simp [armsCommutator,armsCocycle,singleton]
  rw [heq] at hz
  exact mul_ne_zero he hb hz

/-- Fixed points of the genuine torus--coefficient action have a nontrivial
commutator, and their centralizer in U lies in the actual highest root.
Only involutivity on U is required; the coefficient has order two. -/
theorem torus_coefficient_fixed_geometry (m : ℕ) (hm : 0<m)
    (g : torus (binaryParameters m hm)) (σ : CoefficientAut (binaryParameters m hm))
    (hσ : orderOf σ = 2)
    (hi : ∀ x ∈ unipotent (binaryParameters m hm),
      (MulAut.conj g.val * coefficientAction (binaryParameters m hm) σ)
        ((MulAut.conj g.val * coefficientAction (binaryParameters m hm) σ) x) = x) :
    let P := binaryParameters m hm
    let a := MulAut.conj g.val * coefficientAction P σ
    unipotent P ⊓ centralizer ((unipotent P ⊓ a.fixedSubgroup : Subgroup (Carrier P)) : Set (Carrier P)) ≤ highestRoot P ∧
      _root_.commutator ↥(unipotent P ⊓ a.fixedSubgroup) ≠ ⊥ := by
  obtain ⟨c,d,ha⟩ := arms_action m hm g σ
  exact fixed_geometry_of_diagonal _ rfl σ hσ _ c d ha hi


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityFixedGeometry
