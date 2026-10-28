module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.TensorModuleApplication

/-!
# Short-coroot weights lifted from the source tensor

The common source Cartan normalizes each canonical root. For the simple
long and two middle short roots, compare the corresponding faithful
coordinate after the literal diagonal tensor action. Thus the tensor
weights lift to equalities in the original group, not only in a section.
The same short Weyl element gives the other nontrivial long-root weight;
the orthogonal rank-one pair gives the remaining trivial weight.

The result constructs all six positive short-coroot characters on the
whole-actor-aligned pinning. The middle short root still has its source
Frobenius label. Together with the previously constructed long-coroot
weights these equations supply covariance of the last mixed coefficient.
Every positive binary exponent and both orientations are retained.

Source: Fong--Seitz II (9.31), printed p.219, with the compatible tensor
basis preceding (9.27). Actions here use left conjugation.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups MonoidAlgebra TensorProduct
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
open Representation Representation.SL2.BinarySmall
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorTorus
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (σ : F ≃+* F) (indices : Fin 2 ≃ Fin 2)
  (hVi : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0))
  (hVj : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1))
  (μi : localGroup Q split (indices 0) ≃* PSL(2,F))
  (μj : localGroup Q split (indices 1) ≃* PSL(2,ScalarMarking.SourceFixed (σ := σ)))
  (hm : rotationOrder Q = 6)
  (row : StructuralRow Q split (indices 0) (indices 1))
  {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
local notation "i" => indices 0
local notation "j" => indices 1
local notation "si" => UnitarySource.actorReflection Q split i
local notation "q" => GeometricScalars.alignedPair Q split σ indices hVi hVj μi μj hm row e
local notation "w" => GeometricScalars.alignedPlacement Q split σ indices hVi hVj μi μj hm row e
local notation "hs" => GeometricScalars.aligned_short_range Q split σ indices hVi hVj μi μj hm row e
local notation "hl" => GeometricScalars.aligned_long_range Q split σ indices hVi hVj μi μj hm row e
local notation "cc" => StructuralApplication.positiveCommutations Q split (q) (w) (hs) (hl) hm row


local notation "vB" => TensorRootAxes.longVector Q split σ indices hVi hVj μi μj hm row e
local notation "bLift" => TensorRootAxes.longLift Q split σ indices hVi hVj μi μj hm row e
local notation "eLift" => TensorRootAxes.upperLift Q split σ indices hVi hVj μi μj hm row e
local notation "cLift" => TensorMiddleRoots.nextLift Q split σ indices hVi hVj μi μj hm row e
local notation "dLift" => TensorMiddleRoots.middleLift Q split σ indices hVi hVj μi μj hm row e
local notation "cV" => TensorMiddleRoots.nextVector Q split σ indices hVi hVj μi μj hm row e
local notation "dV" => TensorMiddleRoots.middleVector Q split σ indices hVi hVj μi μj hm row e

private theorem short_cartan (t : Fˣ) :
    (q).shortMap (tor t) ∈ Q.tits.B ⊓ Q.tits.N :=
  GeometricPinning.short_cartan Q split σ indices hVi hVj μi μj
    (UnitarySource.actorReflection Q split (indices 0))
    (UnitarySource.actorReflection Q split (indices 1)) hm row.orthogonal t

variable [hEA : IsElementaryAbelian 2 (RadicalQuotient Q split (indices 0))]
include hEA
local notation "ρ" => TensorApplication.sourceAction Q split indices hVi μi (hEA := hEA)
section Chart
variable {C : Type*} [Field C] (κ : F →+* C)
  (J : Additive (RadicalQuotient Q split (indices 0)) →+ TripleSpace C)
  (c : ScalarMarking.SourceFixed (σ := σ) →+ C)

omit hEA [Finite F] [CharP F 2] in
private theorem tor_coordinates (t : Fˣ) (v : TripleSpace C) (r s k : Fin 2) :
    TensorCoordinates.coordinates (TensorAction.cubicTensor κ σ (tor t) v) ((r,s),k) =
      (if r = 0 then κ t.val else κ t.val⁻¹)*
      (if s = 0 then κ (σ t.val) else κ (σ t.val)⁻¹)*
      (if k = 0 then κ (σ (σ t.val)) else κ (σ (σ t.val))⁻¹)*
        TensorCoordinates.coordinates v ((r,s),k) := by
  rw [TensorCoordinates.action]
  fin_cases r <;> fin_cases s <;> fin_cases k <;>
    simp [TensorCoordinates.matrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_two,tor]

/-- The actual short coroot has inverse-norm weight on the simple long root. -/
theorem tor_long0
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (hc : c 1 = 1) (t : Fˣ) (a : K) :
    (q).shortMap (tor t)*(q).l 0 a*((q).shortMap (tor t))⁻¹ =
      (q).l 0 ((e.norm t.val)⁻¹*a) := by
  have hx : (q).shortMap (tor t)*(q).l 0 a*((q).shortMap (tor t))⁻¹ ∈ simpleRoot Q split j :=
    (mem_normalizer_iff.mp (torus_normalizes_simpleRoot Q split j
      (short_cartan Q split σ indices hVi hVj μi μj hm row e t)) ((q).l 0 a)).mp
        ((hl).le ⟨.ofAdd a,rfl⟩)
  obtain ⟨b,hb⟩ := (hl).symm ▸ hx
  have hv : (ρ) (tor t) ((vB) a) = (vB) b.toAdd :=
    TensorApplication.action_conjugation Q split σ indices hVi hVj μi μj hm e row
      (tor t) ((bLift) (.ofAdd a)) ((bLift) b) hb
  have hh := congrArg (fun v => TensorCoordinates.coordinates (J v) ((1,1),1)) hv
  rw [hact,tor_coordinates,hB,hB] at hh
  simp only [TensorMiddleRoots.coefficient_eq_embedding Q split σ indices hVi hVj μi μj hm row e
    κ J c hact hE hB hc] at hh
  simp [TensorCoordinates.coordinates] at hh
  have he : b.toAdd = (e.norm t.val)⁻¹*a := by
    apply Subtype.ext
    apply κ.injective
    change κ b.toAdd.val = κ ((t.val*σ t.val*σ (σ t.val))⁻¹*a.val)
    rw [←hh]
    simp only [map_mul,map_inv₀,mul_inv_rev]
    ring
  exact hb.symm.trans (congrArg ((q).l 0) he)

theorem tor_short1
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (hc : c 1 = 1) (t : Fˣ) (a : F) :
    (q).shortMap (tor t)*(q).s 1 a*((q).shortMap (tor t))⁻¹ =
      (q).s 1 ((t.val*(σ t.val)⁻¹*(σ (σ t.val))⁻¹)*a) := by
  have hr : ((q).shortOrbit 1).range = rootAt Q split i (Q.simple j) :=
    RootGeometry.short_one_rootAt Q split (q) (w) (hs)
  have hx : (q).shortMap (tor t)*(q).s 1 a*((q).shortMap (tor t))⁻¹ ∈ rootAt Q split i (Q.simple j) :=
    (mem_normalizer_iff.mp (rootAt_torus_normalizes Q split i _
      (short_cartan Q split σ indices hVi hVj μi μj hm row e t)) ((q).s 1 a)).mp
        (hr.le ⟨.ofAdd a,rfl⟩)
  obtain ⟨b,hb⟩ := hr.symm ▸ hx
  have hv : (ρ) (tor t) ((cV) a) = (cV) b.toAdd :=
    TensorApplication.action_conjugation Q split σ indices hVi hVj μi μj hm e row
      (tor t) ((cLift) (.ofAdd a)) ((cLift) b) hb
  have hh := congrArg (fun v => TensorCoordinates.coordinates (J v) ((0,1),1)) hv
  rw [hact,tor_coordinates] at hh
  simp only [TensorMiddleRoots.next_coordinates Q split σ indices hVi hVj μi μj hm row e
    κ J c hact hE hB hc] at hh
  simp only [show (1:Fin 2) ≠ 0 from by decide,↓reduceIte] at hh
  have he : b.toAdd = (t.val*(σ t.val)⁻¹*(σ (σ t.val))⁻¹)*a := by
    apply κ.injective
    rw [←hh]
    simp only [map_mul,map_inv₀]
  exact hb.symm.trans (congrArg ((q).s 1) he)

theorem tor_short2
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (hc : c 1 = 1) (t : Fˣ) (a : F) :
    (q).shortMap (tor t)*(q).s 2 a*((q).shortMap (tor t))⁻¹ =
      (q).s 2 ((t.val⁻¹*σ t.val*σ (σ t.val))*a) := by
  have hr : ((q).shortOrbit 2).range = rootAt Q split i (Q.simple j*Q.simple i) :=
    RootGeometry.short_two_rootAt Q split (q) (w) (hs)
  have hx : (q).shortMap (tor t)*(q).s 2 a*((q).shortMap (tor t))⁻¹ ∈ rootAt Q split i (Q.simple j*Q.simple i) :=
    (mem_normalizer_iff.mp (rootAt_torus_normalizes Q split i _
      (short_cartan Q split σ indices hVi hVj μi μj hm row e t)) ((q).s 2 a)).mp
        (hr.le ⟨.ofAdd a,rfl⟩)
  obtain ⟨b,hb⟩ := hr.symm ▸ hx
  have hv : (ρ) (tor t) ((dV) a) = (dV) b.toAdd :=
    TensorApplication.action_conjugation Q split σ indices hVi hVj μi μj hm e row
      (tor t) ((dLift) (.ofAdd a)) ((dLift) b) (by
        change ((dLift) (.ofAdd b.toAdd) : X ⧸ Q.D) = _
        rw [TensorMiddleRoots.middleLift_coe,TensorMiddleRoots.middleLift_coe]
        exact hb)
  have hh := congrArg (fun v => TensorCoordinates.coordinates (J v) ((1,0),0)) hv
  rw [hact,tor_coordinates] at hh
  simp only [TensorMiddleRoots.middle_coordinates Q split σ indices hVi hVj μi μj hm row e
    κ J c hact hE hB hc] at hh
  simp only [show (1:Fin 2) ≠ 0 from by decide,↓reduceIte] at hh
  have he : b.toAdd = (t.val⁻¹*σ t.val*σ (σ t.val))*a := by
    apply κ.injective
    rw [←hh]
    simp only [map_mul,map_inv₀]
  exact hb.symm.trans (congrArg ((q).s 2) he)

end Chart
omit hEA in
/-- All positive short-coroot weights on the actual aligned source roots,
with the original Frobenius marking on the middle root. -/
theorem constructed_weights :
    (∀ (t : Fˣ) (r : Fin 3) (a : F),
      (q).shortMap (tor t)*(q).s r a*((q).shortMap (tor t))⁻¹ =
        (q).s r (![t.val^2,t.val*(σ t.val)⁻¹*(σ (σ t.val))⁻¹,
          t.val⁻¹*σ t.val*σ (σ t.val)] r*a)) ∧
    (∀ (t : Fˣ) (r : Fin 3) (a : K),
      (q).shortMap (tor t)*(q).l r a*((q).shortMap (tor t))⁻¹ =
        (q).l r (![ (e.norm t.val)⁻¹,e.norm t.val,1] r*a)) := by
  let hEA := linear_pair_radicalQuotient_elementary Q split hm j i
    (indices.injective.ne (by decide)) μj μi
  let := TensorApplication.irreducible Q split σ indices hVi hVj μi μj hm e
  obtain ⟨κ,J,c,_,_,hc,hact,hE,hB⟩ :=
    TensorRootAxes.source_axes Q split σ indices hVi hVj μi μj hm row e
  constructor
  · intro t r a
    fin_cases r
    · have hh := (q).hA_short0 e t a
      rw [RankOnePair.hA_parameter] at hh
      exact hh
    · exact tor_short1 Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc t a
    · exact tor_short2 Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc t a
  · intro t r a
    fin_cases r
    · exact tor_long0 Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc t a
    · have hh := congrArg (q).dihedral.A
        (tor_long0 Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc t⁻¹ a)
      have ht : (q).dihedral.A ((q).shortMap (tor t⁻¹)) = (q).shortMap (tor t) := by
        change (q).shortMap (weyl F)*(q).shortMap (tor t⁻¹)*((q).shortMap (weyl F))⁻¹ = _
        rw [←map_inv,←map_mul,←map_mul,weyl_tor,inv_inv]
      simp only [map_mul,map_inv,ht,Units.val_inv_eq_inv_val,Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.norm_inv,inv_inv] at hh
      exact hh
    · change (q).shortMap (tor t)*(q).l 2 a*((q).shortMap (tor t))⁻¹ = (q).l 2 (1*a)
      rw [one_mul]
      exact ((q).shortMap_commute_long2 (cc) (tor t) a).mul_inv_cancel

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorTorus
