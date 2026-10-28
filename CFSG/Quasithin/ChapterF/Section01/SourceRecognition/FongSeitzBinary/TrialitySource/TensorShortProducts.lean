module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.TensorMiddleRoots

/-!
# The complete lifted short-short source product

The earlier radical geometry puts [C,A] in the actual product E D F.
Its conjugation action on the same radical quotient, in the compatible
middle-root tensor coordinates, determines the D coefficient and the
E trace coefficient. The original long Weyl lift exchanges E and F;
their geometric disjointness then determines the final F coefficient.

Thus (9.29)(i) and (9.30) are group equalities on the aligned source
pinning, including q=2 and q=4 and both orientations. The tensor chart is
constructed internally in constructed_short_product. No normalized
commutator or coefficient assumption is added. TensorModuleApplication
combines this with the trace pairings and actual mixed product; the latter's
torus covariance remains necessary before the positive source relations.

Source: Fong--Seitz II printed p.219, (9.29)(i)--(9.30), using I (6E)(b)
and the canonical three-middle-root product. Right commutators are x⁻¹y⁻¹xy.
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
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorShortProducts
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
local notation "eLift" => TensorRootAxes.upperLift Q split σ indices hVi hVj μi μj hm row e
local notation "mV" => TensorRootAxes.mixedVector Q split σ indices hVi hVj μi μj hm row e

local notation "cLift" => TensorMiddleRoots.nextLift Q split σ indices hVi hVj μi μj hm row e
local notation "dLift" => TensorMiddleRoots.middleLift Q split σ indices hVi hVj μi μj hm row e
local notation "cV" => TensorMiddleRoots.nextVector Q split σ indices hVi hVj μi μj hm row e
local notation "dV" => TensorMiddleRoots.middleVector Q split σ indices hVi hVj μi μj hm row e
private theorem short_inv (r : Fin 3) (a : F) : ((q).s r a)⁻¹ = (q).s r a := by
  change (((q).shortOrbit r) (.ofAdd a))⁻¹ = _
  rw [←map_inv,←ofAdd_neg,CharTwo.neg_eq]

/-- The initial radical commutator bound gives an actual three-factor
product for [C,A], before the tensor calculation determines coefficients. -/
theorem short_decomposition (a b : F) :
    ∃ (d : F) (u v : K), rightCommutator ((q).s 1 b) ((q).s 0 a) =
      (q).l 1 u * (q).s 2 d * (q).l 2 v := by
  have hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥ := by
    rw [←(hs)]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rintro x ⟨r,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro y ⟨s,rfl⟩
    exact ((Commute.all s r).map ((q).shortOrbit 0)).eq
  have ha : (q).s 0 a ∈ simpleRemainder Q split j :=
    simpleRoot_le_other_remainder Q split hm i j (indices.injective.ne (by decide))
      ((hs).le ⟨.ofAdd a,rfl⟩)
  have hb : (q).s 1 b ∈ simpleRemainder Q split j :=
    (exchanged_roots_le_remainder Q split hm i j (indices.injective.ne (by decide))).1
      ((RootGeometry.short_one_rootAt Q split (q) (w) (hs)).le ⟨.ofAdd b,rfl⟩)
  have hh : rightCommutator ((q).s 1 b) ((q).s 0 a) ∈
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
    simpa only [rightCommutator,commutatorElement_def,short_inv] using
      Subgroup.commutator_mem_commutator hb ha
  obtain ⟨E,hE,D,hD,F,hF,he⟩ := radical_commutator_three_coordinates Q split hm i j
    (indices.injective.ne (by decide)) hVi hA _ hh
  obtain ⟨u,rfl⟩ := (ModuleApplication.long_one_rootAt Q split (q) (w) (hl)).symm ▸ hE
  obtain ⟨d,rfl⟩ := (RootGeometry.short_two_rootAt Q split (q) (w) (hs)).symm ▸ hD
  obtain ⟨v,rfl⟩ := (ModuleApplication.long_two_rootAt Q split (q) (w) (hl)).symm ▸ hF
  exact ⟨d.toAdd,u.toAdd,v.toAdd,he⟩

variable [hEA : IsElementaryAbelian 2 (RadicalQuotient Q split (indices 0))]
include hEA
local notation "ρ" => TensorApplication.sourceAction Q split indices hVi μi (hEA := hEA)

/-- The same representatives give the upper action on C in the radical
abelianization; only the literal derived root is removed. -/
theorem short_decomposition_action (a b : F) :
    ∃ (d : F) (u v : K),
      rightCommutator ((q).s 1 b) ((q).s 0 a) = (q).l 1 u * (q).s 2 d * (q).l 2 v ∧
      (ρ) (uni a) ((cV) b) =
        (cV) b + Additive.ofMul (Abelianization.of ((eLift) u)) + (dV) d := by
  obtain ⟨d,u,v,he⟩ := short_decomposition Q split σ indices hVi hVj μi μj hm row e a b
  have hv : (q).l 2 v ∈ simpleRemainder Q split i :=
    (exchanged_roots_le_remainder Q split hm j i (indices.injective.ne (by decide))).2
      ((ModuleApplication.long_two_rootAt Q split (q) (w) (hl)).le ⟨.ofAdd v,rfl⟩)
  let fv : simpleRemainder Q split i := ⟨(q).l 2 v,hv⟩
  have hz : Abelianization.of fv = 1 := by
    have hfv : (fv : X ⧸ Q.D) ∈
        (Abelianization.of : simpleRemainder Q split i →* RadicalQuotient Q split i).ker.map
          (simpleRemainder Q split i).subtype := by
      rw [radicalProjection_kernel,row.radical_derived]
      exact (ModuleApplication.long_two_rootAt Q split (q) (w) (hl)).le ⟨.ofAdd v,rfl⟩
    obtain ⟨y,hy,hyv⟩ := hfv
    have heq : y = fv := Subtype.ext hyv
    exact heq ▸ hy
  have hconj : (q).s 0 a * (q).s 1 b * ((q).s 0 a)⁻¹ =
      (q).s 1 b * (q).l 1 u * (q).s 2 d * (q).l 2 v := by
    rw [mul_assoc ((q).s 1 b) ((q).l 1 u),mul_assoc ((q).s 1 b),←he]
    simp only [rightCommutator,mul_assoc,mul_inv_cancel_left]
    rw [short_inv]
  have hact := TensorApplication.action_conjugation Q split σ indices hVi hVj μi μj hm e row
    (uni a) ((cLift) (.ofAdd b))
    ((cLift) (.ofAdd b) * (eLift) u * (dLift) (.ofAdd d) * fv) (by
      change ((cLift) (.ofAdd b) : X ⧸ Q.D) * ((eLift) u : X ⧸ Q.D) *
        ((dLift) (.ofAdd d) : X ⧸ Q.D) * (fv : X ⧸ Q.D) = _
      rw [TensorMiddleRoots.nextLift_coe,TensorMiddleRoots.middleLift_coe,TensorRootAxes.upperLift_coe]
      exact hconj.symm)
  refine ⟨d,u,v,he,?_⟩
  change (ρ) (uni a) (Additive.ofMul (Abelianization.of ((cLift) (.ofAdd b)))) = _
  rw [hact]
  simp only [map_mul,hz,mul_one]
  rfl

section Chart
variable {C : Type*} [Field C] (κ : F →+* C)
  (J : Additive (RadicalQuotient Q split (indices 0)) →+ TripleSpace C)
  (c : ScalarMarking.SourceFixed (σ := σ) →+ C)

/-- The complete lifted short-short product with its still arbitrary
highest coefficient, determined from the now compatible tensor chart. -/
theorem short_product
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (hc : c 1 = 1) (a b : F) :
    ∃ v : K, rightCommutator ((q).s 1 b) ((q).s 0 a) =
      (q).s 2 (σ a*σ (σ b)+σ (σ a)*σ b) *
        (q).l 1 (e.trace (σ a*σ (σ a)*b)) * (q).l 2 v := by
  obtain ⟨d,u,v,hg,hv⟩ := short_decomposition_action Q split σ indices hVi hVj μi μj hm row e a b
  have he := congrArg (fun z => TensorCoordinates.coordinates (J z)) hv
  rw [hact,TensorCoordinates.action] at he
  change TensorCoordinates.upper κ σ a (TensorCoordinates.coordinates (J ((cV) b))) = _ at he
  simp only [map_add,hE] at he
  have hd : d = σ a*σ (σ b)+σ (σ a)*σ b := by
    have hh := congrFun he ((1,0),0)
    rw [TensorCoordinates.upper_100] at hh
    simp only [Pi.add_apply,
      TensorMiddleRoots.next_coordinates Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc,
      TensorMiddleRoots.middle_coordinates Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc] at hh
    simp [TensorCoordinates.coordinates] at hh
    apply κ.injective
    rw [←hh]
    simp only [map_add,map_mul]
    ring
  have hu : u = e.trace (σ a*σ (σ a)*b) := by
    have hh := congrFun he ((0,0),0)
    rw [TensorCoordinates.upper_000] at hh
    simp only [Pi.add_apply,
      TensorMiddleRoots.next_coordinates Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc,
      TensorMiddleRoots.middle_coordinates Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc,
      TensorMiddleRoots.coefficient_eq_embedding Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc] at hh
    simp [TensorCoordinates.coordinates] at hh
    apply Subtype.ext
    apply κ.injective
    change κ u.val = κ ((σ a*σ (σ a)*b) + σ (σ a*σ (σ a)*b) + σ (σ (σ a*σ (σ a)*b)))
    rw [←hh]
    simp only [map_add,map_mul,e.cubic]
    ring
  refine ⟨v,?_⟩
  rw [hg,hd,hu,((cc).short2_long1 _ _).eq]
end Chart

omit hEA in
/-- The highest short-short coefficient is forced by the original long
Weyl symmetry and disjoint long roots. No matrix equations remain as inputs. -/
theorem constructed_short_product (a b : F) :
    rightCommutator ((q).s 1 b) ((q).s 0 a) =
      (q).s 2 (σ a*σ (σ b)+σ (σ a)*σ b) *
        (q).l 1 (e.trace (σ a*σ (σ a)*b)) *
        (q).l 2 (e.trace (a*σ b*σ (σ b))) := by
  let hEA := linear_pair_radicalQuotient_elementary Q split hm j i
    (indices.injective.ne (by decide)) μj μi
  let := TensorApplication.irreducible Q split σ indices hVi hVj μi μj hm e
  obtain ⟨κ,J,c,_,_,hc,hact,hE,hB⟩ :=
    TensorRootAxes.source_axes Q split σ indices hVi hVj μi μj hm row e
  have hp := short_product Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc
  choose f hf using hp
  have he := PinnedApplication.short_coefficient (q) e f
    ((q).longOrbit_injective
      (GeometricLongRoots.aligned_long_injective Q split σ indices hVi hVj μi μj hm row e) 2)
    (ModuleApplication.long_ranges_disjoint Q split (q) (w) (hl) hm)
    (cc).short2_long1 (cc).short2_long2 (cc).long1_long2 hf a b
  rw [hf,he]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorShortProducts
