module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.TensorRootAxes
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.TensorFiltration

/-!
# Compatible middle-root coordinates in the actual triality tensor

The structural radical commutator, transported by the original long Weyl
lift, puts [D,A] in E. The tensor filtration therefore bounds the support
of D; the short Weyl lift gives the complementary support of C. Comparing
with the proved natural-section commutator in the same U/(E D F) determines
all six middle coordinates and proves that the normalized long coefficient
is the restriction of the very same cubic-field embedding.

These formulas prove both full trace pairings in the source group. They
also lift the mixed product to C(a t) D(σ(a) σ²(a) t) E(N(a)t) F(v), with
only the final coefficient still undetermined. The constructed_relations
application supplies its tensor chart and elementary/irreducible instances
internally, in either orientation and including q=2 and q=4. No quotient
coordinate equation is substituted for a group equality: each lift uses
its separately proved structural range or exact middle-root product.

Source: Fong--Seitz I (6E)(b), printed p.43; II printed pp.218--219,
the field comparison before (9.27), (9.27)--(9.29). The short-short product,
highest mixed coefficient and covariance, remaining torus laws and full
marked comparison retain their subsequent source obligations.
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
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorMiddleRoots
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

def nextLift : Multiplicative F →* simpleRemainder Q split i :=
  ((q).shortOrbit 1).codRestrict _ (fun a => by
    have hC : ((q).shortOrbit 1).range ≤ middleRoots Q split j i := by
      rw [RootGeometry.short_one_rootAt Q split (q) (w) (hs)]
      exact le_sup_left.trans le_sup_left
    exact middleRoots_le_remainder Q split hm j i (indices.injective.ne (by decide))
      (hC ⟨a,rfl⟩))
local notation "cLift" => nextLift Q split σ indices hVi hVj μi μj hm row e

theorem nextLift_coe (a : F) : ((cLift) (.ofAdd a) : X ⧸ Q.D) = (q).s 1 a := rfl

def middleLift : Multiplicative F →* simpleRemainder Q split i :=
  (radicalAction Q split i hVi (alignedPinning Q split i hVi μi si (weyl F))).toMonoidHom.comp
    (cLift)
local notation "dLift" => middleLift Q split σ indices hVi hVj μi μj hm row e

theorem middleLift_coe (a : F) : ((dLift) (.ofAdd a) : X ⧸ Q.D) = (q).s 2 a := by
  change (radicalAction Q split i hVi (alignedPinning Q split i hVi μi si (weyl F))
    ((cLift) (.ofAdd a)) : X ⧸ Q.D) = _
  rw [radicalAction_apply,nextLift_coe]
  rfl

def nextVector : F →+ Additive (RadicalQuotient Q split i) :=
  (Abelianization.of.comp (cLift)).toAdditive

def middleVector : F →+ Additive (RadicalQuotient Q split i) :=
  (Abelianization.of.comp (dLift)).toAdditive
local notation "cV" => nextVector Q split σ indices hVi hVj μi μj hm row e
local notation "dV" => middleVector Q split σ indices hVi hVj μi μj hm row e

private theorem short_inv (r : Fin 3) (a : F) : ((q).s r a)⁻¹ = (q).s r a := by
  change (((q).shortOrbit r) (.ofAdd a))⁻¹ = _
  rw [←map_inv,←ofAdd_neg,CharTwo.neg_eq]

/-- 6E(b) and the original long Weyl lift give the literal lower pairing's
range, before any choice of its coefficient. -/
theorem lower_commutator_range (a b : F) :
    ∃ t : K, rightCommutator ((q).s 2 b) ((q).s 0 a) = (q).l 1 t := by
  have hc : rightCommutator ((q).s 2 b) ((q).s 1 a) ∈ ((q).longOrbit 2).range := by
    rw [ModuleApplication.long_two_rootAt Q split (q) (w) (hl)]
    change _ ∈ rootAt Q split j (Q.simple i * Q.simple j)
    rw [←row.radical_derived]
    have hh := Subgroup.commutator_mem_commutator
      (((dLift) (.ofAdd b)).property) (((cLift) (.ofAdd a)).property)
    rw [middleLift_coe,nextLift_coe] at hh
    simpa only [rightCommutator,commutatorElement_def,short_inv] using hh
  obtain ⟨t,ht⟩ := hc
  refine ⟨t.toAdd,?_⟩
  have hh := congrArg (q).dihedral.B ht
  simp only [rightCommutator,map_mul,map_inv] at hh
  have hD : (q).dihedral.B ((q).s 2 b) = (q).s 2 b := (q).orthogonalShort b
  have hC : (q).dihedral.B ((q).s 1 a) = (q).s 0 a := (q).dihedral.B_B _
  have hF : (q).dihedral.B (((q).longOrbit 2) t) = (q).l 1 t.toAdd := (q).dihedral.B_B _
  rw [hD,hC,hF] at hh
  exact hh.symm

/-- The already constructed natural action identifies the leading short
factor of the same mixed commutator. The error belongs to the literal
three-middle-root subgroup, normal only in U. -/
theorem mixed_difference_mem (a : F) (t : K) :
    ((q).s 1 (a*t.val))⁻¹ * rightCommutator ((q).l 0 t) ((q).s 0 a) ∈
      middleRoots Q split i j := by
  let p := GeometricApplication.pair Q split σ indices hVi hVj μi μj hm row
  let wp := GeometricApplication.placement Q split σ indices hVi hVj μi μj hm row
  have hsp := GeometricApplication.short_range Q split σ indices hVi hVj μi μj hm row
  have hlp := GeometricApplication.long_range Q split σ indices hVi hVj μi μj hm row
  let M := (middleRoots Q split i j).subgroupOf split.U
  let : M.Normal := NaturalSectionApplication.positive_normal Q split p wp hsp hm hVi row
  let π := QuotientGroup.mk' M
  let A : split.U := ⟨(q).s 0 a,(hs).le.trans (simpleRoot_le Q split i) ⟨.ofAdd a,rfl⟩⟩
  let B : split.U := ⟨(q).l 0 t,(hl).le.trans (simpleRoot_le Q split j) ⟨.ofAdd t,rfl⟩⟩
  let C : split.U := ⟨(q).s 1 (a*t.val),(show simpleRemainder Q split i ≤ split.U from inf_le_left) (((cLift) (.ofAdd (a*t.val))).property)⟩
  have hA : ScalarAlignment.sectionA Q split p wp hsp M (.ofAdd a) = π A := by
    apply congrArg π
    apply Subtype.ext
    exact ((p).relabelLong_short
      (GeometricScalars.scalarAutomorphism Q split σ indices hVi hVj μi μj hm row e).symm 0 a).symm
  have hB : ScalarAlignment.sectionB Q split (q) (w) (hl) M (.ofAdd t) = π B := rfl
  have hC : ScalarAlignment.sectionC Q split p wp hsp hlp hm M (.ofAdd (a*t.val)) = π C := by
    apply congrArg π
    apply Subtype.ext
    exact ((p).relabelLong_short
      (GeometricScalars.scalarAutomorphism Q split σ indices hVi hVj μi μj hm row e).symm 1 (a*t.val)).symm
  have h := GeometricScalars.leading_commutator Q split σ indices hVi hVj μi μj hm row e a t
  change rightCommutator
    (ScalarAlignment.sectionA Q split p wp hsp M (.ofAdd a))
    (ScalarAlignment.sectionB Q split (q) (w) (hl) M (.ofAdd t)) =
      ScalarAlignment.sectionC Q split p wp hsp hlp hm M (.ofAdd (a*t.val)) at h
  rw [hA,hB,hC] at h
  have hc : C⁻¹ = C := Subtype.ext (short_inv Q split σ indices hVi hVj μi μj hm row e 1 _)
  have hr : rightCommutator (π B) (π A) = π C := by
    calc
      _ = (rightCommutator (π A) (π B))⁻¹ := by
        simp only [rightCommutator,mul_inv_rev,inv_inv,mul_assoc]
      _ = π C := by rw [h,←map_inv,hc]
  have hz : π (C⁻¹ * rightCommutator B A) = 1 := by
    have hmap : π (rightCommutator B A) = rightCommutator (π B) (π A) := by
      simp only [rightCommutator,map_mul,map_inv]
    rw [map_mul,map_inv,hmap,hr,inv_mul_cancel]
  exact (QuotientGroup.eq_one_iff (C⁻¹ * rightCommutator B A)).mp hz

/-- An actual product in the source group, with the leading coefficient
proved and the remaining coefficients still unspecified. -/
theorem mixed_decomposition (a : F) (t : K) :
    ∃ (b : F) (u v : K), rightCommutator ((q).l 0 t) ((q).s 0 a) =
      (q).s 1 (a*t.val) * (q).l 1 u * (q).s 2 b * (q).l 2 v := by
  have hh := mixed_difference_mem Q split σ indices hVi hVj μi μj hm row e a t
  change _ ∈ (middleRoots Q split i j : Set (X ⧸ Q.D)) at hh
  have hE : ((q).longOrbit 1).range = rootAt Q split j (Q.simple i) :=
    ModuleApplication.long_one_rootAt Q split (q) (w) (hl)
  have hD : ((q).shortOrbit 2).range = rootAt Q split i (Q.simple j*Q.simple i) :=
    RootGeometry.short_two_rootAt Q split (q) (w) (hs)
  have hF : ((q).longOrbit 2).range = rootAt Q split j (Q.simple i*Q.simple j) :=
    ModuleApplication.long_two_rootAt Q split (q) (w) (hl)
  rw [middleRoots_product Q split hm i j (indices.injective.ne (by decide)),
    ←hE,←hD,←hF] at hh
  obtain ⟨ed,⟨E,⟨u,rfl⟩,D,⟨b,rfl⟩,rfl⟩,F,⟨v,rfl⟩,hh⟩ := hh
  refine ⟨b.toAdd,u.toAdd,v.toAdd,?_⟩
  have he := congrArg ((q).s 1 (a*t.val) * ·) hh
  change _ = (q).s 1 (a*t.val) * ((q).longOrbit 1 u) * ((q).shortOrbit 2 b) * ((q).longOrbit 2 v)
  simpa only [mul_inv_cancel_left,mul_assoc] using he.symm

/-- Passing the actual group product to its radical abelianization removes
exactly the structural derived root F. -/
theorem mixedVector_decomposition (a : F) (t : K) :
    ∃ (b : F) (u v : K),
      rightCommutator ((q).l 0 t) ((q).s 0 a) =
        (q).s 1 (a*t.val) * (q).l 1 u * (q).s 2 b * (q).l 2 v ∧
      (mV) a t = (cV) (a*t.val) + Additive.ofMul (Abelianization.of ((eLift) u)) + (dV) b := by
  obtain ⟨b,u,v,he⟩ := mixed_decomposition Q split σ indices hVi hVj μi μj hm row e a t
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
  have hg : TensorRootAxes.mixedLift Q split σ indices hVi hVj μi μj hm row e a t =
      (cLift) (.ofAdd (a*t.val)) * (eLift) u * (dLift) (.ofAdd b) * fv := by
    apply Subtype.ext
    change _ = ((cLift) (.ofAdd (a*t.val)) : X ⧸ Q.D) *
      ((eLift) u : X ⧸ Q.D) * ((dLift) (.ofAdd b) : X ⧸ Q.D) * (fv : X ⧸ Q.D)
    rw [TensorRootAxes.mixedLift_coe,nextLift_coe,TensorRootAxes.upperLift_coe,middleLift_coe]
    exact he
  refine ⟨b,u,v,he,?_⟩
  change Additive.ofMul (Abelianization.of _) = _
  rw [hg]
  simp only [map_mul,hz,mul_one]
  rfl

variable [hEA : IsElementaryAbelian 2 (RadicalQuotient Q split (indices 0))]
include hEA
local notation "ρ" => TensorApplication.sourceAction Q split indices hVi μi (hEA := hEA)

theorem weyl_nextVector (a : F) : (ρ) (weyl F) ((cV) a) = (dV) a :=
  radicalRepresentation_of Q split i hVi _ _

/-- Conjugation by an actual short upper root moves D only along E. -/
theorem middle_upper (a b : F) : ∃ t : K,
    rightCommutator ((q).s 2 b) ((q).s 0 a) = (q).l 1 t ∧
    (ρ) (uni a) ((dV) b) = (dV) b + Additive.ofMul (Abelianization.of ((eLift) t)) := by
  obtain ⟨t,ht⟩ := lower_commutator_range Q split σ indices hVi hVj μi μj hm row e a b
  refine ⟨t,ht,?_⟩
  have he : (q).s 0 a * (q).s 2 b * ((q).s 0 a)⁻¹ = (q).s 2 b * (q).l 1 t := by
    rw [←ht,short_inv]
    simp only [rightCommutator,short_inv]
    have hD : (q).s 2 b * (q).s 2 b = 1 := by
      simpa only [short_inv] using inv_mul_cancel ((q).s 2 b)
    simp only [←mul_assoc,hD,one_mul]
  have hv := TensorApplication.action_conjugation Q split σ indices hVi hVj μi μj hm e row
    (uni a) ((dLift) (.ofAdd b)) (((dLift) (.ofAdd b))*((eLift) t)) (by
      change ((dLift) (.ofAdd b) : X ⧸ Q.D) * ((eLift) t : X ⧸ Q.D) = _
      rw [middleLift_coe,TensorRootAxes.upperLift_coe]
      exact he.symm)
  change (ρ) (uni a) (Additive.ofMul (Abelianization.of ((dLift) (.ofAdd b)))) = _
  rw [hv,map_mul]
  rfl

section Chart
variable {C : Type*} [Field C] (κ : F →+* C)
  (J : Additive (RadicalQuotient Q split (indices 0)) →+ TripleSpace C)
  (c : ScalarMarking.SourceFixed (σ := σ) →+ C)

theorem middle_support
  (hact : ∀ (g : SL(2,F)) (v : Additive (RadicalQuotient Q split (indices 0))), J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
  (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
    c t • TensorCoordinates.basis ((0,0),0))

    (b : F) :
    TensorCoordinates.coordinates (J ((dV) b)) ((1,1),1) = 0 ∧
    TensorCoordinates.coordinates (J ((dV) b)) ((1,1),0) = 0 ∧
    TensorCoordinates.coordinates (J ((dV) b)) ((1,0),1) = 0 ∧
    TensorCoordinates.coordinates (J ((dV) b)) ((0,1),1) = 0 := by
  apply TensorFiltration.upper_displacement_top κ σ e.cubic (scalarMarking_exists_nonfixed e)
  intro a
  obtain ⟨t,_,ht⟩ := middle_upper Q split σ indices hVi hVj μi μj hm row e a b
  refine ⟨c t,?_⟩
  rw [←hact,ht,map_add,hE]

theorem next_support
  (hact : ∀ (g : SL(2,F)) (v : Additive (RadicalQuotient Q split (indices 0))), J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
  (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
    c t • TensorCoordinates.basis ((0,0),0))

    (b : F) :
    TensorCoordinates.coordinates (J ((cV) b)) ((0,0),0) = 0 ∧
    TensorCoordinates.coordinates (J ((cV) b)) ((0,0),1) = 0 ∧
    TensorCoordinates.coordinates (J ((cV) b)) ((0,1),0) = 0 ∧
    TensorCoordinates.coordinates (J ((cV) b)) ((1,0),0) = 0 := by
  have hh := middle_support Q split σ indices hVi hVj μi μj hm row e κ J c hact hE b
  rw [←weyl_nextVector,hact] at hh
  simpa only [TensorCoordinates.weyl_coordinates,show (1:Fin 2)-1=0 from rfl,
    show (1:Fin 2)-0=1 from rfl] using hh
/-- Comparing the two literal sections fixes the three leading tensor
coordinates and kills the residual bottom coordinate of C. -/
theorem leading_coordinates
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (a : F) (t : K) :
    TensorCoordinates.coordinates (J ((cV) (a*t.val))) ((0,1),1) = c t*κ a ∧
    TensorCoordinates.coordinates (J ((cV) (a*t.val))) ((1,0),1) = c t*κ (σ a) ∧
    TensorCoordinates.coordinates (J ((cV) (a*t.val))) ((1,1),0) = c t*κ (σ (σ a)) ∧
    TensorCoordinates.coordinates (J ((cV) (a*t.val))) ((1,1),1) = 0 := by
  obtain ⟨b,u,v,_,hu⟩ := mixedVector_decomposition Q split σ indices hVi hVj μi μj hm row e a t
  have hd := middle_support Q split σ indices hVi hVj μi μj hm row e κ J c hact hE b
  have he := congrArg (fun v => TensorCoordinates.coordinates (J v)) hu
  simp only [map_add,hE] at he
  have hc (r s k : Fin 2) := congrFun he ((r,s),k)
  have hM := TensorRootAxes.mixed_coordinates Q split σ indices hVi hVj μi μj hm row e
    κ J c hact hB a t
  constructor
  · have hh := hc 0 1 1
    rw [hM] at hh
    simp only [Pi.add_apply,hd.2.2.2,add_zero] at hh
    simpa [TensorCoordinates.coordinates] using hh.symm
  constructor
  · have hh := hc 1 0 1
    rw [hM] at hh
    simp only [Pi.add_apply,hd.2.2.1,add_zero] at hh
    simpa [TensorCoordinates.coordinates] using hh.symm
  constructor
  · have hh := hc 1 1 0
    rw [hM] at hh
    simp only [Pi.add_apply,hd.2.1,add_zero] at hh
    simpa [TensorCoordinates.coordinates] using hh.symm
  · have hh := hc 1 1 1
    rw [hM] at hh
    simp only [Pi.add_apply,hd.1,add_zero] at hh
    simpa [TensorCoordinates.coordinates] using hh.symm

/-- The normalized long-axis coefficient is the restriction of the same
extension-field embedding. This discharges the previously additive-only
scalar ambiguity uniformly, including q=2 and q=4. -/
theorem coefficient_eq_embedding
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (hc : c 1 = 1) (t : K) : c t = κ t.val := by
  have h1 := (leading_coordinates Q split σ indices hVi hVj μi μj hm row e
    κ J c hact hE hB 1 t).1
  have ht := (leading_coordinates Q split σ indices hVi hVj μi μj hm row e
    κ J c hact hE hB t.val 1).1
  simp only [one_mul,map_one,mul_one,hc,Subfield.coe_one] at h1 ht
  exact h1.symm.trans ht

/-- All eight coordinates of the literal first short orbit, with its original
whole-pinning field label. -/
theorem next_coordinates
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (hc : c 1 = 1) (a : F) (r s k : Fin 2) :
    TensorCoordinates.coordinates (J ((cV) a)) ((r,s),k) =
      if ((r,s),k) = ((0,1),1) then κ a else
      if ((r,s),k) = ((1,0),1) then κ (σ a) else
      if ((r,s),k) = ((1,1),0) then κ (σ (σ a)) else 0 := by
  have h0 := next_support Q split σ indices hVi hVj μi μj hm row e κ J c hact hE a
  have h1 := leading_coordinates Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB a 1
  simp only [Subfield.coe_one,mul_one,hc,one_mul] at h1
  fin_cases r <;> fin_cases s <;> fin_cases k <;> simp_all

/-- The same short Weyl lift gives the complementary three middle
coordinates, retaining the original Frobenius conventions. -/
theorem middle_coordinates
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (hc : c 1 = 1) (a : F) (r s k : Fin 2) :
    TensorCoordinates.coordinates (J ((dV) a)) ((r,s),k) =
      if ((r,s),k) = ((1,0),0) then κ a else
      if ((r,s),k) = ((0,1),0) then κ (σ a) else
      if ((r,s),k) = ((0,0),1) then κ (σ (σ a)) else 0 := by
  rw [←weyl_nextVector,hact,TensorCoordinates.weyl_coordinates,
    next_coordinates Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc]
  fin_cases r <;> fin_cases s <;> fin_cases k <;> rfl

/-- The tensor calculation now proves the full lifted lower trace pairing,
not merely its image modulo the radical's derived subgroup. The structural
range theorem puts the commutator in E before comparing its faithful scalar. -/
theorem lower_pairing
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (hc : c 1 = 1) (a b : F) :
    rightCommutator ((q).s 2 b) ((q).s 0 a) = (q).l 1 (e.trace (a*b)) := by
  obtain ⟨t,ht,hv⟩ := middle_upper Q split σ indices hVi hVj μi μj hm row e a b
  have hh := congrArg (fun v => TensorCoordinates.coordinates (J v) ((0,0),0)) hv
  rw [hact,TensorCoordinates.action] at hh
  change TensorCoordinates.upper κ σ a (TensorCoordinates.coordinates (J ((dV) b))) ((0,0),0) = _ at hh
  rw [TensorCoordinates.upper_000] at hh
  simp only [map_add,hE,Pi.add_apply,
    middle_coordinates Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc] at hh
  simp only [coefficient_eq_embedding Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc] at hh
  simp [TensorCoordinates.coordinates] at hh
  have ht' : t = e.trace (a*b) := by
    apply Subtype.ext
    apply κ.injective
    change κ t.val = κ (a*b + σ (a*b) + σ (σ (a*b)))
    rw [←hh]
    simp only [map_add,map_mul]
    ring
  exact ht'.symm ▸ ht

/-- The original long Weyl lift transports the same field pairing to F. -/
theorem upper_pairing
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (hc : c 1 = 1) (a b : F) :
    rightCommutator ((q).s 2 b) ((q).s 1 a) = (q).l 2 (e.trace (a*b)) :=
  PinnedApplication.upper_from_lower (q) e
    (lower_pairing Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc) a b

/-- The tensor coordinates determine every factor of the actual mixed
product except its final derived-root coefficient. This lifts the section
calculation to an equality in the original source group. -/
theorem mixed_product
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((eLift) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (hc : c 1 = 1) (a : F) (t : K) :
    ∃ v : K, rightCommutator ((q).l 0 t) ((q).s 0 a) =
      (q).s 1 (a*t.val) * (q).s 2 (σ a*σ (σ a)*t.val) *
        (q).l 1 (e.norm a*t) * (q).l 2 v := by
  obtain ⟨b,u,v,hg,hv⟩ := mixedVector_decomposition Q split σ indices hVi hVj μi μj hm row e a t
  have he := congrArg (fun z => TensorCoordinates.coordinates (J z)) hv
  simp only [map_add,hE] at he
  have hM := TensorRootAxes.mixed_coordinates Q split σ indices hVi hVj μi μj hm row e
    κ J c hact hB a t
  have hb : b = σ a*σ (σ a)*t.val := by
    have hh := congrFun he ((1,0),0)
    rw [hM] at hh
    simp only [Pi.add_apply,
      next_coordinates Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc,
      middle_coordinates Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc,
      coefficient_eq_embedding Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc] at hh
    simp [TensorCoordinates.coordinates] at hh
    apply κ.injective
    rw [←hh,map_mul,map_mul]
    ring
  have hu : u = e.norm a*t := by
    have hh := congrFun he ((0,0),0)
    rw [hM] at hh
    simp only [Pi.add_apply,
      next_coordinates Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc,
      middle_coordinates Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc,
      coefficient_eq_embedding Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc] at hh
    simp [TensorCoordinates.coordinates] at hh
    apply Subtype.ext
    apply κ.injective
    change κ u.val = κ ((a*σ a*σ (σ a))*t.val)
    rw [←hh,map_mul,map_mul,map_mul]
    ring
  refine ⟨v,?_⟩
  rw [hg,hb,hu]
  have hcDE := ((cc).short2_long1 (σ a*σ (σ a)*t.val) (e.norm a*t)).eq
  simpa only [mul_assoc] using congrArg
    (fun z => (q).s 1 (a*t.val) * z * (q).l 2 v) hcDE.symm

end Chart
omit hEA in
/-- Both source trace pairings and the lifted mixed product are now derived
on the original marked quotient, with no chart or matrix assumptions.
The last mixed coefficient remains an actual element of the derived root;
its covariance and normalization are further source obligations. -/
theorem constructed_relations :
    (∀ a b : F, rightCommutator ((q).s 2 b) ((q).s 0 a) = (q).l 1 (e.trace (a*b))) ∧
    (∀ a b : F, rightCommutator ((q).s 2 b) ((q).s 1 a) = (q).l 2 (e.trace (a*b))) ∧
    (∀ (a : F) (t : K), ∃ v : K, rightCommutator ((q).l 0 t) ((q).s 0 a) =
      (q).s 1 (a*t.val) * (q).s 2 (σ a*σ (σ a)*t.val) *
        (q).l 1 (e.norm a*t) * (q).l 2 v) := by
  let hEA := linear_pair_radicalQuotient_elementary Q split hm j i
    (indices.injective.ne (by decide)) μj μi
  let := TensorApplication.irreducible Q split σ indices hVi hVj μi μj hm e
  obtain ⟨κ,J,c,_,_,hc,hact,hE,hB⟩ :=
    TensorRootAxes.source_axes Q split σ indices hVi hVj μi μj hm row e
  exact ⟨lower_pairing Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc,
    upper_pairing Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc,
    mixed_product Q split σ indices hVi hVj μi μj hm row e κ J c hact hE hB hc⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorMiddleRoots
