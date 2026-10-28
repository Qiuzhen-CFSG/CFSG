module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.LinearFrattini
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.ReflectedRoots

/-!
# The two whole unitary roots in the linear natural section

The crossed unitary root is fixed by the linear simple root, so its image
lies on the first natural coordinate axis. The specified linear reflection
swaps the axes and sends the whole simple unitary root to that crossed root.
The central Frattini kernel is exactly the intrinsic center on both roots;
the root orders therefore make both coordinate maps surjective.

For any full Hermitian chart, factoring these actual maps through the same
center constructs a single additive equivalence between its SU₃ field and
the SL₂ field. Both reflected roots use that same equivalence. It is not yet
asserted to be multiplicative: the remaining mixed equations must establish
compatibility of field multiplication and the center parameters.
The LinearApplication consumer constructs all hypotheses from the source.
Source: Fong--Seitz II (8C), pp.203--204,208, (8.14)--(8.15), (8.32)--(8.33).
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource

variable {X K : Type*} [Group X] [Field K] [Finite K] [CharP K 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (μ₀ : localGroup Q split i ≃* PSL(2,K))
  [Algebra (ZMod 2) K]
  (c : Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))
    ≃ₗ[ZMod 2] (Fin 2 → K))
  (hc : ∀ a v, c (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split i hVi)
    (alignedPinning Q split i hVi μ₀ s a) v) = Matrix.mulVec a.val (c v))

def linearNaturalSectionMap : simpleRemainder Q split i →* Multiplicative (Fin 2 → K) where
  toFun v := .ofAdd (c (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) v)))
  map_one' := by simp
  map_mul' v w := by simp only [map_mul,ofMul_mul,map_add,ofAdd_add]

include hc in
private theorem linearNaturalSectionMap_action (a : SL(2,K)) (v : simpleRemainder Q split i) :
    (linearNaturalSectionMap Q split i c (remainderRankOneAction Q split i hVi
      (alignedPinning Q split i hVi μ₀ s a) v)).toAdd =
        Matrix.mulVec a.val (linearNaturalSectionMap Q split i c v).toAdd := by
  have ht := hc a (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) v))
  change c (.ofMul (remainderFrattiniAction Q split i hVi (alignedPinning Q split i hVi μ₀ s a)
    (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) v))) = _ at ht
  rw [remainderFrattiniAction_mk] at ht
  exact ht

include hm hij hVj hc in
/-- The crossed whole unitary root lies on the first natural coordinate axis. -/
theorem crossed_unitary_linear_axis (v : simpleRemainder Q split i)
    (hv : (v : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i)) :
    (linearNaturalSectionMap Q split i c v).toAdd 1 = 0 := by
  let a := alignedPinning Q split i hVi μ₀ s (uni (1 : K))
  have ha : (a : X ⧸ Q.D) ∈ simpleRoot Q split i := by
    rw [←alignedSimpleParameter_range Q split i hVi μ₀ s]
    exact ⟨.ofAdd 1,rfl⟩
  have hcom := (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (adjacent_roots_commute Q split hm i j hij hVi hVj) ha) v hv).symm
  have hact : remainderRankOneAction Q split i hVi a v = v := by
    apply Subtype.ext
    rw [remainderRankOneAction_apply,hcom,mul_inv_cancel_right]
  have hh := congrFun (linearNaturalSectionMap_action Q split i hVi s μ₀ c hc (uni 1) v) 0
  change (linearNaturalSectionMap Q split i c (remainderRankOneAction Q split i hVi a v)).toAdd 0 = _ at hh
  rw [hact] at hh
  simpa [uni_val,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using hh.symm

include hc in
/-- The specified source reflection swaps the two natural coordinates. -/
theorem linear_reflection_coordinates (v : simpleRemainder Q split i) :
    (linearNaturalSectionMap Q split i c (remainderRankOneAction Q split i hVi
      (alignedPinning Q split i hVi μ₀ s (weyl K)) v)).toAdd =
      ![(linearNaturalSectionMap Q split i c v).toAdd 1,
        (linearNaturalSectionMap Q split i c v).toAdd 0] := by
  rw [linearNaturalSectionMap_action Q split i hVi s μ₀ c hc]
  ext k
  fin_cases k <;> simp [weyl,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

include hm hij hVj hc in
/-- Reflection places the whole simple unitary root on the second axis. -/
theorem simple_unitary_linear_axis (v : simpleRemainder Q split i)
    (hv : (v : X ⧸ Q.D) ∈ simpleRoot Q split j) :
    (linearNaturalSectionMap Q split i c v).toAdd 0 = 0 := by
  let w := remainderRankOneAction Q split i hVi (alignedPinning Q split i hVi μ₀ s (weyl K)) v
  have hw : (w : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i) := by
    rw [rootAt_eq Q split j (Q.simple i) s.val s.class_eq]
    change (s.val : X ⧸ Q.D)*(w : X ⧸ Q.D)*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j
    have hwv : (w : X ⧸ Q.D) = (s.val : X ⧸ Q.D)*v*(s.val : X ⧸ Q.D)⁻¹ := by
      rw [remainderRankOneAction_apply,alignedPinning_coe,alignedPinningHom_weyl]
    rw [hwv,inv_eq_of_mul_eq_one_right (sourceReflection_sq Q split i hVi μ₀ s)]
    have he : (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)*v*s.val)*s.val = v := by
      calc
        _ = ((s.val : X ⧸ Q.D)*s.val)*v*((s.val : X ⧸ Q.D)*s.val) := by group
        _ = _ := by rw [sourceReflection_sq Q split i hVi μ₀ s]; simp
    rwa [he]
  have hh := crossed_unitary_linear_axis Q split hm i j hij hVi hVj s μ₀ c hc w hw
  have hs := congrFun (linear_reflection_coordinates Q split i hVi s μ₀ c hc v) 1
  exact hs.symm.trans hh

def linearCrossedCoordinate : rootAt Q split j (Q.simple i) →* Multiplicative K where
  toFun d := .ofAdd ((linearNaturalSectionMap Q split i c
    (inclusion (opposite_roots_le_remainder Q split j i hij.symm).2 d)).toAdd 0)
  map_one' := by simp
  map_mul' d e := by
    simp only [map_mul,toAdd_mul,Pi.add_apply,ofAdd_add]

def linearSimpleCoordinate : simpleRoot Q split j →* Multiplicative K where
  toFun b := .ofAdd ((linearNaturalSectionMap Q split i c
    (inclusion (opposite_roots_le_remainder Q split j i hij.symm).1 b)).toAdd 1)
  map_one' := by simp
  map_mul' b d := by
    simp only [map_mul,toAdd_mul,Pi.add_apply,ofAdd_add]

include hc in
/-- The first and second source coordinates agree under the same reflection. -/
theorem linear_reflected_coordinate (b : simpleRoot Q split j) :
    linearCrossedCoordinate Q split i j hij c
      (reflectedUnitaryChart Q split i j s (MulEquiv.refl _) b) =
        linearSimpleCoordinate Q split i j hij c b := by
  let v := inclusion (opposite_roots_le_remainder Q split j i hij.symm).1 b
  have hv : inclusion (opposite_roots_le_remainder Q split j i hij.symm).2
      (reflectedUnitaryChart Q split i j s (MulEquiv.refl _) b) =
        remainderRankOneAction Q split i hVi (alignedPinning Q split i hVi μ₀ s (weyl K)) v := by
    apply Subtype.ext
    change (reflectedUnitaryChart Q split i j s (MulEquiv.refl _) b : X ⧸ Q.D) = _
    rw [reflectedUnitaryChart_apply,remainderRankOneAction_apply,alignedPinning_coe,alignedPinningHom_weyl]
    rw [inv_eq_of_mul_eq_one_right (sourceReflection_sq Q split i hVi μ₀ s)]
    rfl
  change Multiplicative.ofAdd ((linearNaturalSectionMap Q split i c _).toAdd 0) = _
  rw [hv,linear_reflection_coordinates Q split i hVi s μ₀ c hc]
  rfl



include hm hij hVj hc in
/-- The full crossed-root center is exactly the kernel of its natural coordinate. -/
theorem linearCrossedCoordinate_ker
    (hcentral : (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype ≤
      centralizer (simpleRemainder Q split i : Set (X ⧸ Q.D)))
    (hphi : frattini (simpleRemainder Q split i) = _root_.commutator (simpleRemainder Q split i))
    (hZ : _root_.commutator (simpleRoot Q split j) = center (simpleRoot Q split j)) :
    (linearCrossedCoordinate Q split i j hij c).ker = center (rootAt Q split j (Q.simple i)) := by
  ext d
  let v := inclusion (opposite_roots_le_remainder Q split j i hij.symm).2 d
  have hv : (v : X ⧸ Q.D) ∈ rootAt Q split j (Q.simple i) := d.property
  have haxis := crossed_unitary_linear_axis Q split hm i j hij hVi hVj s μ₀ c hc v hv
  constructor
  · intro hd
    have h0 : (linearNaturalSectionMap Q split i c v).toAdd 0 = 0 := congrArg Multiplicative.toAdd hd
    have he : (linearNaturalSectionMap Q split i c v).toAdd = 0 := by
      ext k
      fin_cases k
      · exact h0
      · exact haxis
    have hq : QuotientGroup.mk' (frattini (simpleRemainder Q split i)) v = 1 := by
      apply Additive.ofMul.injective
      exact c.injective (he.trans c.map_zero.symm)
    have hm := hcentral (mem_map_of_mem (simpleRemainder Q split i).subtype ((QuotientGroup.eq_one_iff v).mp hq))
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_centralizer_iff.mp hm x ((opposite_roots_le_remainder Q split j i hij.symm).2 x.property)
  · intro hd
    have hmem : (d : X ⧸ Q.D) ∈ ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i)⁆ := by
      rw [crossed_derived_center_eq Q split i j s hZ]
      exact ⟨d,hd,rfl⟩
    have hmem' := commutator_mono (opposite_roots_le_remainder Q split j i hij.symm).2
      (opposite_roots_le_remainder Q split j i hij.symm).2 hmem
    rw [←map_subtype_commutator,←hphi] at hmem'
    obtain ⟨w,hw,he⟩ := hmem'
    have hwv : w = v := Subtype.ext he
    have hq : QuotientGroup.mk' (frattini (simpleRemainder Q split i)) v = 1 :=
      (QuotientGroup.eq_one_iff v).mpr (hwv ▸ hw)
    change Multiplicative.ofAdd (c (.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) v)) 0) = 1
    rw [hq]
    change Multiplicative.ofAdd (c 0 0) = 1
    rw [map_zero]
    rfl

include hc in
/-- The simple-root kernel has the same full-center description. -/
theorem linearSimpleCoordinate_ker
    (hker : (linearCrossedCoordinate Q split i j hij c).ker = center (rootAt Q split j (Q.simple i))) :
    (linearSimpleCoordinate Q split i j hij c).ker = center (simpleRoot Q split j) := by
  let e := reflectedUnitaryChart Q split i j s (MulEquiv.refl _)
  ext b
  change linearSimpleCoordinate Q split i j hij c b = 1 ↔ b ∈ _
  rw [←linear_reflected_coordinate Q split i j hij hVi s μ₀ c hc]
  change e b ∈ (linearCrossedCoordinate Q split i j hij c).ker ↔ b ∈ _
  rw [hker]
  simp only [mem_center_iff]
  constructor
  · intro h x
    apply e.injective
    simpa only [map_mul] using h (e x)
  · intro h x
    obtain ⟨y,rfl⟩ := e.surjective x
    simpa only [map_mul] using congrArg e (h y)

omit [CharP K 2] in
/-- The first coordinate covers the entire linear coefficient field. -/
theorem linearCrossedCoordinate_surjective {n : ℕ}
    (hK : Nat.card K = (2^n)^2)
    (hD : Nat.card (rootAt Q split j (Q.simple i)) = (2^n)^3)
    (hZD : Nat.card (center (rootAt Q split j (Q.simple i))) = 2^n)
    (hker : (linearCrossedCoordinate Q split i j hij c).ker = center (rootAt Q split j (Q.simple i))) :
    Function.Surjective (linearCrossedCoordinate Q split i j hij c) := by
  apply MonoidHom.surjective_of_card_ker_le_div
  rw [hker,hZD,hD]
  change 2^n ≤ (2^n)^3 / Nat.card K
  rw [hK]
  apply (Nat.le_div_iff_mul_le (pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) n) 2)).mpr
  exact le_of_eq (by ring)

include hc in
/-- Both axes use the same surjective coefficient coordinate. -/
theorem linearSimpleCoordinate_surjective
    (hsurj : Function.Surjective (linearCrossedCoordinate Q split i j hij c)) :
    Function.Surjective (linearSimpleCoordinate Q split i j hij c) := by
  intro x
  obtain ⟨d,hd⟩ := hsurj x
  obtain ⟨b,rfl⟩ := (reflectedUnitaryChart Q split i j s (MulEquiv.refl _)).surjective d
  exact ⟨b,(linear_reflected_coordinate Q split i j hij hVi s μ₀ c hc b).symm.trans hd⟩



include hc in
/-- The whole SU₃ root and its reflection have one common additive label in
the actual SL₂ section. This label is constructed from the two source maps. -/
theorem linear_full_root_labels {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2) (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (b : BenderSuzuki.External.hermitianUnipotentCoord J ≃* simpleRoot Q split j)
    (hker : (linearCrossedCoordinate Q split i j hij c).ker = center (rootAt Q split j (Q.simple i)))
    (hsurj : Function.Surjective (linearCrossedCoordinate Q split i j hij c)) :
    ∃ f : E ≃+ K, ∀ p : BenderSuzuki.External.hermitianUnipotentCoord J,
      linearSimpleCoordinate Q split i j hij c (b p) = .ofAdd (f p.val.1) ∧
      linearCrossedCoordinate Q split i j hij c (reflectedUnitaryChart Q split i j s b p) = .ofAdd (f p.val.1) := by
  let d := reflectedUnitaryChart Q split i j s b
  let δ := (linearCrossedCoordinate Q split i j hij c).comp d.toMonoidHom
  let π := HermitianForm.BinaryRootFrattini.firstCoordinate J
  have hkπ : π.ker = center (BenderSuzuki.External.hermitianUnipotentCoord J) := by
    apply le_antisymm (HermitianForm.BinaryRootFrattini.first_kernel_central J)
    rw [binary_coord_center J hn hE hfixed]
    rintro p ⟨z,rfl⟩
    rfl
  have hk : π.ker = δ.ker := by
    rw [hkπ]
    ext p
    change p ∈ center _ ↔ d p ∈ (linearCrossedCoordinate Q split i j hij c).ker
    rw [hker]
    simp only [mem_center_iff]
    constructor
    · intro hp x
      obtain ⟨y,rfl⟩ := d.surjective x
      simpa only [map_mul] using congrArg d (hp y)
    · intro hp x
      apply d.injective
      simpa only [map_mul] using hp (d x)
  let a := QuotientGroup.liftEquiv π.ker
    (HermitianForm.BinaryRootFrattini.firstCoordinate_surjective J hE hfixed) rfl
  let a' := QuotientGroup.liftEquiv π.ker (hsurj.comp d.surjective) hk
  let f : E ≃+ K := AddEquiv.toMultiplicative.symm (a.symm.trans a')
  have hf (p : BenderSuzuki.External.hermitianUnipotentCoord J) :
      δ p = .ofAdd (f p.val.1) := by
    change a' (QuotientGroup.mk' π.ker p) = a' (a.symm (a (QuotientGroup.mk' π.ker p)))
    rw [a.symm_apply_apply]
  refine ⟨f,fun p => ⟨?_,hf p⟩⟩
  exact (linear_reflected_coordinate Q split i j hij hVi s μ₀ c hc (b p)).symm.trans (hf p)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
