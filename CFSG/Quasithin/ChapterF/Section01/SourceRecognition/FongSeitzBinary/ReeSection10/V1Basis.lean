module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.V1Natural

/-!
# The literal natural basis of the linear section

The simple Suzuki root maps to the second coordinate line of the faithful
natural V₁ module. Its kernel is exactly Omega, and its first-coordinate
quotient gives an additive field label. The supplied linear reflection
sends the corrected Suzuki chart to the first coordinate line with that
same label. Scaling the natural intertwiner once makes both parameter-one
vectors the coordinate unit vectors. This proves the root-vector assertion
in (10.6), in the pinned column convention, for every m, including m=0.

The label is an additive equivalence normalized at one. Its compatibility
with the other natural layers and the source field automorphisms must still
be derived by the commutator comparison (10.7)--(10.9); no multiplicativity
is assumed here. OriginalV1Basis applies the actual vectors and action to
the original radical, retaining both endpoint maps and Q.q.
Source: Fong--Seitz II (1974), printed pp.222--223, (10.6).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open Theory.PSL2.SemilinearCoverage
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)
local instance v1BasisBinaryAlgebra : Algebra (ZMod 2) (ReeF4.CoefficientField m) := ZMod.algebra _ 2

theorem V1Coordinates_shiftedRoot (a : positiveRoot Q split (.inr 2)) :
    V1Coordinates Q split c (Additive.ofMul (QuotientGroup.mk (inclusion
      (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) a))) =
      ![V1Coordinates Q split c (Additive.ofMul (QuotientGroup.mk (inclusion
        (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) a))) 0,0] := by
  let u := linearPinning Q split c (uni (1 : ReeF4.CoefficientField m))
  have hu : (u : X ⧸ Q.D) ∈ simpleRoot Q split 0 := by
    rw [←GTwoSource.alignedPinningHom_unip_map Q split 0
      (linearRemainder_le_kernel Q split c) (linearLocalMarking Q split c) (c.reflections 0)]
    exact mem_map_of_mem _ ((mem_Unip_iff _).mpr ⟨1,rfl⟩)
  have hc : Commute (u : X ⧸ Q.D) (a : X ⧸ Q.D) :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (adjacent_commutator_eq_bot Q split c.rotation_eight 0 1 (by decide)
        (linearRemainder_le_kernel Q split c) (remainder_le_kernel Q split c))
          hu) _ a.property).symm
  let v : (V1Section Q split c).numerator :=
    ⟨a,positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide) a.property⟩
  have hv : (V1Section Q split c).numeratorAction u v = v := by
    apply Subtype.ext
    change (u : X ⧸ Q.D) * a * (u : X ⧸ Q.D)⁻¹ = a
    rw [hc.eq,mul_inv_cancel_right]
  have hh := V1Coordinates_source Q split c u v
  rw [hv,show (linearPinning Q split c).symm u = uni 1 from
    (linearPinning Q split c).symm_apply_apply _] at hh
  let x := V1Coordinates Q split c (Additive.ofMul (QuotientGroup.mk v))
  have hx : x 1 = 0 := by
    have hh0 := congrFun hh 0
    change x 0 = (Representation.SL2.BinarySmall.natural (uni 1) x) 0 at hh0
    simp only [Representation.SL2.BinarySmall.natural_apply,uni_val,Matrix.mulVec,
      dotProduct,Fin.sum_univ_two] at hh0
    change x 0 = 1*x 0+1*x 1 at hh0
    simp only [one_mul] at hh0
    exact (add_left_cancel (hh0.symm.trans (add_zero (x 0)).symm))
  change x = ![x 0,0]
  ext i
  fin_cases i
  · rfl
  · exact hx


include c in
theorem simpleSuzuki_le_linearRemainder : simpleRoot Q split 1 ≤ simpleRemainder Q split 0 := by
  simpa only [positiveRoot,positiveKind,positiveWord,Matrix.cons_val_zero,rootAt_one] using
    positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)

/-- The literal simple Suzuki root in the linear quotient. -/
def V1SimpleRoot : simpleRoot Q split 1 →* (V1Section Q split c).Carrier :=
  (QuotientGroup.mk' _).comp (inclusion (simpleSuzuki_le_linearRemainder Q split c))

theorem V1SimpleRoot_kernel : (V1SimpleRoot Q split c).ker =
    (omegaOneAmbient (simpleRoot Q split 1)).subgroupOf (simpleRoot Q split 1) := by
  rw [V1SimpleRoot,←MonoidHom.comap_ker,QuotientGroup.ker_mk']
  ext x
  let z : positiveRoot Q split (.inr 0) := ⟨x,by
    simpa only [positiveRoot,positiveKind,positiveWord,Matrix.cons_val_zero,rootAt_one] using x.property⟩
  have hbar := linearBarBoundary_right Q split c z
  change inclusion (simpleSuzuki_le_linearRemainder Q split c) x ∈
    (X1 Q split).subgroupOf (simpleRemainder Q split 0) ↔ _
  rw [←linearBarBoundary_kernel Q split c,MonoidHom.mem_ker]
  change linearBarBoundary Q split c
    (inclusion (positiveRoot_le_remainder Q split c (.inr 0) 0 (by decide)) z) = 1 ↔ _
  rw [hbar]
  change (1,positiveSuzukiBar Q split c 0 z) = (1,1) ↔
    (x : X ⧸ Q.D) ∈ omegaOneAmbient (simpleRoot Q split 1)
  simp only [Prod.mk.injEq,true_and]
  simpa only [positiveRoot,positiveKind,positiveWord,Matrix.cons_val_zero,rootAt_one] using
    positiveSuzukiBar_eq_one Q split c 0 z

/-- First-coordinate labels on the actual quotient, with Omega killed. -/
def V1SimpleBar : Multiplicative (ReeF4.CoefficientField m) →* (V1Section Q split c).Carrier :=
  (QuotientGroup.lift _ (V1SimpleRoot Q split c) (V1SimpleRoot_kernel Q split c).ge).comp
    (suzukiOmegaQuotientEquiv Q split 1 m c.suzuki c.suzukiBorel).symm.toMonoidHom

theorem V1SimpleBar_parameter (a b : ReeF4.CoefficientField m) :
    V1SimpleBar Q split c (.ofAdd a) =
      V1SimpleRoot Q split c (suzukiParameter Q split 1 m c.suzuki c.suzukiBorel a b) := by
  rw [←suzukiOmegaQuotientEquiv_parameter Q split 1 m c.suzuki c.suzukiBorel a b]
  change QuotientGroup.lift _ (V1SimpleRoot Q split c) (V1SimpleRoot_kernel Q split c).ge ((suzukiOmegaQuotientEquiv Q split 1 m c.suzuki c.suzukiBorel).symm
    ((suzukiOmegaQuotientEquiv Q split 1 m c.suzuki c.suzukiBorel) _)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem V1SimpleBar_injective : Function.Injective (V1SimpleBar Q split c) := by
  apply (V1SimpleBar Q split c).ker_eq_bot_iff.mp
  apply bot_unique
  intro a ha
  obtain ⟨x,hx⟩ := (suzukiFirstCoordinate_surjective Q split 1 m c.suzuki c.suzukiBorel) a
  obtain ⟨⟨u,v⟩,rfl⟩ := (suzukiParameter_bijective Q split 1 m c.suzuki c.suzukiBorel).surjective x
  rw [suzukiFirstCoordinate_parameter] at hx
  rw [←hx] at ha ⊢
  have hz : V1SimpleRoot Q split c (suzukiParameter Q split 1 m c.suzuki c.suzukiBorel u v) = 1 := by
    rw [←V1SimpleBar_parameter]
    exact ha
  have hk : suzukiParameter Q split 1 m c.suzuki c.suzukiBorel u v ∈
      (suzukiFirstCoordinate Q split 1 m c.suzuki c.suzukiBorel).ker := by
    rw [suzukiFirstCoordinate_kernel,←V1SimpleRoot_kernel Q split c]
    exact hz
  exact (suzukiFirstCoordinate_parameter Q split 1 m c.suzuki c.suzukiBorel u v).symm.trans hk

/-- The supplied reflection sends the simple root to the opposite endpoint line. -/
theorem V1Coordinates_simpleRoot (a : simpleRoot Q split 1) :
    V1Coordinates Q split c (Additive.ofMul (V1SimpleRoot Q split c a)) =
      ![0,V1Coordinates Q split c (Additive.ofMul (V1SimpleRoot Q split c a)) 1] := by
  let v : (V1Section Q split c).numerator := inclusion (simpleSuzuki_le_linearRemainder Q split c) a
  let z := positiveRootEquiv Q split c (.inr 2) a
  have hv : (V1Section Q split c).numeratorAction
      ⟨(c.reflections 0).val,(c.reflections 0).mem_rankOne⟩ v =
      inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide)) z := by
    apply Subtype.ext
    change ((c.reflections 0).val : X ⧸ Q.D) * a * ((c.reflections 0).val : X ⧸ Q.D)⁻¹ = (z : X ⧸ Q.D)
    rw [show (z : X ⧸ Q.D) =
      ((c.reflections 0).val : X ⧸ Q.D)⁻¹ * a * (c.reflections 0).val from rfl,
      inv_eq_of_mul_eq_one_right (linearReflection_sq Q split c)]
  have hs := V1Coordinates_reflection Q split c v
  rw [hv] at hs
  have hz := congrFun (V1Coordinates_shiftedRoot Q split c z) 1
  rw [hs] at hz
  let x := V1Coordinates Q split c (Additive.ofMul (V1SimpleRoot Q split c a))
  have hx : x 0 = 0 := by
    change (Representation.SL2.BinarySmall.natural (weyl _) x) 1 = 0 at hz
    change (Matrix.mulVec !![0,1;1,0] x) 1 = 0 at hz
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_two] using hz
  change x = ![0,x 1]
  ext i
  fin_cases i
  · exact hx
  · rfl

def V1SourceLabelHom : ReeF4.CoefficientField m →+ ReeF4.CoefficientField m where
  toFun a := V1Coordinates Q split c (Additive.ofMul (V1SimpleBar Q split c (.ofAdd a))) 1
  map_zero' := by
    change V1Coordinates Q split c (Additive.ofMul (V1SimpleBar Q split c 1)) 1 = 0
    rw [map_one]
    exact congrFun (map_zero (V1Coordinates Q split c).toLinearEquiv) 1
  map_add' a b := by
    change V1Coordinates Q split c (Additive.ofMul
      (V1SimpleBar Q split c (.ofAdd a * .ofAdd b))) 1 = _
    rw [map_mul]
    exact congrFun ((V1Coordinates Q split c).toLinearEquiv.map_add _ _) 1

theorem V1Coordinates_simpleBar (a : ReeF4.CoefficientField m) :
    V1Coordinates Q split c (Additive.ofMul (V1SimpleBar Q split c (.ofAdd a))) =
      ![0,V1SourceLabelHom Q split c a] := by
  change V1Coordinates Q split c (Additive.ofMul (V1SimpleBar Q split c (.ofAdd a))) =
    ![0,V1Coordinates Q split c (Additive.ofMul (V1SimpleBar Q split c (.ofAdd a))) 1]
  rw [V1SimpleBar_parameter Q split c a 0]
  exact V1Coordinates_simpleRoot Q split c _

theorem V1SourceLabelHom_injective : Function.Injective (V1SourceLabelHom Q split c) := by
  intro a b hab
  have he : V1Coordinates Q split c (Additive.ofMul (V1SimpleBar Q split c (.ofAdd a))) =
      V1Coordinates Q split c (Additive.ofMul (V1SimpleBar Q split c (.ofAdd b))) := by
    rw [V1Coordinates_simpleBar,V1Coordinates_simpleBar,hab]
  exact V1SimpleBar_injective Q split c ((V1Coordinates Q split c).injective he)

def V1SourceLabel : ReeF4.CoefficientField m ≃+ ReeF4.CoefficientField m :=
  AddEquiv.ofBijective (V1SourceLabelHom Q split c)
    ⟨V1SourceLabelHom_injective Q split c,
      Finite.surjective_of_injective (V1SourceLabelHom_injective Q split c)⟩


/-- The corrected source Suzuki chart uses its literal first coordinate in V₁. -/
theorem V1Coordinates_suzukiChart (a b : ReeF4.CoefficientField m) :
    V1Coordinates Q split c (Additive.ofMul (V1SimpleRoot Q split c (suzukiChart Q split c (a,b)))) =
      ![0,V1SourceLabel Q split c a] := by
  rw [suzukiChart_apply,←V1SimpleBar_parameter]
  exact V1Coordinates_simpleBar Q split c a

/-- The opposite endpoint has the same additive label, using the supplied reflection. -/
theorem V1Coordinates_shiftedSuzukiChart (a b : ReeF4.CoefficientField m) :
    V1Coordinates Q split c (Additive.ofMul (QuotientGroup.mk
      (inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide))
        (positiveRootEquiv Q split c (.inr 2) (suzukiChart Q split c (a,b)))))) =
      ![V1SourceLabel Q split c a,0] := by
  let u := suzukiChart Q split c (a,b)
  let v : (V1Section Q split c).numerator := inclusion (simpleSuzuki_le_linearRemainder Q split c) u
  have hv : (V1Section Q split c).numeratorAction
      ⟨(c.reflections 0).val,(c.reflections 0).mem_rankOne⟩ v =
      inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide))
        (positiveRootEquiv Q split c (.inr 2) u) := by
    apply Subtype.ext
    change ((c.reflections 0).val : X ⧸ Q.D) * u * ((c.reflections 0).val : X ⧸ Q.D)⁻¹ =
      ((c.reflections 0).val : X ⧸ Q.D)⁻¹ * u * (c.reflections 0).val
    rw [inv_eq_of_mul_eq_one_right (linearReflection_sq Q split c)]
  have hs := V1Coordinates_reflection Q split c v
  rw [hv] at hs
  change V1Coordinates Q split c _ = Representation.SL2.BinarySmall.natural (weyl _)
    (V1Coordinates Q split c (Additive.ofMul (V1SimpleRoot Q split c u))) at hs
  rw [show u = suzukiChart Q split c (a,b) from rfl,V1Coordinates_suzukiChart] at hs
  refine hs.trans ?_
  change Matrix.mulVec !![0,1;1,0] ![0,V1SourceLabel Q split c a] = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]


theorem V1SourceLabel_one_ne_zero : V1SourceLabel Q split c 1 ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : ReeF4.CoefficientField m) ≠ 0)
    ((V1SourceLabel Q split c).injective (h.trans (map_zero _).symm))

/-- A common scalar normalizes both source endpoint vectors. -/
def V1BasisCoordinates : (linearV1Representation Q split c).Equiv
    (Representation.SL2.BinarySmall.natural (K := ReeF4.CoefficientField m)) :=
  (V1Coordinates Q split c).trans
    (Representation.Equiv.mk
      ((LinearEquiv.smulOfNeZero (ReeF4.CoefficientField m) (Fin 2 → ReeF4.CoefficientField m)
        (V1SourceLabel Q split c 1)⁻¹ (inv_ne_zero (V1SourceLabel_one_ne_zero Q split c))).restrictScalars (ZMod 2))
      (fun g => by
        apply LinearMap.ext
        intro v
        change (V1SourceLabel Q split c 1)⁻¹ • (Matrix.mulVec g.val v) =
          Matrix.mulVec g.val ((V1SourceLabel Q split c 1)⁻¹ • v)
        exact (Matrix.mulVec_smul _ _ _).symm))

theorem V1BasisCoordinates_apply (v : Additive (V1Section Q split c).Carrier) :
    V1BasisCoordinates Q split c v =
      (V1SourceLabel Q split c 1)⁻¹ • V1Coordinates Q split c v := rfl

/-- The common additive label is normalized at one; multiplicativity is a later source step. -/
def V1BasisLabel : ReeF4.CoefficientField m ≃+ ReeF4.CoefficientField m :=
  (V1SourceLabel Q split c).trans
    (LinearEquiv.smulOfNeZero (ReeF4.CoefficientField m) (ReeF4.CoefficientField m)
      (V1SourceLabel Q split c 1)⁻¹ (inv_ne_zero (V1SourceLabel_one_ne_zero Q split c))).toAddEquiv

@[simp] theorem V1BasisLabel_one : V1BasisLabel Q split c 1 = 1 :=
  inv_mul_cancel₀ (V1SourceLabel_one_ne_zero Q split c)

theorem V1BasisCoordinates_suzukiChart (a b : ReeF4.CoefficientField m) :
    V1BasisCoordinates Q split c (Additive.ofMul (V1SimpleRoot Q split c (suzukiChart Q split c (a,b)))) =
      ![0,V1BasisLabel Q split c a] := by
  rw [V1BasisCoordinates_apply,V1Coordinates_suzukiChart]
  ext i
  fin_cases i
  · exact mul_zero _
  · rfl

theorem V1BasisCoordinates_shiftedSuzukiChart (a b : ReeF4.CoefficientField m) :
    V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
      (inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide))
        (positiveRootEquiv Q split c (.inr 2) (suzukiChart Q split c (a,b)))))) =
      ![V1BasisLabel Q split c a,0] := by
  rw [V1BasisCoordinates_apply,V1Coordinates_shiftedSuzukiChart]
  ext i
  fin_cases i
  · rfl
  · exact mul_zero _

/-- Both printed parameter-one vectors, in the pinned column convention. -/
theorem V1_basis10_6 :
    V1BasisCoordinates Q split c (Additive.ofMul (V1SimpleRoot Q split c (suzukiChart Q split c (1,0)))) =
        ![0,1] ∧
    V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
      (inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide))
        (positiveRootEquiv Q split c (.inr 2) (suzukiChart Q split c (1,0)))))) = ![1,0] := by
  constructor
  · rw [V1BasisCoordinates_suzukiChart,V1BasisLabel_one]
  · rw [V1BasisCoordinates_shiftedSuzukiChart,V1BasisLabel_one]

/-- Normalization retains the same literal conjugation representation. -/
theorem V1BasisCoordinates_source (r : rankOne Q split 0) (v : (V1Section Q split c).numerator) :
    V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk
      ((V1Section Q split c).numeratorAction r v))) =
      Representation.SL2.BinarySmall.natural ((linearPinning Q split c).symm r)
        (V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk v))) := by
  have he := LinearMap.congr_fun ((V1BasisCoordinates Q split c).isIntertwining'
    ((linearPinning Q split c).symm r)) (Additive.ofMul (QuotientGroup.mk v))
  change V1BasisCoordinates Q split c
    (V1Representation Q split c ((linearPinning Q split c) ((linearPinning Q split c).symm r))
      (Additive.ofMul (QuotientGroup.mk v))) = _ at he
  rw [MulEquiv.apply_symm_apply] at he
  exact he


/-- The two printed representatives, ordered as {u₂(1), u₂(1)^s₁}. -/
def V1BasisPoint (i : Fin 2) : (V1Section Q split c).numerator :=
  ![inclusion (simpleSuzuki_le_linearRemainder Q split c) (suzukiChart Q split c (1,0)),
    inclusion (positiveRoot_le_remainder Q split c (.inr 2) 0 (by decide))
      (positiveRootEquiv Q split c (.inr 2) (suzukiChart Q split c (1,0)))] i

@[simp] theorem V1BasisPoint_zero :
    (V1BasisPoint Q split c 0 : X ⧸ Q.D) = suzukiChart Q split c (1,0) := rfl

@[simp] theorem V1BasisPoint_one :
    (V1BasisPoint Q split c 1 : X ⧸ Q.D) =
      ((c.reflections 0).val : X ⧸ Q.D)⁻¹ * suzukiChart Q split c (1,0) * (c.reflections 0).val := rfl

theorem V1BasisPoint_coordinates (i : Fin 2) :
    V1BasisCoordinates Q split c (Additive.ofMul (QuotientGroup.mk (V1BasisPoint Q split c i))) =
      ![![0,1],![1,0]] i := by
  fin_cases i
  · exact (V1_basis10_6 Q split c).1
  · exact (V1_basis10_6 Q split c).2

/-- The literal pair gives a basis after the natural identification. -/
theorem V1BasisPoint_isBasis :
    LinearIndependent (ReeF4.CoefficientField m)
      (fun i : Fin 2 => V1BasisCoordinates Q split c
        (Additive.ofMul (QuotientGroup.mk (V1BasisPoint Q split c i)))) ∧
    Submodule.span (ReeF4.CoefficientField m)
      (Set.range (fun i : Fin 2 => V1BasisCoordinates Q split c
        (Additive.ofMul (QuotientGroup.mk (V1BasisPoint Q split c i))))) = ⊤ := by
  let b := (Pi.basisFun (ReeF4.CoefficientField m) (Fin 2)).reindex (Equiv.swap 0 1)
  have he : (fun i : Fin 2 => V1BasisCoordinates Q split c
      (Additive.ofMul (QuotientGroup.mk (V1BasisPoint Q split c i)))) = b := by
    funext i j
    rw [V1BasisPoint_coordinates]
    fin_cases i <;> fin_cases j <;> simp [b,Pi.basisFun_apply]
  rw [he]
  exact ⟨b.linearIndependent,b.span_eq⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
