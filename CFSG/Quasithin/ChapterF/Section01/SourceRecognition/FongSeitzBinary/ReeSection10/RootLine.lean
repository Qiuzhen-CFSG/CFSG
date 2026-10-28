module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.NaturalAlignment
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.PositiveCharts
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.LayerOrders

/-!
# The first distinguished source line in V₂

The reflected linear root U₁^s₂ centralizes U₂ and intersects T₂ trivially:
conjugation by the literal reflection takes it to U₁ and preserves T₂,
which lies in the linear remainder. Its faithful image in V₂ therefore lies
in the first matrix coordinate line. Equal cardinalities make it the whole
line, also when q = 2. Reading that coordinate is an additive isomorphism;
composing it with the existing positive chart gives the actual field-label
change. Multiplicativity and the other distinguished lines remain to be
established by the source commutator comparison.

Source: Fong--Seitz II (1974), printed pp.221--223, (10.4) and (10.7).
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open ReeF4
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

include c in
theorem reflectedLinear_le_suzukiRemainder :
    positiveRoot Q split (.inl 1) ≤ simpleRemainder Q split 1 :=
  (octagon_three_roots_le_remainder Q split c.rotation_eight 1 0 (by decide)).1

include c in
theorem reflectedLinear_disjoint_T2 :
    Disjoint (positiveRoot Q split (.inl 1)) (T2 Q split) := by
  apply disjoint_def.mpr
  intro x hx ht
  let s := (c.reflections 1).val
  have hx' : (s : X ⧸ Q.D) * x * (s : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split 0 := by
    change x ∈ rootAt Q split 0 (Q.simple 1) at hx
    rw [rootAt_eq Q split 0 _ s (c.reflections 1).class_eq] at hx
    exact hx
  have ht' := (mem_normalizer_iff.mp
    (rankOne_normalizes_T2 Q split c (c.reflections 1).mem_rankOne) x).mp ht
  have he := disjoint_def.mp (simpleRoot_disjoint_remainder Q split 0)
    hx' (T2_le_linearRemainder Q split c ht')
  exact (MulAut.conj (s : X ⧸ Q.D)).injective (he.trans (map_one _).symm)

/-- The literal reflected linear root maps injectively into V₂. -/
def V2ReflectedLinear : positiveRoot Q split (.inl 1) →* (V2Section Q split c).Carrier :=
  (QuotientGroup.mk' (V2Section Q split c).denominator).comp
    (inclusion (reflectedLinear_le_suzukiRemainder Q split c))

theorem V2ReflectedLinear_injective : Function.Injective (V2ReflectedLinear Q split c) := by
  apply (V2ReflectedLinear Q split c).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  have ht : (x : X ⧸ Q.D) ∈ T2 Q split := by
    change QuotientGroup.mk' (V2Section Q split c).denominator
      (inclusion (reflectedLinear_le_suzukiRemainder Q split c) x) = 1 at hx
    change inclusion (reflectedLinear_le_suzukiRemainder Q split c) x ∈
      (QuotientGroup.mk' (V2Section Q split c).denominator).ker at hx
    rw [QuotientGroup.ker_mk'] at hx
    exact hx
  exact Subtype.ext (disjoint_def.mp (reflectedLinear_disjoint_T2 Q split c) x.property ht)

include c in
theorem reflectedLinear_centralizes_suzukiRoot :
    ⁅simpleRoot Q split 1, positiveRoot Q split (.inl 1)⁆ = ⊥ :=
  adjacent_commutator_eq_bot Q split c.rotation_eight 1 0 (by decide)
    (remainder_le_kernel Q split c)
    (remainder_le_panelKernel_of_marking Q split 0 c.linear c.linearSylow c.linearBorel
      (linear_normalizer_index c.linearSylow))

theorem V2Coordinates_reflectedLinear (a : positiveRoot Q split (.inl 1)) :
    V2Coordinates Q split c (Additive.ofMul (V2ReflectedLinear Q split c a)) =
      ![V2Coordinates Q split c (Additive.ofMul (V2ReflectedLinear Q split c a)) 0,0,0,0] := by
  apply Representation.SuzukiNatural.root_fixed_coordinates
  intro g hg
  let u := (suzukiRootEquiv Q split 1 m c.suzuki c.suzukiBorel).symm ⟨g,hg⟩
  let r : rankOne Q split 1 := inclusion le_sup_left u
  let v : simpleRemainder Q split 1 := inclusion (reflectedLinear_le_suzukiRemainder Q split c) a
  have hr : suzukiActorEquiv Q split 1 m c.suzuki c.suzukiBorel r = g := by
    change (suzukiRootEquiv Q split 1 m c.suzuki c.suzukiBorel u : SuzukiMatrixGroup m) = g
    exact congrArg Subtype.val ((suzukiRootEquiv Q split 1 m c.suzuki c.suzukiBorel).apply_symm_apply ⟨g,hg⟩)
  have hc : Commute (u : X ⧸ Q.D) (a : X ⧸ Q.D) :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (reflectedLinear_centralizes_suzukiRoot Q split c) u.property) _ a.property).symm
  have hv : (V2Section Q split c).numeratorAction r v = v := by
    apply Subtype.ext
    change (u : X ⧸ Q.D) * a * (u : X ⧸ Q.D)⁻¹ = a
    rw [hc.eq, mul_inv_cancel_right]
  have h := V2Coordinates_source Q split c r v
  rw [hr,hv] at h
  exact h.symm

/-- The source field label read from the first natural coordinate of the
reflected linear root.  This keeps the label tied to the literal quotient. -/
def reflectedLinearCoordinate (a : positiveRoot Q split (.inl 1)) :
    Representation.SuzukiNatural.F m :=
  V2Coordinates Q split c
    (Additive.ofMul (V2ReflectedLinear Q split c a)) 0

theorem reflectedLinearCoordinate_injective :
    Function.Injective (reflectedLinearCoordinate Q split c) := by
  intro a b hab
  apply V2ReflectedLinear_injective Q split c
  apply (V2Coordinates Q split c).injective
  change V2Coordinates Q split c (Additive.ofMul (V2ReflectedLinear Q split c a)) =
    V2Coordinates Q split c (Additive.ofMul (V2ReflectedLinear Q split c b))
  rw [V2Coordinates_reflectedLinear Q split c a,
    V2Coordinates_reflectedLinear Q split c b]
  funext i
  fin_cases i
  · exact hab
  all_goals rfl

theorem reflectedLinearCoordinate_bijective :
    Function.Bijective (reflectedLinearCoordinate Q split c) := by
  apply (reflectedLinearCoordinate_injective Q split c).bijective_of_nat_card_le
  rw [GaloisField.card 2 (2*m+1) (by omega),
    linear_positiveRoot_card Q split c 1]

/-- Reading the first natural coordinate after the source positive chart gives
an explicit bijective label on the common coefficient field.  No field
homomorphism is asserted here; the later commutator comparison determines its
normalization and twist. -/
theorem reflectedLinearCoordinate_chart_bijective
    (σ : CoefficientField m ≃+* CoefficientField m) :
    Function.Bijective (fun a : CoefficientField m =>
      reflectedLinearCoordinate Q split c
        (positiveChart Q split c σ (.inl 1) a)) :=
  (reflectedLinearCoordinate_bijective Q split c).comp
    (positiveChart Q split c σ (.inl 1)).bijective

def reflectedLinearLabelHom : positiveRoot Q split (.inl 1) →*
    Multiplicative (Representation.SuzukiNatural.F m) where
  toFun a := Multiplicative.ofAdd (reflectedLinearCoordinate Q split c a)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change V2Coordinates Q split c (Additive.ofMul (V2ReflectedLinear Q split c 1)) 0 = 0
    rw [map_one]
    change (V2Coordinates Q split c).toLinearEquiv 0 0 = 0
    rw [map_zero]
    rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    change V2Coordinates Q split c (Additive.ofMul (V2ReflectedLinear Q split c (a*b))) 0 =
      V2Coordinates Q split c (Additive.ofMul (V2ReflectedLinear Q split c a)) 0 +
      V2Coordinates Q split c (Additive.ofMul (V2ReflectedLinear Q split c b)) 0
    rw [map_mul]
    exact congrFun ((V2Coordinates Q split c).toLinearEquiv.map_add
      (Additive.ofMul (V2ReflectedLinear Q split c a))
      (Additive.ofMul (V2ReflectedLinear Q split c b))) 0

def reflectedLinearLabel : positiveRoot Q split (.inl 1) ≃*
    Multiplicative (Representation.SuzukiNatural.F m) :=
  MulEquiv.ofBijective (reflectedLinearLabelHom Q split c)
    (Multiplicative.ofAdd.bijective.comp (reflectedLinearCoordinate_bijective Q split c))

def reflectedLinearFieldLabel (σ : CoefficientField m ≃+* CoefficientField m) :
    CoefficientField m ≃+ CoefficientField m :=
  ((linearChart Q split c σ).trans
    ((positiveRootEquiv Q split c (.inl 1)).trans
      (reflectedLinearLabel Q split c))).toAdditive

theorem reflectedLinearFieldLabel_apply (σ : CoefficientField m ≃+* CoefficientField m)
    (a : CoefficientField m) : reflectedLinearFieldLabel Q split c σ a =
      reflectedLinearCoordinate Q split c (positiveChart Q split c σ (.inl 1) a) := rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
