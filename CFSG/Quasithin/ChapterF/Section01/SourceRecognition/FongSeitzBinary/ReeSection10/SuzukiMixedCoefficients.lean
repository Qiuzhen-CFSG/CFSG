module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.AngularAssembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.RankOneCentralization

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory ReeF4
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

def suzukiMixedRootPoint (i : RootPresentationRecognition.PositiveTables.Root)
    (hi : i ≠ .inr 0) (a : RootPresentationRecognition.PositiveTables.Parameter m i) :
    (V2Section Q split (pinnedInput Q split c)).numerator :=
  inclusion (positiveRoot_le_remainder Q split (pinnedInput Q split c) i 1 hi)
    (synchronizedPositiveChart Q split c i a)

/-- The literal right commutator of the opposite and simple whole Suzuki roots. -/
def synchronizedSuzukiMixed (a b y z : CoefficientField m) :
    (V2Section Q split (pinnedInput Q split c)).numerator :=
  V2RightCommutator Q split (pinnedInput Q split c)
    (suzukiChart Q split (pinnedInput Q split c) (a,b))
    (suzukiMixedRootPoint Q split c (.inr 2) (by decide) (y,z))

theorem synchronizedSuzukiMixed_coordinates (a b y z : CoefficientField m) :
    V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk (synchronizedSuzukiMixed Q split c a b y z))) =
      ![(b*y)*pinnedLinearV2Label Q split c 1,
        (titsEnd m a*y)*pinnedLinearV2Label Q split c 1,0,0] := by
  have h := V2RightCommutator_coordinates Q split (pinnedInput Q split c) a b
    (suzukiMixedRootPoint Q split c (.inr 2) (by decide) (y,z))
  dsimp only at h
  rw [show V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk (suzukiMixedRootPoint Q split c (.inr 2) (by decide) (y,z)))) =
      ![0,0,y*pinnedLinearV2Label Q split c 1,0] from
    synchronized_opposite_coordinates Q split c y z] at h
  change V2Coordinates Q split (pinnedInput Q split c)
      (Additive.ofMul (QuotientGroup.mk (V2RightCommutator Q split (pinnedInput Q split c)
        (suzukiChart Q split (pinnedInput Q split c) (a,b))
        (suzukiMixedRootPoint Q split c (.inr 2) (by decide) (y,z))))) = _
  rw [h]
  ext i
  fin_cases i <;> simp <;> ring

theorem synchronizedSuzukiMixed_val (a b y z : CoefficientField m) :
    (synchronizedSuzukiMixed Q split c a b y z : X ⧸ Q.D) =
      (synchronizedPositivePoint Q split c (.inr 2) (y,z))⁻¹ *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D)⁻¹ *
      synchronizedPositivePoint Q split c (.inr 2) (y,z) *
      (suzukiChart Q split (pinnedInput Q split c) (a,b) : X ⧸ Q.D) :=
  V2RightCommutator_val Q split (pinnedInput Q split c) _ _

theorem synchronizedSuzukiMixed_support (a b y z : CoefficientField m) :
    ∃ p v l w t r s : CoefficientField m,
      (synchronizedSuzukiMixed Q split c a b y z : X ⧸ Q.D) =
        synchronizedPositivePoint Q split c (.inl 2) p *
        synchronizedPositivePoint Q split c (.inr 1) (v,l) *
        synchronizedPositivePoint Q split c (.inl 3) w *
        synchronizedPositivePoint Q split c (.inr 3) (t,r) *
        synchronizedPositivePoint Q split c (.inl 1) s := by
  have hk : (synchronizedSuzukiMixed Q split c a b y z : X ⧸ Q.D) ∈
      ⁅simpleRoot Q split 1,positiveRoot Q split (.inr 2)⁆ := by
    rw [synchronizedSuzukiMixed_val]
    rw [commutator_comm]
    have h := commutator_mem_commutator
      ((positiveRoot Q split (.inr 2)).inv_mem
        (synchronizedPositiveChart Q split c (.inr 2) (y,z)).property)
      ((simpleRoot Q split 1).inv_mem
        (suzukiChart Q split (pinnedInput Q split c) (a,b)).property)
    simpa only [commutatorElement_def,inv_inv,synchronizedPositivePoint] using h
  obtain ⟨⟨p,v,w,t,s,e⟩,hk⟩ := V2_cross_commutator_support Q split (pinnedInput Q split c) _ hk
  obtain ⟨p,rfl⟩ := (synchronizedPositiveChart Q split c (.inl 2)).surjective p
  obtain ⟨⟨v,l⟩,rfl⟩ := (synchronizedPositiveChart Q split c (.inr 1)).surjective v
  obtain ⟨w,rfl⟩ := (synchronizedPositiveChart Q split c (.inl 3)).surjective w
  obtain ⟨⟨t,r⟩,rfl⟩ := (synchronizedPositiveChart Q split c (.inr 3)).surjective t
  obtain ⟨s,rfl⟩ := (synchronizedPositiveChart Q split c (.inl 1)).surjective s
  refine ⟨p,v,l,w,t,r,s,?_⟩
  simpa only [synchronizedPositivePoint,V2InteriorFactors,rootProduct,mul_one,mul_assoc] using hk.symm


/-- The two exterior coordinates of the Suzuki--Suzuki commutator are
forced by its five-root support.  This is the coefficient extraction used in
(10.23)--(10.26); the two remaining coordinates are left for the angular
coefficient equations. -/
theorem synchronizedSuzukiMixed_outer_coefficients
    (a b y z : CoefficientField m) :
    ∃ p v l w t r s : CoefficientField m,
      (synchronizedSuzukiMixed Q split c a b y z : X ⧸ Q.D) =
        synchronizedPositivePoint Q split c (.inl 2) p *
        synchronizedPositivePoint Q split c (.inr 1) (v,l) *
        synchronizedPositivePoint Q split c (.inl 3) w *
        synchronizedPositivePoint Q split c (.inr 3) (t,r) *
        synchronizedPositivePoint Q split c (.inl 1) s ∧
      s = b*y ∧ t = titsEnd m a*y := by
  obtain ⟨p,v,l,w,t,r,s,hprod⟩ :=
    synchronizedSuzukiMixed_support Q split c a b y z
  refine ⟨p,v,l,w,t,r,s,hprod,?_,?_⟩
  · have hc := V2_interior_coordinates Q split c
      (synchronizedPositiveChart Q split c (.inl 2) p)
      (synchronizedPositiveChart Q split c (.inr 1) (v,l))
      (synchronizedPositiveChart Q split c (.inl 3) w) t r
      (synchronizedPositiveChart Q split c (.inl 1) s)
      (synchronizedSuzukiMixed Q split c a b y z)
      (by simpa only [synchronizedPositivePoint,synchronizedPositiveChart,positivePoint] using hprod)
    rw [synchronizedSuzukiMixed_coordinates Q split c a b y z] at hc
    rw [synchronized_reflected_coordinate Q split c s,
      V2MiddleFieldLabel_scalar Q split c] at hc
    have hs : s * pinnedLinearV2Label Q split c 1 =
        (b*y) * pinnedLinearV2Label Q split c 1 := by
      simpa only [Matrix.cons_val,Fin.isValue,Matrix.head_cons] using (congrFun hc 0).symm
    exact mul_right_cancel₀ (pinnedLinearV2Label_one_ne_zero Q split c) hs
  · have hc := V2_interior_coordinates Q split c
      (synchronizedPositiveChart Q split c (.inl 2) p)
      (synchronizedPositiveChart Q split c (.inr 1) (v,l))
      (synchronizedPositiveChart Q split c (.inl 3) w) t r
      (synchronizedPositiveChart Q split c (.inl 1) s)
      (synchronizedSuzukiMixed Q split c a b y z)
      (by simpa only [synchronizedPositivePoint,synchronizedPositiveChart,positivePoint] using hprod)
    rw [synchronizedSuzukiMixed_coordinates Q split c a b y z] at hc
    rw [synchronized_reflected_coordinate Q split c s,
      V2MiddleFieldLabel_scalar Q split c] at hc
    have ht : t * pinnedLinearV2Label Q split c 1 =
        (titsEnd m a*y) * pinnedLinearV2Label Q split c 1 := by
      simpa only [Matrix.cons_val,Fin.isValue,Matrix.head_cons] using (congrFun hc 1).symm
    exact mul_right_cancel₀ (pinnedLinearV2Label_one_ne_zero Q split c) ht

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
