module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.EnlargedSwapping
public import Theory.GroupTheory.NormalizerAction.CommutingCoordinates
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Enlarged

/-!
# Literal six-dimensional coordinates in the remaining swapping case

The elementary product B=A C_G(L) is identified with the binary four-space
and a binary plane. Multiplication retains both ambient factors. Every actor
in the marked parabolic centralizes the second factor, so its image is the
specified parabolic extended by the identity. The corrected cubic rotates
the same common four-group and moves both coordinate factors.

The faithful image of N_G(B)/C_G(B) retains the marked source point. Its
point stabilizer has order dividing |H|=4608, so every point-fixing element
has order dividing 4608. The original local-data and configuration consumers
therefore reduce to the displayed finite action, without an extra ambient
or coordinate premise. Excluding this finite action remains with
qt-d-14414-g2-source, as does local-data assembly; universal I.4.5 remains
with qt-i45-g2-recognition. EarlierSetupResults retains its existing earlier
producers and qt-d-14414-source retains final 14.4.14 assembly.

Source: Aschbacher–Smith, proof of 14.4.4–5, printed pp.1007–1008.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour.SplitImage
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G]

/-- The faithful normalizer quotient action in the six-dimensional coordinates. -/
def sixAction (B : Subgroup G) (e : B ≃* BinarySixSplitPair.E) :
    NormalizerAction.Star B →* MulAut BinarySixSplitPair.E :=
  (MulAut.congr e).toMonoidHom.comp (NormalizerAction.action B)

theorem sixAction_injective (B : Subgroup G) (e : B ≃* BinarySixSplitPair.E) :
    Function.Injective (sixAction B e) :=
  (MulAut.congr e).injective.comp (NormalizerAction.action_injective B)

/-- Extend the literal actor image by the identity on the actual central factor. -/
theorem product_actorImage {A D K : Subgroup G}
    {a : A ≃* BinaryFourSplitPair.E} {d : D ≃* BinarySixSplitPair.E₂}
    (e : NormalizerAction.ProductCoordinates A D a d)
    (hKA : K ≤ normalizer (A : Set G)) (hKD : K ≤ centralizer (D : Set G)) :
    (quotientImage (A ⊔ D) K).map (sixAction (A ⊔ D) e.equiv) =
      (actorImage A K a).map BinarySixSplitPair.extend := by
  have hKB : K ≤ normalizer ((A ⊔ D : Subgroup G) : Set G) :=
    (le_inf hKA (hKD.trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup A D)
  have hact (n : G) (hnK : n ∈ K)
      (hnA : n ∈ normalizer (A : Set G))
      (hnB : n ∈ normalizer ((A ⊔ D : Subgroup G) : Set G)) :
      sixAction (A ⊔ D) e.equiv (NormalizerAction.quotient (A ⊔ D) ⟨n,hnB⟩) =
        BinarySixSplitPair.extend (coordinateAction A a (NormalizerAction.quotient A ⟨n,hnA⟩)) := by
    simp only [sixAction,coordinateAction,MonoidHom.comp_apply,
      NormalizerAction.action_quotient]
    exact e.action_eq n hnA (hKD hnK) hnB
  ext x
  constructor
  · rintro ⟨q,⟨n,hnK,rfl⟩,rfl⟩
    let nA : normalizer (A : Set G) := ⟨n,hKA hnK⟩
    refine ⟨coordinateAction A a (NormalizerAction.quotient A nA),⟨nA,hnK,rfl⟩,?_⟩
    exact (hact n hnK nA.property n.property).symm
  · rintro ⟨q,⟨n,hnK,rfl⟩,rfl⟩
    let nB : normalizer ((A ⊔ D : Subgroup G) : Set G) := ⟨n,hKB hnK⟩
    refine ⟨NormalizerAction.quotient (A ⊔ D) nB,⟨nB,hnK,rfl⟩,?_⟩
    exact hact n hnK n.property nB.property

/-- A fully concrete remaining action. The group J is an actual faithful
normalizer image; its point stabilizer retains the source centralizer bound. -/
def SixDimensionalSwappingCase : Prop :=
  ∃ (J : Subgroup (MulAut BinarySixSplitPair.E)) (q : MulAut BinarySixSplitPair.E),
    BinarySixSplitPair.parabolic ≤ J ∧ q ∈ J ∧ BinarySixSplitPair.RotatingCubic q ∧
    ∀ w ∈ J, w BinarySixSplitPair.point = BinarySixSplitPair.point → orderOf w ∣ 4608

variable [Finite G]

/-- Actual enlarged swapping geometry supplies one common set of six-dimensional
coordinates, including the escaping cubic and the full point-stabilizer bound. -/
theorem sixDimensionalSwappingCase_of_enlarged
    {T : Sylow 2 G} {L V : Subgroup G} (F : InvariantFlag T V 3)
    (hcase : EnlargedSwappingCase L F) : SixDimensionalSwappingCase := by
  obtain ⟨s,hBe,hBcard,hDcard,hdis,hinf,hTN,hcommon,hfour,hHcard,
    P,z,hPL,hpoint,⟨p⟩,hactorN,hactorC,c,hcB,hc3,hcQ,hcs,hcA,hcD,hcn,hcc⟩ := hcase
  let A := zpowers (s:G) ⊔ ⁅F.U,zpowers (s:G)⁆
  let D := centralizer (L : Set G)
  let B := A ⊔ D
  let : IsElementaryAbelian 2 B := hBe
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (show D ≤ B from le_sup_right)
  obtain ⟨eD⟩ := BinarySixSplitPair.coordinates_four D hDcard
  have hAD : A ≤ centralizer (D : Set G) := by
    have hAL : A ≤ L := hinf.ge.trans inf_le_right
    exact hAL.trans (le_centralizer_iff.mp le_rfl)
  obtain ⟨e⟩ := NormalizerAction.productCoordinates_nonempty A D p.coordinates eD hdis hAD
  let f := sixAction B e.equiv
  have hf : Function.Injective f := sixAction_injective B e.equiv
  let n : normalizer (B : Set G) := ⟨c,hcB⟩
  let cstar := NormalizerAction.quotient B n
  let q := f cstar
  let zB : B := inclusion le_sup_left z
  have hz : e.equiv zB = BinarySixSplitPair.point := by
    rw [e.apply_left,p.point_eq]
    rfl
  have heval (x : NormalizerAction.Star B) (v : B) :
      f x (e.equiv v) = e.equiv (NormalizerAction.action B x v) := by
    change e.equiv (NormalizerAction.action B x (e.equiv.symm (e.equiv v))) = _
    rw [e.equiv.symm_apply_apply]
  have hpar : (quotientImage B (P ⊔ ((T:Subgroup G) ⊓ L))).map f =
      BinarySixSplitPair.parabolic := by
    rw [product_actorImage e p.normalizes hactorC,p.parabolic_image]
    rfl
  have hover : (quotientImage B ((T:Subgroup G) ⊓ L)).map f =
      BinarySixSplitPair.overlap := by
    rw [product_actorImage e (le_sup_right.trans p.normalizes)
      (le_sup_right.trans hactorC),p.sylow_image]
    rfl
  have hcentralizer : F.H = centralizer ({(zB:G)} : Set G) := by
    exact F.H_eq_centralizer (by decide) (z:G) hpoint
  have hqfix : q BinarySixSplitPair.point = BinarySixSplitPair.point := by
    rw [←hz,heval]
    apply congrArg e.equiv
    apply (NormalizerAction.quotient_mem_pointStabilizer B zB n).mpr
    exact hcentralizer ▸ c.property
  have hq3 : q^3=1 := by
    change (f (NormalizerAction.quotient B n))^3=1
    rw [←map_pow,←map_pow,show n^3=1 from Subtype.ext (congrArg (fun x:F.H => (x:G)) hc3),map_one,map_one]
  have hqn : q ∈ normalizer (BinarySixSplitPair.overlap : Set (MulAut BinarySixSplitPair.E)) := by
    rw [←hover]
    exact (quotientImage B ((T:Subgroup G) ⊓ L)).le_normalizer_map f ⟨cstar,hcn,rfl⟩
  have hqc : q ∉ centralizer (BinarySixSplitPair.overlap : Set (MulAut BinarySixSplitPair.E)) := by
    intro hc
    apply hcc
    intro x hx
    apply hf
    simpa only [map_mul] using hc (f x) (hover ▸ (mem_map.mpr ⟨x,hx,rfl⟩))
  have hqA : BinarySixSplitPair.leftFactor.map q.toMonoidHom ≠ BinarySixSplitPair.leftFactor := by
    intro hh
    apply hcA
    apply (e.left_map_eq_iff n).mp
    change BinarySixSplitPair.leftFactor.map
      (MulAut.congr e.equiv (B.normalizerMonoidHom n)).toMonoidHom = BinarySixSplitPair.leftFactor
    simpa only [q,f,sixAction,MonoidHom.comp_apply,cstar,NormalizerAction.action_quotient,MulEquiv.coe_toMonoidHom] using hh
  have hqD : BinarySixSplitPair.rightFactor.map q.toMonoidHom ≠ BinarySixSplitPair.rightFactor := by
    intro hh
    apply hcD
    apply (e.right_map_eq_iff n).mp
    change BinarySixSplitPair.rightFactor.map
      (MulAut.congr e.equiv (B.normalizerMonoidHom n)).toMonoidHom = BinarySixSplitPair.rightFactor
    simpa only [q,f,sixAction,MonoidHom.comp_apply,cstar,NormalizerAction.action_quotient,MulEquiv.coe_toMonoidHom] using hh
  refine ⟨f.range,q,?_,⟨cstar,rfl⟩,⟨hq3,hqfix,hqn,hqc,hqA,hqD⟩,?_⟩
  · rw [←hpar]
    exact map_le_range f _
  · rintro w ⟨x,rfl⟩ hw
    have hx : x ∈ NormalizerAction.pointStabilizer B zB := by
      apply e.equiv.injective
      change e.equiv (NormalizerAction.action B x zB) = e.equiv zB
      rw [←heval,hz]
      exact hw
    rw [orderOf_injective f hf]
    have hd := (NormalizerAction.pointStabilizer B zB).orderOf_dvd_natCard hx
    have hc := NormalizerAction.pointStabilizer_card_dvd B zB
    rw [←hcentralizer,hHcard] at hc
    exact hd.trans hc

variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The source local-data constructor has only the concrete finite-action
obstruction left; no ambient normalizer or coordinate callback is assumed. -/
theorem source_localData_or_six_dimensional_swapping
    (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (SourceLocalData L F) ∨ SixDimensionalSwappingCase := by
  rcases source_localData_or_enlarged_swapping d earlier hq chosen previous F hne hZ hcard with
    hd | hs
  · exact Or.inl hd
  · exact Or.inr (sixDimensionalSwappingCase_of_enlarged F hs)

/-- Literal application of the source reduction to the I.4.5 configuration. -/
theorem source_configuration_or_six_dimensional_swapping
    (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (DimensionFour.G2ThreeConfiguration G) ∨ SixDimensionalSwappingCase := by
  rcases source_localData_or_six_dimensional_swapping d earlier hq chosen previous F hne hZ hcard with
    hd | hs
  · obtain ⟨localData⟩ := hd
    exact Or.inl (configuration_of_source_local d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard localData)
  · exact Or.inr hs

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
