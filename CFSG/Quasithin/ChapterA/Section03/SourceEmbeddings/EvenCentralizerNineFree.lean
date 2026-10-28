module

public import CFSG.Quasithin.Chapter1.Section01.ModelActions115
public import Theory.SpecificGroups.PSL2.NineFreeInnerCentralizer
public import Theory.SpecificGroups.PSL3Four.NineFreeInnerCentralizer
public import Theory.SpecificGroups.SymplecticFour.NineFreeInnerCentralizer
public import Theory.SpecificGroups.Alternating.EightNineFreeInnerCentralizer
public import Theory.SpecificGroups.SU3.FourNineFreeAutomorphisms
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# The even-model centralizer calculation in 14.3.20

Fixing a Sylow two-subgroup forces the whole two-part into the marked
centralizer. Its order dividing 2304 therefore excludes 512 from the group
order. Concrete unipotent subgroups restrict the family parameters; the
remaining cases use the full automorphism centralizers, transported along
actual model isomorphisms. All small derived rows are included.

Source: Aschbacher--Smith 14.3.20, printed p.998, and the characteristic-two
alternatives in 1.1.5(3)(a--b), printed pp.501--503. This is the intrinsic
numerical calculation; the ambient faithful action is a separate input.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCentralizerNineFree
open ClassificationModels Chapter1.Section02.LocalModels
open Theory.GroupTheory.CentralizerSmallKernelTransport
open scoped MatrixGroups
variable {X : Type*} [Group X] [Finite X]

private theorem power_dvd {a b : ℕ} (h : 9 ≤ a * b) : 512 ∣ (2 ^ a) ^ b := by
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 h

omit [Group X] [Finite X] in
private theorem parameter_le_two {f : ℕ} (h : ¬ 512 ∣ Nat.card X)
    (hd : (2 ^ f) ^ 3 ∣ Nat.card X) : f ≤ 2 := by
  by_contra hn
  exact h ((power_dvd (by omega)).trans hd)

omit [Finite X] in
private theorem centralizer_card_congr {Y : Type*} [Group Y] (e : X ≃* Y) (x : X) :
    Nat.card (centralizer ({x} : Set X)) = Nat.card (centralizer ({e x} : Set Y)) :=
  Nat.card_congr (centralizerEquiv e x).toEquiv

omit [Finite X] in
private theorem rankOne (hm : IsBenderModel X) (hsmall : ¬ 512 ∣ Nat.card X)
    (h480 : 480 ∣ Nat.card X) (x : X) (hx : orderOf x = 2)
    (hc : Nat.card (centralizer ({x} : Set X)) ∣ 2304) :
    ¬ 9 ∣ Nat.card (centralizer ({MulAut.conj x} : Set (MulAut X))) := by
  classical
  cases hm with
  | linear f hf iso =>
    obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := iso
    let := hFfield
    let := hFfinite
    let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    rw [MulAut.card_centralizer_conj_congr e x]
    exact Theory.PSL2.binary_not_nine_dvd_inner_involution_centralizer hF (e x)
      ((e.orderOf_eq x).trans hx) ((centralizer_card_congr e x) ▸ hc)
  | unitary f hf iso =>
    obtain ⟨F, hFfield, hFfinite, J, hF, hconj, ⟨e⟩⟩ := iso
    let := hFfield
    let := hFfinite
    have hd := BenderSuzuki.MatrixGroups.HermitianForm.BinarySylowOrder.cube_dvd_card_projective
      J (by omega : f ≠ 0) hF hconj
    rw [← Nat.card_congr e.toEquiv] at hd
    have hf2 : f = 2 := by have := parameter_le_two hsmall hd; omega
    subst f
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hF hconj
    have hb := BenderSuzuki.MatrixGroups.HermitianForm.four_not_nine_dvd_card_aut J
      (by simpa using hF) (by simpa using hfixed)
    rw [MulAut.card_centralizer_conj_congr e x]
    exact fun h => hb (h.trans (card_subgroup_dvd_card _))
  | suzuki m hm iso =>
    obtain ⟨e⟩ := iso
    have hd : 3 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
      (by decide : 3 ∣ 480).trans ((Nat.card_congr e.toEquiv) ▸ h480)
    exact False.elim (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hd)

omit [Finite X] in
private theorem rankTwo (hm : RankTwoTheoremC X) (hsmall : ¬ 512 ∣ Nat.card X)
    (h480 : 480 ∣ Nat.card X) (x : X) (hx : orderOf x = 2)
    (hc : Nat.card (centralizer ({x} : Set X)) ∣ 2304) :
    ¬ 9 ∣ Nat.card (centralizer ({MulAut.conj x} : Set (MulAut X))) := by
  classical
  cases hm with
  | linear f hf iso =>
    obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := iso
    let := hFfield
    let := hFfinite
    have hd := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_unipotent, hF, ← Nat.card_congr e.toEquiv] at hd
    have hf2 := parameter_le_two hsmall hd
    have hf' : f = 1 ∨ f = 2 := by omega
    rcases hf' with rfl | rfl
    · have ho : Nat.card X = 168 := by
        rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective, hF]
        norm_num
      rw [ho] at h480
      norm_num at h480
    · let := Fintype.ofFinite F
      let := Fintype.ofFinite Matrix.PSL3Four.F
      let a : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card, Matrix.PSL3Four.card_F, Nat.reducePow] using hF)
      let b := e.trans (Atlas.fieldEquivPSL 3 a)
      rw [MulAut.card_centralizer_conj_congr b x]
      exact Matrix.PSL3Four.not_nine_dvd_inner_involution_centralizer (b x)
        ((b.orderOf_eq x).trans hx)
  | symplectic f hf iso =>
    obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := iso
    let := hFfield
    let := hFfinite
    let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let b := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)).card_subgroup_dvd_card
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent, hF,
      ← Nat.card_congr b.toEquiv] at hd
    have hf2 : f = 2 := by
      by_contra hn
      exact hsmall ((power_dvd (by omega)).trans hd)
    subst f
    rw [MulAut.card_centralizer_conj_congr b x]
    exact Theory.SpecificGroups.SymplecticFour.not_nine_dvd_inner_involution_centralizer
      (by simpa using hF) (b x) ((b.orderOf_eq x).trans hx)
      ((centralizer_card_congr b x) ▸ hc)
  | g2 f hf iso =>
    obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := iso
    let := hFfield
    let := hFfinite
    have hd : (2 ^ f) ^ 6 ∣ Nat.card X := by
      rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hF]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    exact False.elim (hsmall ((power_dvd (by omega)).trans hd))
  | triality f hf iso =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff X f (by omega)).mp iso
    have hd := (Triality.Standard.Parabolics.unipotent
      (Triality.Standard.binaryParameters f (by omega))).card_subgroup_dvd_card
    rw [Triality.Standard.Parabolics.card_unipotent_binary _ rfl] at hd
    change (2 ^ f) ^ 12 ∣ Nat.card (Triality.Standard.BinaryCarrier f _) at hd
    rw [← Nat.card_congr e.toEquiv] at hd
    exact False.elim (hsmall ((power_dvd (by omega)).trans hd))
  | ree m hm iso =>
    obtain ⟨d, ⟨e⟩⟩ := iso
    let b := e.trans d.modelEquiv
    have hd := (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
    rw [ReeF4.Parabolics.card_unipotent, ← Nat.card_congr b.toEquiv] at hd
    exact False.elim (hsmall ((power_dvd (by omega)).trans hd))
  | symplectic_derived iso =>
    obtain ⟨e⟩ := iso
    let b := e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
    have ho : Nat.card X = 360 := by
      rw [Nat.card_congr b.toEquiv, nat_card_alternatingGroup]
      norm_num
    rw [ho] at h480
    norm_num at h480
  | g2_derived iso =>
    obtain ⟨e⟩ := iso
    have ho : Nat.card X = 6048 := by
      rw [Nat.card_congr e.toEquiv]
      exact Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)
    rw [ho] at h480
    norm_num at h480
  | tits iso =>
    obtain ⟨e⟩ := iso
    have ho : Nat.card X = 17971200 :=
      (Nat.card_congr e.toEquiv).trans Tits.parrottGroup_card
    exact False.elim (hsmall (ho ▸ (by decide : 512 ∣ 17971200)))

omit [Finite X] in
private theorem binaryLinear {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL X n 2) (hsmall : ¬ 512 ∣ Nat.card X)
    (x : X) (hx : orderOf x = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({MulAut.conj x} : Set (MulAut X))) := by
  classical
  obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := hm
  let := hFfield
  let := hFfinite
  rcases hn with rfl | rfl
  · let := Fintype.ofFinite F
    let a : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
    let b := (e.trans (Atlas.fieldEquivPSL 4 a)).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
    rw [MulAut.card_centralizer_conj_congr b x]
    exact alternatingGroup.eight_not_nine_dvd_inner_involution_centralizer (b x)
      ((b.orderOf_eq x).trans hx)
  · have ho := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [hF] at ho
    norm_num [Fin.prod_univ_succ] at ho
    have hh : Nat.card X = 9999360 := (Nat.card_congr e.toEquiv).trans ho
    exact False.elim (hsmall (hh ▸ (by decide : 512 ∣ 9999360)))

/-- Every characteristic-two family and every small derived row satisfies the
intrinsic numerical centralizer bound. No ambient-action hypothesis is used. -/
theorem not_nine_dvd (hm : LieTypeTwoModel X) (x : X) (hx : orderOf x = 2)
    (hS : ∃ S : Sylow 2 X, ∀ y : S, MulAut.conj x y = y)
    (h480 : 480 ∣ Nat.card X) (hc : Nat.card (centralizer ({x} : Set X)) ∣ 2304) :
    ¬ 9 ∣ Nat.card (centralizer ({MulAut.conj x} : Set (MulAut X))) := by
  have hsmall : ¬ 512 ∣ Nat.card X := by
    intro hd
    obtain ⟨S, hS⟩ := hS
    exact (by decide : ¬ 512 ∣ 2304)
      ((pow_dvd_card_centralizer_of_fixes_sylow (n := 9) x S hS hd).trans hc)
  rcases hm with hm | hm | ⟨n, hn, hm⟩
  · exact rankOne hm hsmall h480 x hx hc
  · exact rankTwo hm hsmall h480 x hx hc
  · exact binaryLinear hn hm hsmall x hx

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCentralizerNineFree
