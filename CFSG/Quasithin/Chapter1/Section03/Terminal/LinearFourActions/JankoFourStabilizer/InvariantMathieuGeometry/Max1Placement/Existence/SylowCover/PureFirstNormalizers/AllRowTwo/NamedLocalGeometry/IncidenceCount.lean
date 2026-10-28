module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.CanonicalF
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Counting all native F occurrences through a first-class point

The actual exterior marking identifies the first-class points of F with its
155-element decomposable orbit. The full native normalizer has order
10239344640. Count the ambient transporters of a point into F both by that
point orbit and by the conjugates of F that contain it. The certified first
centralizer order then gives exactly 330 such actual ambient conjugates.
The final application uses the literal marked point of the finite-row data.

This proves the ambient occurrence count needed for the proposed finite
incidence argument. It does not yet identify these occurrences with a word
table or assert uniqueness over a sixteen row. The proof uses public
orbit--stabilizer equivalences and the existing native exterior action;
there is no new matrix computation or normalizer-cover premise.
Source context: Kleidman--Wilson (1988), Section 2.1, pp.488--489, and the
native F normalizer identification cited in `LinearFive.Normalizer`.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
open LinearFive LinearFive.NativeNormalizer
open Representation Representation.SL5ExteriorSquare Representation.SL5TenDimensional
open Representation.SL5ExteriorSquare.TwoGeneratorRecognition
attribute [local irreducible] modelGroup matrixA matrixB

private theorem native_orbit_isConj (x y : LinearFive.F)
    (h : InExteriorOrbit (exteriorMarking x).toAdd (exteriorMarking y).toAdd) :
    IsConj (x : Model) (y : Model) := by
  obtain ⟨g,hg⟩ := h
  obtain ⟨n,hn⟩ := LinearFive.normalizerProjection_surjective g
  have hm := LinearFive.normalizerProjection_exterior n x
  rw [hn,hg] at hm
  have hy : LinearFive.F.normalizerMonoidHom n x = y :=
    exteriorMarking.injective (congrArg Multiplicative.ofAdd hm)
  exact isConj_iff.mpr ⟨n,(Subgroup.normalizerMonoidHom_apply_apply_coe LinearFive.F n x).symm.trans
    (congrArg Subtype.val hy)⟩

/-- Ambient first-class fusion is exactly the decomposable exterior orbit. -/
theorem first_iff_decomposable (x : LinearFive.F) :
    IsConj a (x : Model) ↔ InExteriorOrbit decomposable (exteriorMarking x).toAdd := by
  constructor
  · intro h
    have hx0 : (exteriorMarking x).toAdd ≠ 0 := by
      intro he
      have hx1 : x = 1 := exteriorMarking.injective
        ((congrArg Multiplicative.ofAdd he).trans exteriorMarking.map_one.symm)
      have ha : a = 1 := isConj_one_left.mp (by simpa only [hx1,Subgroup.coe_one] using h)
      have ho := orderOf_a
      simp [ha] at ho
    rcases exterior_orbits_exhaustive (exteriorMarking x).toAdd hx0 with hd | hu
    · exact hd
    · have huX := native_orbit_isConj nondecomposableRep x
        (by rw [nondecomposableRep_marking]; exact hu)
      exact (representatives_not_isConj (decomposableRep_first.trans (h.trans huX.symm))).elim
  · intro h
    exact decomposableRep_first.symm.trans (native_orbit_isConj decomposableRep x
      (by rw [decomposableRep_marking]; exact h))

/-- Count the actual first-class elements of the literal native F. -/
theorem first_points_in_F_card : Nat.card {x : LinearFive.F // IsConj a (x : Model)} = 155 := by
  let e : LinearFive.F ≃ V := {
    toFun := fun x => (exteriorMarking x).toAdd
    invFun := fun v => exteriorMarking.symm (Multiplicative.ofAdd v)
    left_inv := exteriorMarking.symm_apply_apply
    right_inv := fun v => congrArg Multiplicative.toAdd (exteriorMarking.apply_symm_apply (Multiplicative.ofAdd v)) }
  rw [Nat.card_congr (e.subtypeEquiv (fun x => first_iff_decomposable x))]
  exact card_decomposable_orbit

/-- Count the full normalizer using its literal F kernel and SL₅(2) quotient. -/
theorem native_F_normalizer_card : Nat.card LinearFive.fullNormalizer = 10239344640 := by
  have hk : Nat.card LinearFive.normalizerKernel = 1024 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe LinearFive.F.le_normalizer).toEquiv]
    exact LinearFive.F_card
  rw [card_eq_card_quotient_mul_card_subgroup LinearFive.normalizerKernel,
    Nat.card_congr LinearFive.normalizerQuotient.toEquiv,hk,card_specialLinearFive]

section
variable {G X : Type*} [_root_.Group G] [MulAction G X]
open MulAction
private theorem incidencePreimage_card (a : X) (P : X → Prop) :
    Nat.card {g : G // P (g • a)} =
      Nat.card {b : orbit G a // P b.val} * Nat.card (stabilizer G a) := by
  let e := (orbitProdStabilizerEquivGroup G a).symm
  have he (g : G) : (e g).1.val = g • a := rfl
  let e' : {g : G // P (g • a)} ≃ {b : orbit G a × stabilizer G a // P b.1.val} :=
    e.subtypeEquiv (fun g => by rw [he])
  rw [Nat.card_congr (e'.trans (Equiv.prodSubtypeFstEquivSubtypeProd
    (p := fun b : orbit G a => P b.val) (β := stabilizer G a))),Nat.card_prod]

end


open scoped Pointwise
private local instance subgroupConjugation : MulAction Model (Subgroup Model) :=
  MulAction.compHom (Subgroup Model) ConjAct.toConjAct.toMonoidHom

private theorem occurrence_count_product (t : Model) :
    Nat.card (fOccurrences (zpowers t)) * Nat.card LinearFive.fullNormalizer =
      Nat.card (centralizer ({t} : Set Model)) * Nat.card {x : LinearFive.F // IsConj t (x : Model)} := by
  have h1 := incidencePreimage_card (G := Model) LinearFive.F (fun Y => t ∈ Y)
  have h2 := incidencePreimage_card (G := ConjAct Model) t (fun x => x ∈ LinearFive.F)
  have hs : MulAction.stabilizer Model LinearFive.F = LinearFive.fullNormalizer := by
    ext g
    exact conjAct_pointwise_smul_iff
  have hc : Nat.card (MulAction.stabilizer (ConjAct Model) t) =
      Nat.card (centralizer ({t} : Set Model)) := by
    apply Nat.card_congr
    exact ((ConjAct.toConjAct (G := Model)).toEquiv.subtypeEquiv (fun g => by
      rw [mem_centralizer_singleton_iff, MulAction.mem_stabilizer_iff, ConjAct.smul_def,
        mul_inv_eq_iff_eq_mul]
      rfl)).symm
  have hf : Nat.card {Y : MulAction.orbit Model LinearFive.F // t ∈ Y.val} =
      Nat.card (fOccurrences (zpowers t)) := by
    apply Nat.card_congr
    refine {
      toFun := fun Y => ⟨Y.val.val, ?_⟩
      invFun := fun Y => ⟨⟨Y.val, ?_⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    · obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp Y.val.property
      exact ⟨g,hg.symm,zpowers_le.mpr Y.property⟩
    · obtain ⟨g,hg,_⟩ := Y.property
      exact MulAction.mem_orbit_iff.mpr ⟨g,hg.symm⟩
    · obtain ⟨_,_,h⟩ := Y.property
      exact h (mem_zpowers t)
  have hp : Nat.card {x : MulAction.orbit (ConjAct Model) t // x.val ∈ LinearFive.F} =
      Nat.card {x : LinearFive.F // IsConj t (x : Model)} := by
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨⟨x.val.val,x.property⟩,(ConjAct.mem_orbit_conjAct.mp x.val.property).symm⟩
      invFun := fun x => ⟨⟨x.val.val,ConjAct.mem_orbit_conjAct.mpr x.property.symm⟩,x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have ht : Nat.card {g : Model // t ∈ g • LinearFive.F} =
      Nat.card {g : ConjAct Model // g • t ∈ LinearFive.F} := by
    apply Nat.card_congr
    let e : Model ≃ ConjAct Model := (Equiv.inv Model).trans ConjAct.toConjAct.toEquiv
    apply e.subtypeEquiv
    intro g
    change t ∈ LinearFive.F.map (MulAut.conj g).toMonoidHom ↔ g⁻¹*t*(g⁻¹)⁻¹ ∈ LinearFive.F
    rw [inv_inv]
    constructor
    · rintro ⟨y,hy,he⟩
      change g*y*g⁻¹ = t at he
      rw [← he]
      rw [show g⁻¹ * (g*y*g⁻¹) * g = y by group]
      exact hy
    · intro h
      refine ⟨g⁻¹*t*g,h,?_⟩
      change g*(g⁻¹*t*g)*g⁻¹ = t
      group
  rw [hs,hf] at h1
  rw [hp,hc] at h2
  exact h1.symm.trans (ht.trans (h2.trans (mul_comm _ _)))

/-- Every first-class point lies in exactly 330 actual ambient F occurrences. -/
theorem first_point_F_occurrences_card (t : Model) (ht : IsConj a t) :
    Nat.card (fOccurrences (zpowers t)) = 330 := by
  have h := occurrence_count_product t
  have hc : Nat.card (centralizer ({a} : Set Model)) = 21799895040 := by
    simpa only [Cardinality.LocalInvolutionCensus.z_eq_a] using Cardinality.Thompson.centralizer_z_card
  have hct : Nat.card (centralizer ({t} : Set Model)) = 21799895040 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp ht
    let e := MulAut.conj g
    have he : e a = t := hg
    let ec : centralizer ({a} : Set Model) ≃ centralizer ({t} : Set Model) :=
      e.toEquiv.subtypeEquiv (fun x => by
        simp only [mem_centralizer_singleton_iff,← he]
        change x*a = a*x ↔ e x * e a = e a * e x
        rw [← map_mul,← map_mul,e.injective.eq_iff])
    exact (Nat.card_congr ec.symm).trans hc
  have hpt : Nat.card {x : LinearFive.F // IsConj t (x : Model)} = 155 := by
    let ep : {x : LinearFive.F // IsConj t (x : Model)} ≃ {x : LinearFive.F // IsConj a (x : Model)} :=
      Equiv.subtypeEquivRight (fun x => ⟨ht.trans,ht.symm.trans⟩)
    exact (Nat.card_congr ep).trans first_points_in_F_card
  rw [native_F_normalizer_card,hpt,hct] at h
  omega

open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- The ambient count at the actual marked point used by all shared rows. -/
theorem marked_point_F_occurrences_card :
    Nat.card (fOccurrences (zpowers FiniteConfigurations.markedT)) = 330 := by
  apply first_point_F_occurrences_card
  change IsConj a t
  exact (isConj_iff.mpr ⟨h⁻¹,by simpa only [inv_inv] using conjugates_t⟩).symm

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
