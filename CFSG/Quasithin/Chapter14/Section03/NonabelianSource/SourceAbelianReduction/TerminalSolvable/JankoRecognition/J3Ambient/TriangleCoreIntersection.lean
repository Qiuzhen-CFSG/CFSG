module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.OverlapPair
public import Theory.SpecificGroups.Janko3.SourceRecognition.BaumeisterParabolics.PointCentralizer
public import Theory.SpecificGroups.MinusExtraspecial.ElementaryBound
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The actual point-centralizer intersection with the involution core

The point centralizer is literally `A₄ × C₂`. Its intersection with the
full minus-extraspecial involution core is a normal elementary subgroup,
so has order at most four. A normal subgroup of this size containing the
central involution can only be that involution line. The full core is
transported from the original H-type centralizer by actual involution
fusion; no local complement or triangle model is assumed.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
open Theory.GroupTheory

private theorem normal_small_product {H : Type*} [Group H] [Finite H]
    (e : H ≃* (alternatingGroup (Fin 4) × Multiplicative (ZMod 2)))
    (I : Subgroup H) [I.Normal] (hI : Nat.card I ≤ 4)
    (z : H) (hzI : z ∈ I) (hz : orderOf z = 2) (hzc : z ∈ center H) :
    I = zpowers z := by
  let f : H →* alternatingGroup (Fin 4) :=
    (MonoidHom.fst _ _).comp e.toMonoidHom
  have hf : Function.Surjective f := Prod.fst_surjective.comp e.surjective
  have hzf : f z = 1 := by
    have hc : f z ∈ center (alternatingGroup (Fin 4)) := by
      apply mem_center_iff.mpr
      intro x
      obtain ⟨y, rfl⟩ := hf x
      simpa only [map_mul] using congrArg f (mem_center_iff.mp hzc y)
    rwa [alternatingGroup.center_eq_bot (by simp), mem_bot] at hc
  let J := I.map f
  let : J.Normal := Normal.map inferInstance f hf
  have hJcard : Nat.card J ≤ 4 :=
    (Nat.card_le_card_of_surjective (f.subgroupMap I) (f.subgroupMap_surjective I)).trans hI
  have hJ : J = ⊥ := by
    rcases AlternatingFourPair.normalA4 J with hh | hh | hh
    · exact hh
    · have hc : Nat.card J = 4 := by
        rw [hh]
        exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
      have hi : Function.Injective (f.subgroupMap I) :=
        ((f.subgroupMap_surjective I).bijective_of_nat_card_le (by rw [hc]; exact hI)).1
      have he : (f.subgroupMap I) (⟨z, hzI⟩ : I) = 1 := Subtype.ext hzf
      have hz1 : z = 1 := congrArg Subtype.val (hi (he.trans (map_one _).symm))
      rw [hz1, orderOf_one] at hz
      omega
    · have hc : Nat.card J = 12 := by
        rw [hh, Nat.card_congr (topEquiv (G := alternatingGroup (Fin 4))).toEquiv]
        exact alternatingGroup.card_of_card_eq_four (by simp)
      omega
  have hfst (x : I) : (e (x : H)).1 = 1 := by
    have hh : f (x : H) ∈ J := mem_map_of_mem f x.property
    rw [hJ, mem_bot] at hh
    exact hh
  let t : I → Multiplicative (ZMod 2) := fun x => (e (x : H)).2
  have ht : Function.Injective t := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact Prod.ext ((hfst x).trans (hfst y).symm) hxy
  have hIc : Nat.card I ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      using Nat.card_le_card_of_injective t ht
  apply (eq_of_le_of_card_ge (zpowers_le.mpr hzI) ?_).symm
  rw [Nat.card_zpowers, hz]
  exact hIc

private theorem core_equiv_at_involution {G : Type*} [Group G] [Finite G]
    {D : Seed G} (hc : Janko23.OneInvolutionClass G) (f : G) (hf : orderOf f = 2) :
    Nonempty (Janko23.ambientCore f ≃* MinusExtraspecial.Model) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hc.isConj D.localType.involution hf)
  let a := MulAut.conj g
  have haf : a f = D.z := hg
  let c : Janko23.involutionCentralizer f ≃* Janko23.involutionCentralizer D.z :=
    (CentralizerSmallKernelTransport.centralizerEquiv a f).trans
      (MulEquiv.subgroupCongr (by rw [haf]))
  have he : (Janko23.localCore f).map c.toMonoidHom = Janko23.localCore D.z :=
    map_generalizedFitting_equiv c
  let e0 : Janko23.localCore f ≃* Janko23.localCore D.z :=
    ((Janko23.localCore f).equivMapOfInjective c.toMonoidHom c.injective).trans
      (MulEquiv.subgroupCongr he)
  let e1 : Janko23.localCore f ≃* Janko23.ambientCore f :=
    (Janko23.localCore f).equivMapOfInjective _
      (Janko23.involutionCentralizer f).subtype_injective
  exact ⟨e1.symm.trans (e0.trans D.localType.core_equiv.some)⟩

variable {G : Type*} [Group G] [Finite G]

set_option maxHeartbeats 800000 in
/-- The actual point centralizer meets the full involution core in the literal involution line. -/
theorem literal_triangle_point_core_intersection
    {D : Seed G} (_P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    (j.range ⊓ centralizer ({j SingerField.fieldElement} : Set G)) ⊓
      Janko23.ambientCore (j SingerField.fieldElement) =
        zpowers (j SingerField.fieldElement) := by
  let f := j SingerField.fieldElement
  let H := Janko23.involutionCentralizer f
  let X := j.range ⊓ H
  let Q := Janko23.ambientCore f
  have hf : orderOf f = 2 := image_involution_order j hj.1
  obtain ⟨eQ⟩ := core_equiv_at_involution (D := D) hc f hf
  have hQc : Nat.card Q = 32 := (Nat.card_congr eQ.toEquiv).trans MinusExtraspecial.card_model
  let eX : X ≃* (alternatingGroup (Fin 4) × Multiplicative (ZMod 2)) :=
    PointCentralizer.imagePointCentralizerEquiv j hj.1
  let I := Q.subgroupOf X
  have hQH : Q ≤ H := Janko23.ambientCore_le f
  have hXH : X ≤ H := inf_le_right
  have hQN : (Q.subgroupOf H).Normal := by
    rw [Janko23.ambientCore_subgroupOf]
    infer_instance
  let : I.Normal := by
    change (Q.subgroupOf X).Normal
    exact normal_subgroupOf_of_le_normalizer
      (hXH.trans ((normal_subgroupOf_iff_le_normalizer hQH).mp hQN))
  have hpow (x : I) : x ^ 2 = 1 := by
    have hx32 : ((x : X) : G) ^ 32 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨x, x.property⟩ : Q))
      rw [hQc] at hh
      exact congrArg Subtype.val hh
    have hxX : (x : X) ^ 32 = 1 := Subtype.ext hx32
    have hm : (eX (x : X)) ^ 32 = 1 := by rw [← map_pow, hxX, map_one]
    have hmodel : ∀ y : alternatingGroup (Fin 4) × Multiplicative (ZMod 2),
        y ^ 32 = 1 → y ^ 2 = 1 := by decide +kernel
    apply Subtype.ext
    apply eX.injective
    change eX ((x : X) ^ 2) = eX 1
    rw [map_pow, map_one]
    exact hmodel _ hm
  let : IsElementaryAbelian 2 I := {
    toIsMulCommutative := ⟨⟨fun x y =>
      (Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hpow z)) x y).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  let IQ := X.subgroupOf Q
  let ei : I ≃* IQ := {
    toFun := fun x => ⟨⟨x, x.property⟩, x.val.property⟩
    invFun := fun x => ⟨⟨x, x.property⟩, x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hIQ : IsElementaryAbelian 2 IQ := IsElementaryAbelian.of_surjective ei.toMonoidHom ei.surjective
  have hIc : Nat.card I ≤ 4 := by
    rw [Nat.card_congr ei.toEquiv]
    exact MinusExtraspecial.elementary_subgroup_card_le_four eQ IQ hIQ
  have hfX : f ∈ X := ⟨⟨SingerField.fieldElement, rfl⟩, mem_centralizer_singleton_iff.mpr rfl⟩
  let fX : X := ⟨f, hfX⟩
  have hfI : fX ∈ I := Janko23.HTypeAt.involution_mem_core
  have hfXo : orderOf fX = 2 := (orderOf_coe fX).symm.trans hf
  have hfXc : fX ∈ center X := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2)
  have hIeq := normal_small_product eX I hIc fX hfI hfXo hfXc
  have hm := congrArg (Subgroup.map X.subtype) hIeq
  rw [subgroupOf_map_subtype, MonoidHom.map_zpowers] at hm
  change X ⊓ Q = zpowers f
  exact (inf_comm X Q).trans hm

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
