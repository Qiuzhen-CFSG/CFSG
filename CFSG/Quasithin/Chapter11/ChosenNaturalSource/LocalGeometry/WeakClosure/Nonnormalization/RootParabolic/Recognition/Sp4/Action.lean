module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.TransvectionFree.Action
public import Theory.SpecificGroups.SymplecticFour.RootDisplacement
public import Theory.SpecificGroups.SymplecticFour.ReciprocalSmallActors
public import Theory.Representation.SemilinearInvolutionFixedCard

/-!
# Recognizing small reciprocal symplectic actors

An elementary normalizer actor whose fixed index on the original module is
at most q has field-linear quotient action: a nontrivial field-twisted
involution would have q² displacements. A fixed field line then puts each
operator in the actual symplectic image. Uniqueness of the covering action
lifts this homomorphism to the entire original module, retaining its central
kernel. Its kernel is the literal ambient centralizer. If the reciprocal
actor corank is n, its image has order q and displacement dimension one,
so it is a conjugate of the whole transvection root.

The semilinear fixed-count calculation follows the checked three-space
argument in Closure/Amalgam/Even/Linear/Displacement.lean (also used in the
shadow reduction's reciprocal Sp4 calculation). Here the bound comes from
the original centralizer index, so no trivial or split central kernel is needed.
The actual conjugate-module consumer is in Recognition/Sp4.lean.

Source: Aschbacher--Smith, 11.2.4, printed p.769, using I.2.3(1b), p.413.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Subgroup Representation Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Recognition
open NormalizedPlane.TransvectionFree

private theorem linear_of_small_displacement
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (a : Vector F →+ Vector F) (ha : Function.Involutive a)
    (hsemi : ∃ σ : F ≃+* F, ∀ c v, a (c • v) = σ c • a v)
    (hcard : Nat.card (a - AddMonoidHom.id _).range ≤ Nat.card F) :
    ∀ (c : F) v, a (c • v) = c • a v := by
  obtain ⟨σ,hσ⟩ := hsemi
  have hs : σ = RingEquiv.refl F := by
    by_contra hn
    have hi : Function.Involutive σ := by
      intro c
      have h := ha (c • (Pi.single (Sum.inl 0) 1 : Vector F))
      rw [hσ,hσ,ha] at h
      simpa using congrFun h (Sum.inl 0)
    let δ := a - AddMonoidHom.id (Vector F)
    have hk : δ.ker = a.eqLocus (AddMonoidHom.id _) := by
      ext v
      exact sub_eq_zero
    have he := Representation.SemilinearInvolution.fixed_card_sq σ hi hn a ha hσ
    rw [← hk] at he
    have hc := δ.ker.card_mul_index
    rw [AddSubgroup.index_ker] at hc
    have hp : 0 < Nat.card δ.ker := Nat.card_pos
    have hr : Nat.card δ.range = Nat.card δ.ker := by nlinarith
    have hsquare : Nat.card δ.range ^ 2 = Nat.card F ^ 4 := by
      rw [hr,he,Nat.card_fun,Nat.card_sum,Nat.card_fin]
    have hF : 1 < Nat.card F := Finite.one_lt_card
    have hh : Nat.card δ.range ^ 2 ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hcard 2
    have hq : Nat.card F ^ 2 < Nat.card F ^ 4 := Nat.pow_lt_pow_right hF (by decide)
    omega
  simpa only [hs,RingEquiv.refl_apply] using hσ

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

private theorem displacement_card_le_index {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (a : A) :
    Nat.card (((quotientAction D S m (inclusion hA a)).toAddMonoidHom) -
      AddMonoidHom.id _).range ≤ (centralizer (A : Set G)).relIndex V := by
  let c := Coordinates.sp4 m
  let δ := (quotientAction D S m (inclusion hA a)).toAddMonoidHom -
    AddMonoidHom.id (Vector S.field.Carrier)
  let p : V →* Multiplicative δ.range :=
    δ.rangeRestrict.toMultiplicative.comp c.projection
  have hp : Function.Surjective p := δ.rangeRestrict_surjective.comp c.projection_surjective
  have hk : (centralizer (A : Set G)).subgroupOf V ≤ p.ker := by
    intro v hv
    have he : V.normalizerMonoidHom (inclusion hA a) v = v := by
      apply Subtype.ext
      change (a:G) * (v:G) * (a:G)⁻¹ = (v:G)
      have hc : (a:G) * (v:G) = (v:G) * (a:G) := hv a.val a.property
      rw [hc,mul_inv_cancel_right]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change quotientAction D S m (inclusion hA a) ((Coordinates.sp4 m).projection v).toAdd -
      (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection v).toAdd) = 0
    rw [quotientAction_projection,he,sub_self]
  have hi : p.ker.index = Nat.card δ.range := by
    rw [index_ker,p.range_eq_top_of_surjective hp]
    exact Nat.card_congr (topEquiv : (⊤ : Subgroup (Multiplicative δ.range)) ≃* _).toEquiv
  rw [←hi]
  change p.ker.index ≤ ((centralizer (A : Set G)).subgroupOf V).index
  have hh := relIndex_le_of_le_left (L := (⊤ : Subgroup V)) hk index_ne_zero_of_finite
  simpa only [relIndex_top_right] using hh

/-- A reciprocal index at most q excludes field twists in the original quotient. -/
theorem small_action_linear {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (a : A) (ha : a^2=1)
    (hindex : (centralizer (A : Set G)).relIndex V ≤ Nat.card S.field.Carrier) :
    ∀ (r : S.field.Carrier) v, quotientAction D S m (inclusion hA a) (r • v) =
      r • quotientAction D S m (inclusion hA a) v := by
  apply linear_of_small_displacement (quotientAction D S m (inclusion hA a)).toAddMonoidHom
  · intro v
    change quotientAction D S m (inclusion hA a)
      (quotientAction D S m (inclusion hA a) v) = v
    rw [←Module.End.mul_apply,←map_mul,←map_mul,←pow_two,ha,map_one,map_one]
    rfl
  · exact SymplecticNaturalNormalizer.exists_field_twist
      ⟨linearAction (quotientAction D S m) (inclusion hA a),
        quotientAction_mem_normalizer D S m _⟩
  · exact (displacement_card_le_index m hA a).trans hindex

/-- The small square-one normalizer operators lie in the actual symplectic image. -/
theorem small_action_inner {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (a : A) (ha : a^2=1)
    (hindex : (centralizer (A : Set G)).relIndex V ≤ Nat.card S.field.Carrier) :
    linearAction (quotientAction D S m) (inclusion hA a) ∈ naturalDerivedImage := by
  let ρ := quotientAction D S m
  have hinv (v) : ρ (inclusion hA a) (ρ (inclusion hA a) v) = v := by
    rw [←Module.End.mul_apply,←map_mul,←map_mul,←pow_two,ha,map_one,map_one]
    rfl
  have hfixed : ∃ v : Vector S.field.Carrier, v ≠ 0 ∧ ρ (inclusion hA a) v = v := by
    by_cases h : ∀ v, ρ (inclusion hA a) v = v
    · exact ⟨Pi.single (.inl 0) 1,by intro hz; simpa using congrFun hz (.inl 0),h _⟩
    · push Not at h
      obtain ⟨v,hv⟩ := h
      refine ⟨ρ (inclusion hA a) v - v,sub_ne_zero.mpr hv,?_⟩
      rw [map_sub,hinv]
      ext i
      simp only [Pi.sub_apply,CharTwo.sub_eq_add,add_comm]
  obtain ⟨v,hv,hfix⟩ := hfixed
  exact quotientAction_inner_of_line D S m (inclusion hA a)
    (by rw [←map_pow,ha,map_one]) v hv
    (fun r => (small_action_linear m hA a ha hindex r v).trans (congrArg (r • ·) hfix))


private theorem field_large : 2 < Nat.card S.field.Carrier := by
  rw [S.field.card_eq]
  simpa only [pow_one] using pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) S.nonbinary

/-- The literal small normalizer action, realized in Sp₄ over the original field. -/
def smallHom {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hindex : (centralizer (A : Set G)).relIndex V ≤ Nat.card S.field.Carrier) :
    A →* Sp S.field.Carrier :=
  (SymplecticNaturalNormalizer.naturalEquiv (field_large (S := S))).symm.toMonoidHom.comp
    (((linearAction (quotientAction D S m)).comp (inclusion hA)).codRestrict
      naturalDerivedImage (fun a => small_action_inner m hA a (hsq a) hindex))

theorem smallHom_quotient {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hindex : (centralizer (A : Set G)).relIndex V ≤ Nat.card S.field.Carrier) (a : A) :
    SymplecticNaturalNormalizer.naturalHom (smallHom m hA hsq hindex a) =
      linearAction (quotientAction D S m) (inclusion hA a) := by
  exact congrArg Subtype.val
    ((SymplecticNaturalNormalizer.naturalEquiv (field_large (S := S))).apply_symm_apply _)

/-- Agreement on the entire original module, including its nonsplit central kernel. -/
theorem smallHom_action {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hindex : (centralizer (A : Set G)).relIndex V ≤ Nat.card S.field.Carrier)
    (a : A) (v : D.space) :
    (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D m (smallHom m hA hsq hindex a) v)) : G) =
        (a : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (a : G)⁻¹ := by
  rw [←fullAction_eq_marked D S m (inclusion hA a) _
    (smallHom_quotient m hA hsq hindex a).symm]
  exact fullAction_conjugation D _ v

private theorem smallHom_ker {A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hindex : (centralizer (A : Set G)).relIndex V ≤ Nat.card S.field.Carrier) :
    (smallHom m hA hsq hindex).ker = (A ⊓ centralizer (V : Set G)).subgroupOf A := by
  ext a
  constructor
  · intro ha
    refine ⟨a.property,mem_centralizer_iff.mpr ?_⟩
    intro v hv
    obtain ⟨w,hw⟩ := D.spaceEquiv.surjective ⟨v,hv⟩
    have hh := smallHom_action m hA hsq hindex a w.toAdd
    rw [show smallHom m hA hsq hindex a = 1 from ha,map_one] at hh
    change (D.spaceEquiv w : G) = (a:G) * (D.spaceEquiv w : G) * (a:G)⁻¹ at hh
    rw [hw] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · rintro ⟨_,ha⟩
    change smallHom m hA hsq hindex a = 1
    apply SymplecticNaturalNormalizer.naturalHom_injective
    rw [smallHom_quotient,map_one]
    apply LinearEquiv.ext
    intro v
    let c := Coordinates.sp4 m
    obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
    have he : V.normalizerMonoidHom (inclusion hA a) w = w := by
      apply Subtype.ext
      change (a:G) * (w:G) * (a:G)⁻¹ = (w:G)
      have hc : (w : G) * (a : G) = (a : G) * (w : G) :=
        mem_centralizer_iff.mp ha w.val w.property
      rw [←hc,mul_inv_cancel_right]
    have hh := quotientAction_projection D S m (inclusion hA a) w
    rw [he,hw] at hh
    exact hh

/-- The image order is computed from the literal ambient action kernel. -/
theorem smallHom_card {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hindex : (centralizer (A : Set G)).relIndex V ≤ Nat.card S.field.Carrier) :
    Nat.card (smallHom m hA hsq hindex).range =
      2 ^ subgroupCorank A (A ⊓ centralizer (V : Set G)) := by
  rw [←index_ker,smallHom_ker]
  change (A ⊓ centralizer (V : Set G)).relIndex A = _
  rw [subgroupCorank_eq_quotient_finrank,relIndex_eq_two_pow_quotient_finrank]


/-- The reciprocal vector index bounds the field dimension of displacement. -/
theorem smallHom_displacement_dimension {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hindex : (centralizer (A : Set G)).relIndex V ≤ Nat.card S.field.Carrier)
    (hcorank : subgroupCorank A (A ⊓ centralizer (V : Set G)) = S.field.degree) :
    Module.finrank S.field.Carrier (displacementSpace (smallHom m hA hsq hindex).range) = 1 := by
  let α := smallHom m hA hsq hindex
  have hc : Nat.card α.range = Nat.card S.field.Carrier := by
    rw [smallHom_card,hcorank,S.field.card_eq]
  have hi := Theory.SpecificGroups.SymplecticFour.fixed_quotient_card_le_centralizer_index
    V A hA (Coordinates.sp4 m).projection (Coordinates.sp4 m).projection_surjective α (by
      intro a v
      apply Multiplicative.toAdd.injective
      exact (quotientAction_projection D S m (inclusion hA a) v).symm.trans
        (LinearEquiv.congr_fun (smallHom_quotient m hA hsq hindex a) _).symm)
  rw [fixed_quotient_card] at hi
  have hupper : Module.finrank S.field.Carrier (displacementSpace α.range) ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right (Finite.one_lt_card (α := S.field.Carrier))).mp
    simpa only [pow_one] using hi.trans hindex
  have hlower := card_actor_le_displacement_dimension α.range
  rw [hc] at hlower
  have hn : Module.finrank S.field.Carrier (displacementSpace α.range) ≠ 0 := by
    intro hz
    rw [hz] at hlower
    simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,pow_zero] at hlower
    have := Finite.one_lt_card (α := S.field.Carrier)
    omega
  change Module.finrank S.field.Carrier (displacementSpace α.range) = 1
  omega

private theorem quadratic_of_displacement_line
    {F : Type*} [Field F] [Finite F] (A : Subgroup (Sp F))
    (hd : Module.finrank F (displacementSpace A) = 1) :
    ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v := by
  let P := displacementSpace A
  have hn : P ≠ ⊥ := by
    intro hz
    change displacementSpace A = ⊥ at hz
    rw [hz,finrank_bot] at hd
    omega
  obtain ⟨u,hu,hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have hspan := (finrank_eq_one_iff_of_nonzero' (K := F) (⟨u,hu⟩ : P)
    (by intro hz; exact hu0 (congrArg Subtype.val hz))).mp hd
  have hPF : P ≤ TwoLocalCover.fixedSpace A := by
    rw [←orthogonal_displacementSpace]
    intro v hv w hw
    obtain ⟨a,ha⟩ := hspan ⟨v,hv⟩
    obtain ⟨b,hb⟩ := hspan ⟨w,hw⟩
    have ha' := congrArg Subtype.val ha
    have hb' := congrArg Subtype.val hb
    change a • u = v at ha'
    change b • u = w at hb'
    rw [←ha',←hb']
    simp [TwoLocalCover.form_alternating u]
  intro x hx y hy v
  exact hPF (Coinvariants.sub_mem_ker
    (ρ := (symplecticNatural 2).comp A.subtype) (⟨y,hy⟩ : A) v) x hx

/-- Both reciprocal coranks identify the full field-sized transvection root. -/
theorem smallHom_conjugate_root {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hA : A ≤ normalizer (V : Set G)) (hsq : ∀ a : A, a^2=1)
    (hindex : (centralizer (A : Set G)).relIndex V ≤ Nat.card S.field.Carrier)
    (hcorank : subgroupCorank A (A ⊓ centralizer (V : Set G)) = S.field.degree) :
    ∃ z : Sp S.field.Carrier,
      (smallHom m hA hsq hindex).range.map (MulAut.conj z).toMonoidHom = RootSubgroup.group 0 := by
  have hd := smallHom_displacement_dimension m hA hsq hindex hcorank
  apply FourLongRoots.exists_conjugate_root_of_displacement_one _ _ hd
    (quadratic_of_displacement_line _ hd)
  rw [smallHom_card,hcorank,S.field.card_eq]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Recognition
