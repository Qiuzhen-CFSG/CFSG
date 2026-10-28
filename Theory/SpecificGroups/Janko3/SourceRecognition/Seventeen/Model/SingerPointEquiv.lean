module
public import Theory.SpecificGroups.Janko3.SourceRecognition.BaumeisterParabolics.Point
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Point

/-!
# The marked Singer point group in the seventeen-point model

A field isomorphism between the two fields of order sixteen identifies the
translation groups. A scalar is sent to the diagonal with its eighth power:
conjugation by that diagonal acts by the original scalar. Fourth-power
Frobenius is sent to the literal field actor. Thus the entire Singer point
group is identified with the actual point stabilizer, and its given
complement is identified with the literal point-pair intersection.
-/

public noncomputable section
open Subgroup
open Theory.PSL2 Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.SingerPoint

open SingerField (K)
private abbrev Two := Multiplicative (ZMod 2)

private def powerEquiv {A : Type*} [CommGroup A] (r s : ℕ)
    (h : ∀ a : A, a ^ (r * s) = a) : MulAut A where
  toFun a := a ^ r
  invFun a := a ^ s
  left_inv a := (pow_mul a r s).symm.trans (h a)
  right_inv a := (pow_mul a s r).symm.trans (by simpa only [Nat.mul_comm] using h a)
  map_mul' a b := mul_pow a b r

private theorem unit_pow_sixteen (u : Kˣ) : u ^ 16 = u := by
  apply Units.ext
  exact SingerField.field_card ▸ FiniteField.pow_card (u : K)

private theorem two_cases (a : Two) : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  revert a
  decide +kernel

private def powerFour : MulAut Kˣ := powerEquiv 4 4 unit_pow_sixteen

private def involutionAction {A : Type*} [Group A] (σ : MulAut A)
    (hσ : σ * σ = 1) : Two →* MulAut A where
  toFun a := if a = 1 then 1 else σ
  map_one' := by simp
  map_mul' a b := by
    rcases two_cases a with rfl | rfl <;> rcases two_cases b with rfl | rfl
    · simp
    · simp
    · simp
    · have hn : (Multiplicative.ofAdd (1 : ZMod 2) : Two) ≠ 1 := by decide
      have hs : (Multiplicative.ofAdd (1 : ZMod 2) : Two) *
          Multiplicative.ofAdd 1 = 1 := by decide
      simp only [hs,if_true,if_neg hn,hσ]

private def unitAction : Two →* MulAut Kˣ :=
  involutionAction powerFour (MulEquiv.ext fun u =>
    (pow_mul u 4 4).symm.trans (unit_pow_sixteen u))

private theorem unitAction_generator (u : Kˣ) :
    unitAction (Multiplicative.ofAdd 1) u = u ^ 4 := rfl

private abbrev ScalarActor := Kˣ ⋊[unitAction] Two

private instance : Fintype ScalarActor :=
  Fintype.ofEquiv (Kˣ × Two) SemidirectProduct.equivProd.symm

private def complementCoordinates (c : Complement) : ScalarActor :=
  match c.2 with
  | .r j => ⟨BaumeisterParabolics.alpha ^ (5 * c.1.toAdd.val) *
      BaumeisterParabolics.alpha ^ (3 * j.val), 1⟩
  | .sr j => ⟨BaumeisterParabolics.alpha ^ (5 * c.1.toAdd.val) *
      BaumeisterParabolics.alpha ^ (12 * j.val), Multiplicative.ofAdd 1⟩

private def complementCoordinatesHom : Complement →* ScalarActor where
  toFun := complementCoordinates
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private def complementCoordinatesEquiv : Complement ≃* ScalarActor :=
  MulEquiv.ofBijective complementCoordinatesHom (by decide +kernel)

private theorem complementCoordinates_action : ∀ (c : Complement) (t : K),
    BaumeisterParabolics.complementHom c t =
      (complementCoordinates c).left *
        (if (complementCoordinates c).right = 1 then t else t ^ 4) := by
  decide +kernel

private def normalizerCoordinates : SingerField.normalizer ≃* ScalarActor :=
  BaumeisterParabolics.complementEquiv.symm.trans complementCoordinatesEquiv

private theorem normalizerCoordinates_action (n : SingerField.normalizer) (t : K) :
    n.val t = (normalizerCoordinates n).left *
      (if (normalizerCoordinates n).right = 1 then t else t ^ 4) := by
  obtain ⟨c,rfl⟩ := BaumeisterParabolics.complementEquiv.surjective n
  have h₁ : (BaumeisterParabolics.complementEquiv c).val =
      BaumeisterParabolics.complementHom c := rfl
  have h₂ : complementCoordinatesEquiv c = complementCoordinates c := rfl
  simpa only [normalizerCoordinates, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply,h₁,h₂] using complementCoordinates_action c t

/-- A fixed field identification; the subsequent maps retain its literal action. -/
def fieldEquiv : K ≃+* F := by
  letI := Fintype.ofFinite F
  apply FiniteField.ringEquivOfCardEq
  rw [SingerField.field_card, ← Nat.card_eq_fintype_card, field_card]

private def halfPower : MulAut Kˣ := powerEquiv 8 2 unit_pow_sixteen

private def unitEquiv : Kˣ ≃* Fˣ :=
  halfPower.trans (Units.mapEquiv fieldEquiv.toMulEquiv)

private theorem unitEquiv_square (u : Kˣ) : (unitEquiv u : F)^2 = fieldEquiv u := by
  change (fieldEquiv ((u ^ 8 : Kˣ) : K))^2 = fieldEquiv u
  calc
    _ = fieldEquiv (((u ^ 8)^2 : Kˣ) : K) :=
      (map_pow fieldEquiv ((u ^ 8 : Kˣ) : K) 2).symm
    _ = fieldEquiv (u : K) := congrArg (fun v : Kˣ => fieldEquiv (v : K))
      ((pow_mul u 8 2).symm.trans (unit_pow_sixteen u))

private theorem actorEquiv_symm_generator :
    actorEquiv.symm (Multiplicative.ofAdd 1) = actorGenerator :=
  actorEquiv.injective (by rw [MulEquiv.apply_symm_apply,actorEquiv_generator])

private def scalarActorEquiv : ScalarActor ≃* Fˣ ⋊[unitsAction] Actor :=
  SemidirectProduct.congr unitEquiv actorEquiv.symm (by
    intro a
    apply MulEquiv.ext
    intro u
    rcases two_cases a with rfl | rfl
    · simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply]
    · simp only [MulEquiv.trans_apply,actorEquiv_symm_generator,unitsAction_generator,
        unitAction_generator,map_pow])

private theorem actor_apply (a : Two) (t : K) :
    (actorEquiv.symm a).val (fieldEquiv t) =
      fieldEquiv (if a = 1 then t else t ^ 4) := by
  rcases two_cases a with rfl | rfl
  · simp
  · rw [actorEquiv_symm_generator]
    change fieldInvolution (fieldEquiv t) = _
    have hn : (Multiplicative.ofAdd (1 : ZMod 2) : Two) ≠ 1 := by decide
    simp only [fieldInvolution_apply,if_neg hn,map_pow]

/-- The prescribed scalar/Frobenius map onto the literal overlap complement. -/
def complementEquiv : SingerField.normalizer ≃* C :=
  normalizerCoordinates.trans (scalarActorEquiv.trans
    (torusLiftEquiv.trans (subgroupOfEquivOfLe inf_le_left).symm))

private def rootMap : Multiplicative K →* Model :=
  rootHom.comp fieldEquiv.toAddEquiv.toMultiplicative.toMonoidHom

private def complementMap : SingerField.normalizer →* Model :=
  torusLift.comp (scalarActorEquiv.toMonoidHom.comp normalizerCoordinates.toMonoidHom)

private theorem complementMap_eq (n : SingerField.normalizer) :
    complementMap n = ((complementEquiv n : point) : Model) := rfl

private theorem action_compatibility (n : SingerField.normalizer) :
    rootMap.comp (SingerField.action n).toMonoidHom =
      (MulAut.conj (complementMap n)).toMonoidHom.comp rootMap := by
  apply MonoidHom.ext
  intro t
  change rootHom (Multiplicative.ofAdd (fieldEquiv (n.val t.toAdd))) =
    torusLift (scalarActorEquiv (normalizerCoordinates n)) *
      rootHom (Multiplicative.ofAdd (fieldEquiv t.toAdd)) *
        (torusLift (scalarActorEquiv (normalizerCoordinates n)))⁻¹
  rw [torusLift_root]
  apply congrArg rootHom
  apply congrArg Multiplicative.ofAdd
  change fieldEquiv (n.val t.toAdd) =
    (unitEquiv (normalizerCoordinates n).left : F)^2 *
      (actorEquiv.symm (normalizerCoordinates n).right).val (fieldEquiv t.toAdd)
  rw [unitEquiv_square,actor_apply,normalizerCoordinates_action,map_mul]

private def ambientHom : SingerField.Model →* Model :=
  SemidirectProduct.lift rootMap complementMap action_compatibility

private theorem ambientHom_mem (x : SingerField.Model) : ambientHom x ∈ point := by
  apply point.mul_mem
  · exact root_le_point ⟨_,rfl⟩
  · exact (complementEquiv x.right).val.property

private def pointHom : SingerField.Model →* point :=
  ambientHom.codRestrict point ambientHom_mem

private theorem pointHom_surjective : Function.Surjective pointHom := by
  intro x
  obtain ⟨⟨r,c⟩,he,-⟩ := pointComplement.existsUnique x
  obtain ⟨t,ht⟩ := r.property
  obtain ⟨u,hu⟩ := fieldEquiv.toAddEquiv.toMultiplicative.surjective t
  obtain ⟨n,hn⟩ := complementEquiv.surjective c
  refine ⟨⟨u,n⟩,?_⟩
  apply Subtype.ext
  change rootMap u * complementMap n = (x : Model)
  rw [complementMap_eq,hn]
  change rootHom (fieldEquiv.toAddEquiv.toMultiplicative u) * ((c : point) : Model) = _
  rw [hu,ht]
  exact congrArg Subtype.val he

/-- The Singer model as the actual point stabilizer, with its literal complement. -/
def pointEquiv : SingerField.Model ≃* point := by
  letI : Finite SingerField.Model := Nat.finite_of_card_ne_zero
    (by rw [SingerField.model_card]; decide)
  exact MulEquiv.ofBijective pointHom
    ((Nat.bijective_iff_surjective_and_card pointHom).mpr
      ⟨pointHom_surjective,by rw [SingerField.model_card,point_card]⟩)

theorem pointEquiv_root (t : Multiplicative K) :
    (pointEquiv (SingerField.root t) : Model) =
      rootHom (fieldEquiv.toAddEquiv.toMultiplicative t) := by
  exact SemidirectProduct.lift_inl rootMap complementMap action_compatibility t

theorem pointEquiv_inr (n : SingerField.normalizer) :
    pointEquiv (SemidirectProduct.inr n) = (complementEquiv n : point) := by
  apply Subtype.ext
  exact (SemidirectProduct.lift_inr rootMap complementMap action_compatibility n).trans
    (complementMap_eq n)

/-- The original designated complement maps exactly to the point-pair intersection. -/
theorem pointEquiv_complement :
    BaumeisterParabolics.pointComplement.map pointEquiv.toMonoidHom = C := by
  apply le_antisymm
  · rintro _ ⟨x,⟨n,rfl⟩,rfl⟩
    change pointEquiv (SemidirectProduct.inr n) ∈ C
    rw [pointEquiv_inr]
    exact (complementEquiv n).property
  · intro c hc
    obtain ⟨n,hn⟩ := complementEquiv.surjective ⟨c,hc⟩
    exact ⟨SemidirectProduct.inr n,⟨n,rfl⟩,by
      change pointEquiv (SemidirectProduct.inr n) = c
      rw [pointEquiv_inr,hn]⟩

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.SingerPoint
