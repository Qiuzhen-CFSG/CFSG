module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.Sp4

/-!
# A symplectic realization of the literal reciprocal action

Pull back the original alternating form by a field-linear reciprocal actor.
Its conjugation of the full component action makes the associated dual
endomorphism commute with the natural derived action. The proved scalar
commutant therefore makes the pulled-back form a scalar multiple of the
original one. Involutivity and characteristic two force that scalar to be one.
Taking matrices yields a genuine homomorphism into Sp₄ with the exact
reciprocal evaluation formula.

The invariant-form argument adapts the proof idea in
`SymplecticConjugatePair.Ambient.Normalizer.NaturalSemilinear` to the literal
original quotient and uses its public scalar-commutant theorem. No assumed
symplectic realization or matrix-action tag occurs in the source application.
Source: Aschbacher--Smith 11.3.7(4), printed p.773 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal

private theorem involutive_normalizer_preserves_form
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (a : Vector F →ₗ[F] Vector F) (ha : Function.Involutive a)
    (hnat : ∀ x : Sp F, ∃ y : Sp F, ∀ v, a (x • v) = y • a v) :
    ∀ v w, form F (a v) (a w) = form F v w := by
  let B := (form F).comp a a
  let Q : Module.End F (Vector F) :=
    ((form F).toDual TwoLocalCover.form_nondegenerate).symm.toLinearMap.comp B
  have hQ (v w : Vector F) : form F (Q v) w = form F (a v) (a w) :=
    LinearMap.BilinForm.apply_toDual_symm_apply
      (hB := TwoLocalCover.form_nondegenerate) (B v) w
  have hB (x : Sp F) (v w : Vector F) :
      form F (a (x • v)) (a (x • w)) = form F (a v) (a w) := by
    obtain ⟨y, hy⟩ := hnat x
    rw [hy,hy]
    exact preserves_form y (a v) (a w)
  obtain ⟨c,hc⟩ :=
    SymplecticConjugatePair.Ambient.Normalizer.Commutant.natural_centralizer_scalar
      Q.toAddMonoidHom (by
        intro x v
        change Q (x.val • v) = x.val • Q v
        apply ((form F).toDual TwoLocalCover.form_nondegenerate).injective
        apply LinearMap.ext
        intro w
        obtain ⟨w,rfl⟩ : ∃ z : Vector F, x.val • z = w :=
          ⟨x.val⁻¹ • w,by simp⟩
        change form F (Q (x.val • v)) (x.val • w) =
          form F (x.val • Q v) (x.val • w)
        rw [hQ,hB,←hQ]
        exact (preserves_form x.val (Q v) w).symm)
  have hmul (v w : Vector F) : form F (a v) (a w) = c * form F v w := by
    rw [←hQ,show Q v = c • v from hc v]
    simp
  have hsq : c ^ 2 = 1 := by
    have h := hmul (a (Pi.single (.inl 0) 1)) (a (Pi.single (.inr 0) 1))
    rw [ha,ha,hmul] at h
    simpa [form_apply,Pi.single_apply,pow_two] using h.symm
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hsq)
  simpa only [hc1,one_mul] using hmul

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

private theorem reciprocal_sp4_intertwines
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (g : G)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (w : omegaClosure T H) (x : Sp S.field.Carrier) :
    ∃ y : Sp S.field.Carrier, ∀ v : Vector S.field.Carrier,
      reciprocalAction (.sp4 a) g hN w (x • v) =
        symplecticNatural (k := S.field.Carrier) 2 y (reciprocalAction (.sp4 a) g hN w v) := by
  let c := Coordinates.sp4 a
  let N := normalizer (V : Set G)
  let J := L.subgroupOf N
  let e : J ≃* L := subgroupOfEquivOfLe D.normalizes
  let q : J →* c.ModelGroup := c.quotientMap.comp e.toMonoidHom
  let hNV := WeakClosure.seed_normalizer_le D S
  let _ : J.Normal := normal_subgroupOf_of_le_normalizer hNV
  let ρ := c.conjugationAction hNV le_rfl
  have hnat (j : J) (v : c.Space) : ρ (j : N) v = c.modelAction (q j) v := by
    obtain ⟨u,hu⟩ := c.projection_surjective (Multiplicative.ofAdd v)
    rw [←show (c.projection u).toAdd = v from congrArg Multiplicative.toAdd hu]
    change ρ (j : N) (c.projection u).toAdd =
      c.modelAction (c.quotientMap (e j)) (c.projection u).toAdd
    rw [c.conjugationAction_projection,←c.projection_component_conjugation]
    rfl
  obtain ⟨j,hj⟩ := (c.quotientMap_surjective.comp e.surjective) x
  let z : N := reciprocalNormalizerHom g hN w
  let b := J.normalizerMonoidHom ⟨z,J.normalizer_eq_top ▸ mem_top z⟩
  change q j = x at hj
  refine ⟨q (b j),?_⟩
  change ∀ v : c.Space, ρ z (c.modelAction x v) = c.modelAction (q (b j)) (ρ z v)
  intro v
  rw [←hj,←hnat j v,←hnat (b j) (ρ z v)]
  change ρ z (ρ (j : N) v) = ρ (z * (j : N) * z⁻¹) (ρ z v)
  simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]

/-- Every actual reciprocal actor preserves the original symplectic form. -/
theorem sp4_reciprocal_preserves_form
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 a)) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (w : omegaClosure T H) :
    ∀ v z, form S.field.Carrier (reciprocalAction (.sp4 a) g hN w v)
      (reciprocalAction (.sp4 a) g hN w z) = form S.field.Carrier v z := by
  let ρ := reciprocalAction (.sp4 a) g hN
  let l : Vector S.field.Carrier →ₗ[S.field.Carrier] Vector S.field.Carrier :=
    { toFun := ρ w
      map_add' := (ρ w).map_add
      map_smul' := sp4_reciprocal_action_linear a f g n hN w }
  apply involutive_normalizer_preserves_form l
  · intro v
    change ρ w (ρ w v) = v
    rw [←Module.End.mul_apply,←map_mul,←pow_two,n.square_eq_one w,map_one]
    rfl
  · exact reciprocal_sp4_intertwines a g hN w

/-- A genuine symplectic matrix homomorphism realizing exactly the reciprocal
conjugation action, with the original field and selected conjugator. -/
theorem sp4_reciprocal_symplectic_realization
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 a)) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ∃ α : omegaClosure T H →* Sp S.field.Carrier,
      ∀ w (v : Vector S.field.Carrier), α w • v = reciprocalAction (.sp4 a) g hN w v := by
  let ρ := reciprocalAction (.sp4 a) g hN
  let l (w : omegaClosure T H) :
      Vector S.field.Carrier →ₗ[S.field.Carrier] Vector S.field.Carrier :=
    { toFun := ρ w
      map_add' := (ρ w).map_add
      map_smul' := sp4_reciprocal_action_linear a f g n hN w }
  have hl1 : l 1 = 1 := by
    apply LinearMap.ext
    intro v
    change ρ 1 v = v
    rw [map_one]
    rfl
  have hlmul (u w : omegaClosure T H) : l (u*w) = l u * l w := by
    apply LinearMap.ext
    intro v
    change ρ (u*w) v = ρ u (ρ w v)
    rw [map_mul]
    rfl
  let α (w : omegaClosure T H) : Sp S.field.Carrier :=
    ⟨LinearMap.toMatrix' (l w), by
      apply SymplecticGroup.mem_iff'.mpr
      have he := Matrix.toBilin'_comp (-Matrix.J (Fin 2) S.field.Carrier)
        (LinearMap.toMatrix' (l w)) (LinearMap.toMatrix' (l w))
      have hp : (form S.field.Carrier).comp (l w) (l w) = form S.field.Carrier := by
        apply LinearMap.ext
        intro v
        apply LinearMap.ext
        intro z
        exact sp4_reciprocal_preserves_form a f g n hN w v z
      simp only [Matrix.toLin'_toMatrix'] at he
      have hm := Matrix.toBilin'.injective (he.symm.trans hp)
      simpa [Matrix.mul_neg,Matrix.neg_mul,form] using hm⟩
  refine ⟨{ toFun := α
            map_one' := ?_
            map_mul' := ?_ },fun w v => LinearMap.toMatrix'_mulVec (l w) v⟩
  · apply Subtype.ext
    change LinearMap.toMatrix' (l 1) = 1
    rw [hl1,LinearMap.toMatrix'_one]
  · intro u w
    apply Subtype.ext
    change LinearMap.toMatrix' (l (u*w)) =
      LinearMap.toMatrix' (l u) * LinearMap.toMatrix' (l w)
    rw [hlmul,LinearMap.toMatrix'_mul]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
