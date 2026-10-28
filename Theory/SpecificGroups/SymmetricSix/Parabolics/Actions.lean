module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.PolarSpace
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
# The six-letter action on the binary symplectic points

The duad table identifies the two-element subsets of six letters. Transporting
that action gives faithful primitive actions of both `S₆` and `A₆` on duads.
Under `duadPolarEquiv`, disjointness is symplectic orthogonality. The transported
permutation of nonzero vectors extends by fixing zero; preservation of the
binary alternating form and its nondegeneracy force this extension to be linear.
We obtain an injective homomorphism into the actual matrix symplectic group,
with an explicit equivariance theorem for the natural module.

`Duad` and `Syntheme` in the original tables are both aliases of `Fin 15`.
The instance in this module is the **duad** action. A syntheme action must use
its own named action structure, rather than this instance.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.4,
the proof of I.5.8, and I.5.9, printed pp.420–422. This module supplies the
point action; line actions and stabilizer orbits are separate obligations.
-/

@[expose] public section

open Finset
open scoped Matrix
namespace Theory.SpecificGroups.SymmetricSix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem duadSet_injective : Function.Injective duadSet := by decide

theorem duadSet_complete (s : Finset Letter) (hs : s.card = 2) :
    ∃ d, duadSet d = s := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
  have h : ∀ a b : Letter, a ≠ b → ∃ d, duadSet d = {a, b} := by decide
  exact h a b hab

noncomputable def duadPairEquiv : Duad ≃ Set.powersetCard Letter 2 :=
  Equiv.ofBijective (fun d => ⟨duadSet d, duad_is_duad d⟩)
    ⟨fun _ _ h => duadSet_injective (congrArg Subtype.val h), by
      intro ⟨s, hs⟩
      obtain ⟨d, hd⟩ := duadSet_complete s hs
      exact ⟨d, Subtype.ext hd⟩⟩

noncomputable instance duadAction : MulAction S6 Duad where
  smul g d := duadPairEquiv.symm (g • duadPairEquiv d)
  one_smul d := by
    change duadPairEquiv.symm (1 • duadPairEquiv d) = d
    simp
  mul_smul g h d := by
    change duadPairEquiv.symm ((g * h) • duadPairEquiv d) =
      duadPairEquiv.symm (g • duadPairEquiv (duadPairEquiv.symm (h • duadPairEquiv d)))
    simp [mul_smul]

@[simp] theorem duadPairEquiv_smul (g : S6) (d : Duad) :
    duadPairEquiv (g • d) = g • duadPairEquiv d := by
  change duadPairEquiv (duadPairEquiv.symm _) = _
  exact duadPairEquiv.apply_symm_apply _

@[simp] theorem duadSet_smul (g : S6) (d : Duad) :
    duadSet (g • d) = (duadSet d).image g := by
  exact congrArg Subtype.val (duadPairEquiv_smul g d)

private noncomputable def pairToDuadHom : Set.powersetCard Letter 2 →[S6] Duad where
  toFun := duadPairEquiv.symm
  map_smul' g p := by
    apply duadPairEquiv.injective
    simp

instance duad_preprimitive : MulAction.IsPreprimitive S6 Duad := by
  have : MulAction.IsPreprimitive S6 (Set.powersetCard Letter 2) :=
    Set.powersetCard.isPreprimitive_perm (by decide) (by norm_num [Letter]) (by norm_num [Letter])
  exact MulAction.IsPreprimitive.of_surjective (f := pairToDuadHom)
    duadPairEquiv.symm.surjective

instance duad_faithful : FaithfulSMul S6 Duad := by
  have : FaithfulSMul S6 (Set.powersetCard Letter 2) :=
    Set.powersetCard.faithfulSMul (by decide) (by norm_num [Letter])
  exact FaithfulSMul.of_injective pairToDuadHom duadPairEquiv.symm.injective

private noncomputable def a6PairToDuadHom : Set.powersetCard Letter 2 →[A6] Duad where
  toFun := duadPairEquiv.symm
  map_smul' g p := pairToDuadHom.map_smul' g.val p

instance a6_duad_preprimitive : MulAction.IsPreprimitive A6 Duad := by
  have ht : MulAction.IsPretransitive A6 (Set.powersetCard Letter 2) :=
    Set.powersetCard.isPretransitive_alternatingGroup (by norm_num [Letter])
  have : Nontrivial (Set.powersetCard Letter 2) :=
    Set.powersetCard.nontrivial' (by decide) (by norm_num [Letter])
  have : MulAction.IsPreprimitive A6 (Set.powersetCard Letter 2) := by
    rw [← MulAction.isCoatom_stabilizer_iff_preprimitive _ (duadPairEquiv 0)]
    rw [Set.powersetCard.stabilizer_coe (G := A6) (duadPairEquiv 0)]
    apply alternatingGroup.isCoatom_stabilizer
    · exact ⟨0, by change 0 ∈ duadSet 0; decide⟩
    · exact ⟨2, by change 2 ∉ duadSet 0; decide⟩
    · change Nat.card Letter ≠ 2 * (↑(duadSet 0) : Set Letter).ncard
      simp [Set.ncard_coe_finset, duad_is_duad, Letter]
  exact MulAction.IsPreprimitive.of_surjective (f := a6PairToDuadHom)
    duadPairEquiv.symm.surjective

instance a6_duad_faithful : FaithfulSMul A6 Duad := inferInstance


theorem duadCollinear_smul_iff (g : S6) (d e : Duad) :
    duadCollinear (g • d) (g • e) ↔ duadCollinear d e := by
  unfold duadCollinear
  rw [duadSet_smul, duadSet_smul, ← Finset.image_inter _ _ g.injective,
    Finset.card_image_of_injective _ g.injective]
  simp only [ne_eq, smul_left_cancel_iff]

/-- The permutation of the nonzero vectors induced by permuting the six letters. -/
noncomputable def polarPointPerm (g : S6) : Equiv.Perm BinaryPoint :=
  duadPolarEquiv.symm.trans ((MulAction.toPerm g).trans duadPolarEquiv)

@[simp] theorem polarPointPerm_vector (g : S6) (d : Duad) :
    polarPointPerm g (polarVector d) = polarVector (g • d) := by
  change duadPolarEquiv (g • duadPolarEquiv.symm (duadPolarEquiv d)) = duadPolarEquiv (g • d)
  simp

theorem polarPointPerm_orthogonal (g : S6) (v w : BinaryPoint) :
    polarForm (polarPointPerm g v).val (polarPointPerm g w).val = 0 ↔
      polarForm v.val w.val = 0 := by
  obtain ⟨d, rfl⟩ := polarVector_bijective.2 v
  obtain ⟨e, rfl⟩ := polarVector_bijective.2 w
  rw [polarPointPerm_vector, polarPointPerm_vector,
    polarVector_orthogonal, polarVector_orthogonal, duadCollinear_smul_iff]
  simp only [smul_left_cancel_iff]

noncomputable def polarAction (g : S6) (v : NaturalModule) : NaturalModule :=
  if h : v = 0 then 0 else (polarPointPerm g ⟨v, h⟩).val

@[simp] theorem polarAction_zero (g : S6) : polarAction g 0 = 0 := by
  simp [polarAction]

@[simp] theorem polarAction_point (g : S6) (v : BinaryPoint) :
    polarAction g v.val = (polarPointPerm g v).val := by
  simp [polarAction, v.property]

@[simp] theorem polarAction_vector (g : S6) (d : Duad) :
    polarAction g (polarVector d).val = (polarVector (g • d)).val := by
  rw [polarAction_point, polarPointPerm_vector]

theorem polarAction_surjective (g : S6) : Function.Surjective (polarAction g) := by
  intro v
  by_cases h : v = 0
  · exact ⟨0, by simp [h]⟩
  · obtain ⟨w, hw⟩ := (polarPointPerm g).surjective ⟨v, h⟩
    exact ⟨w.val, (polarAction_point g w).trans (congrArg Subtype.val hw)⟩

theorem polarAction_form (g : S6) (v w : NaturalModule) :
    polarForm (polarAction g v) (polarAction g w) = polarForm v w := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases hw : w = 0
  · simp [hw]
  have he := polarPointPerm_orthogonal g ⟨v, hv⟩ ⟨w, hw⟩
  rw [← polarAction_point, ← polarAction_point] at he
  have hbinary : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  exact hbinary _ _ he

theorem polarAction_add (g : S6) (v w : NaturalModule) :
    polarAction g (v + w) = polarAction g v + polarAction g w := by
  apply sub_eq_zero.mp
  apply polarForm_nondegenerate.1
  intro z
  obtain ⟨z, rfl⟩ := polarAction_surjective g z
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply,
    polarAction_form, sub_self]

theorem polarAction_smul (g : S6) (c : ZMod 2) (v : NaturalModule) :
    polarAction g (c • v) = c • polarAction g v := by
  have hc : c = 0 ∨ c = 1 := by decide +revert
  rcases hc with rfl | rfl <;> simp

noncomputable def polarLinearMap (g : S6) : NaturalModule →ₗ[ZMod 2] NaturalModule where
  toFun := polarAction g
  map_add' := polarAction_add g
  map_smul' := polarAction_smul g


@[simp] theorem polarAction_one (v : NaturalModule) : polarAction 1 v = v := by
  by_cases hv : v = 0
  · simp [hv]
  · obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨v, hv⟩
    have h : (polarVector d).val = v := congrArg Subtype.val hd
    rw [← h, polarAction_vector, one_smul]

@[simp] theorem polarAction_mul (g h : S6) (v : NaturalModule) :
    polarAction (g * h) v = polarAction g (polarAction h v) := by
  by_cases hv : v = 0
  · simp [hv]
  · obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨v, hv⟩
    have hvd : (polarVector d).val = v := congrArg Subtype.val hd
    rw [← hvd, polarAction_vector, polarAction_vector, polarAction_vector, mul_smul]

/-- The six-letter action is linear on the natural binary module. -/
noncomputable instance polarModuleAction : DistribMulAction S6 NaturalModule where
  smul := polarAction
  one_smul := polarAction_one
  mul_smul := polarAction_mul
  smul_zero := polarAction_zero
  smul_add := polarAction_add

noncomputable instance polarPointAction : MulAction S6 BinaryPoint where
  smul g v := polarPointPerm g v
  one_smul v := by
    apply Subtype.ext
    exact (polarAction_point 1 v).symm.trans (polarAction_one v.val)
  mul_smul g h v := by
    apply Subtype.ext
    change (polarPointPerm (g * h) v).val =
      (polarPointPerm g (polarPointPerm h v)).val
    simpa only [polarAction_point] using polarAction_mul g h v.val

/-- Equivariance for the actual linear action on the binary module. -/
theorem duadPolarEquiv_equivariant (g : S6) (d : Duad) :
    duadPolarEquiv (g • d) = g • duadPolarEquiv d :=
  (polarPointPerm_vector g d).symm

/-- The disjointness graph is equivariantly the symplectic orthogonality graph. -/
theorem polar_equivariant_relation (g : S6) (d e : Duad) :
    duadCollinear d e ↔
      g • duadPolarEquiv d ≠ g • duadPolarEquiv e ∧
      polarForm (g • (polarVector d).val) (g • (polarVector e).val) = 0 := by
  change duadCollinear d e ↔
    polarPointPerm g (polarVector d) ≠ polarPointPerm g (polarVector e) ∧ _
  rw [(polarPointPerm g).injective.ne_iff, polarVector_injective.ne_iff]
  change duadCollinear d e ↔ d ≠ e ∧
    polarForm (polarAction g (polarVector d).val)
      (polarAction g (polarVector e).val) = 0
  rw [polarAction_form, polarVector_orthogonal]
  exact ⟨fun h => ⟨h.1, Or.inr h⟩, fun ⟨hne, h⟩ => h.resolve_left hne⟩

private noncomputable def duadToPolarHom : Duad →[S6] BinaryPoint where
  toFun := duadPolarEquiv
  map_smul' := duadPolarEquiv_equivariant

instance polarPoint_preprimitive : MulAction.IsPreprimitive S6 BinaryPoint :=
  MulAction.IsPreprimitive.of_surjective (f := duadToPolarHom) duadPolarEquiv.surjective

instance polarPoint_faithful : FaithfulSMul S6 BinaryPoint :=
  FaithfulSMul.of_injective duadToPolarHom duadPolarEquiv.injective

private noncomputable def a6DuadToPolarHom : Duad →[A6] BinaryPoint where
  toFun := duadPolarEquiv
  map_smul' g d := duadPolarEquiv_equivariant g.val d

instance a6_polarPoint_preprimitive : MulAction.IsPreprimitive A6 BinaryPoint :=
  MulAction.IsPreprimitive.of_surjective (f := a6DuadToPolarHom) duadPolarEquiv.surjective

instance a6_polarPoint_faithful : FaithfulSMul A6 BinaryPoint := inferInstance

/-- A concrete matrix representation, in the standard `Matrix.J` convention. -/
noncomputable def polarRepresentation : S6 →* Matrix.symplecticGroup (Fin 2) (ZMod 2) where
  toFun g := ⟨(polarLinearMap g).toMatrix', by
    rw [SymplecticGroup.mem_iff']
    have hf : polarForm.comp (polarLinearMap g) (polarLinearMap g) = polarForm := by
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      exact polarAction_form g v w
    have hm := congrArg LinearMap.BilinForm.toMatrix' hf
    rw [LinearMap.BilinForm.toMatrix'_comp] at hm
    simpa only [polarForm, LinearMap.BilinForm.toMatrix'_toBilin'] using hm⟩
  map_one' := by
    apply Subtype.ext
    change (polarLinearMap 1).toMatrix' = 1
    have h : polarLinearMap 1 = 1 := by
      apply LinearMap.ext
      exact polarAction_one
    rw [h, LinearMap.toMatrix'_one]
  map_mul' g h := by
    apply Subtype.ext
    change (polarLinearMap (g * h)).toMatrix' =
      (polarLinearMap g).toMatrix' * (polarLinearMap h).toMatrix'
    rw [← LinearMap.toMatrix'_mul]
    congr 1
    apply LinearMap.ext
    exact polarAction_mul g h

/-- The matrix action sends the vector of a duad to that of its permuted duad. -/
theorem polarRepresentation_equivariant (g : S6) (d : Duad) :
    (polarRepresentation g).val *ᵥ (polarVector d).val = (polarVector (g • d)).val := by
  change (polarLinearMap g).toMatrix' *ᵥ _ = _
  rw [LinearMap.toMatrix'_mulVec]
  exact polarAction_vector g d

theorem polarRepresentation_injective : Function.Injective polarRepresentation := by
  intro g h hgh
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Duad)
  intro d
  apply polarVector_injective
  apply Subtype.ext
  rw [← polarRepresentation_equivariant, ← polarRepresentation_equivariant, hgh]

/-- Transitivity stated as a transporter, including the alternating subgroup. -/
theorem a6_duad_transitive (d e : Duad) : ∃ g : A6, g • d = e :=
  MulAction.exists_smul_eq A6 d e

theorem duad_transitive (d e : Duad) : ∃ g : S6, g • d = e :=
  MulAction.exists_smul_eq S6 d e

theorem a6_polarPoint_transitive (v w : BinaryPoint) : ∃ g : A6, g • v = w :=
  MulAction.exists_smul_eq A6 v w

theorem polarPoint_transitive (v w : BinaryPoint) : ∃ g : S6, g • v = w :=
  MulAction.exists_smul_eq S6 v w

/-- The point action uses the original, concrete parabolic subgroup. -/
theorem duad_stabilizer_zero : MulAction.stabilizer S6 (0 : Duad) = duadStabilizer := by
  ext g
  change g • (0 : Duad) = 0 ↔ (pair 0 1).image g = pair 0 1
  rw [← duadSet_injective.eq_iff, duadSet_smul]
  rfl

theorem a6_duad_stabilizer_zero :
    MulAction.stabilizer A6 (0 : Duad) = a6DuadStabilizer := by
  ext g
  change (g.val • (0 : Duad) = 0) ↔ g.val ∈ duadStabilizer
  exact SetLike.ext_iff.mp duad_stabilizer_zero g.val

/-- Compatibility on every vector, not only the nonzero point representatives. -/
theorem polarRepresentation_apply (g : S6) (v : NaturalModule) :
    (polarRepresentation g).val *ᵥ v = polarAction g v :=
  LinearMap.toMatrix'_mulVec (polarLinearMap g) v

end Theory.SpecificGroups.SymmetricSix
