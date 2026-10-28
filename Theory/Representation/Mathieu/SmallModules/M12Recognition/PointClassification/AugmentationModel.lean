module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.Reduction
public import Mathlib.Logic.Equiv.Option

/-!
# The actual M₁₁ augmentation model inside the M₁₂ heart

Extend an eleven-point vector by zero at the twelfth point, using the actual
Atlas point embedding, and take its class modulo constants. On augmentation
kernels this is injective: a constant vector vanishing at point twelve is zero.
Both spaces have dimension ten, so this gives an equivariant linear equivalence.
The marking and the inverse-permutation action convention are preserved.

Faithfulness of the augmentation action follows by adding its complementary
constant line. The order-eleven degree bound then proves irreducibility of the
reference point action. These results construct and compare the reference module;
they do not assert completeness of the degree-ten M₁₁ modules.

Source application: Aschbacher--Smith, G.7.3(2), printed p.348 (PDF p.359),
citing G. D. James, J. Algebra 27 (1973), 57--111. The concrete point
embedding is from `Theory.Mathieu.M12.Properties.PointStabilizer`.
-/

public section

open Sporadic.Mathieu BinaryPermutation
namespace Representation.MathieuSmall.M12Recognition.PointClassification

private def points : Option (Fin 11) ≃ Fin 12 :=
  (Equiv.optionCongr m11M12PointEquiv).trans (Equiv.optionSubtypeNe (12 : Fin 12))

private theorem points_none : points none = (12 : Fin 12) := rfl
private theorem points_some (i : Fin 11) : points (some i) = m11M12PointEmbedding i := rfl

private noncomputable def extendZero : Full (Fin 11) →ₗ[ZMod 2] Full (Fin 12) where
  toFun v j := (points.symm j).elim 0 v
  map_add' v w := by ext j; cases h : points.symm j <;> simp [h]
  map_smul' c v := by ext j; cases h : points.symm j <;> simp [h]

private theorem extendZero_twelve (v : Full (Fin 11)) : extendZero v (12 : Fin 12) = 0 := by
  change (points.symm (points none)).elim 0 v = 0
  simp

private theorem extendZero_embedded (v : Full (Fin 11)) (i : Fin 11) :
    extendZero v (m11M12PointEmbedding i) = v i := by
  change (points.symm (points (some i))).elim 0 v = v i
  simp

private theorem augmentation_extendZero (v : Full (Fin 11)) :
    augmentation (Fin 12) (extendZero v) = augmentation (Fin 11) v := by
  change (∑ j, extendZero v j) = ∑ i, v i
  rw [← Equiv.sum_comp points]
  simp only [Fintype.sum_option, points_none, points_some,
    extendZero_twelve, extendZero_embedded, zero_add]

private theorem extendZero_equivariant (g : M11) (v : Full (Fin 11)) :
    extendZero (representation (Fin 11) g.val v) =
      representation (Fin 12) (pointEmbedding g).val (extendZero v) := by
  ext j
  obtain ⟨i, rfl⟩ := points.surjective j
  cases i with
  | none =>
      rw [points_none, extendZero_twelve, representation_apply]
      change 0 = extendZero v ((m11ToM12ExtendHom g)⁻¹ (12 : Fin 12))
      rw [← map_inv, m11ToM12ExtendHom_apply_12, extendZero_twelve]
  | some i =>
      rw [points_some, extendZero_embedded, representation_apply]
      change v ((g.val).symm i) =
        extendZero v ((m11ToM12ExtendHom g)⁻¹ (m11M12PointEmbedding i))
      rw [← map_inv, m11ToM12ExtendHom_apply_embedded, extendZero_embedded]
      rfl

/-- The binary augmentation action on the actual eleven points of M₁₁. -/
@[expose] noncomputable def augmentationRepresentation : Representation (ZMod 2) M11 (core (Fin 11)) :=
  (coreRepresentation (Fin 11)).comp M11.subtype

/-- Zero extension followed by the actual twelve-point quotient map. -/
private noncomputable def augmentationToPoint :
    Representation.IntertwiningMap augmentationRepresentation pointRepresentation where
  toLinearMap :=
    ((constants (Fin 12)).mkQ.comp (extendZero.comp (core (Fin 11)).subtype)).codRestrict
      (natural (Fin 12)) (fun v => ⟨extendZero v.val, by
        change augmentation (Fin 12) (extendZero v.val) = 0
        rw [augmentation_extendZero]
        exact v.property, rfl⟩)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (constants (Fin 12)).mkQ (extendZero (representation (Fin 11) g.val v.val)) =
      (constants (Fin 12)).mkQ
        (representation (Fin 12) (pointEmbedding g).val (extendZero v.val))
    rw [extendZero_equivariant]

private theorem augmentationToPoint_injective : Function.Injective augmentationToPoint := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro v hv
  have he : (constants (Fin 12)).mkQ (extendZero v.val) = 0 :=
    congrArg Subtype.val hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    ((Submodule.Quotient.mk_eq_zero (constants (Fin 12))).mp he)
  have hz : c = 0 := by
    have h := congrFun hc (12 : Fin 12)
    simpa only [Pi.smul_apply, allOne, smul_eq_mul, mul_one, extendZero_twelve] using h
  have hv0 : v = 0 := by
    apply Subtype.ext
    ext i
    change v.val i = 0
    have h := congrFun hc (m11M12PointEmbedding i)
    simpa only [hz, zero_smul, Pi.zero_apply, extendZero_embedded] using h.symm
  exact hv0

/-- The marked eleven-point augmentation module is the restricted M₁₂ heart. -/
noncomputable def augmentationEquivPoint :
    Representation.Equiv augmentationRepresentation pointRepresentation :=
  augmentationToPoint.ofBijective ⟨augmentationToPoint_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [finrank_core, finrank_m12Heart]; rfl)).mp augmentationToPoint_injective⟩

/-- Dimension of the degree-eleven augmentation module. -/
theorem finrank_augmentation : Module.finrank (ZMod 2) (core (Fin 11)) = 10 := by
  rw [finrank_core]; rfl

/-- The actual M₁₁ action on the augmentation module is faithful. -/
theorem augmentationRepresentation_injective : Function.Injective augmentationRepresentation := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  change g = 1
  have hc (v : core (Fin 11)) : coreRepresentation (Fin 11) g.val v = v := by
    exact DFunLike.congr_fun hg v
  have hf (v : Full (Fin 11)) : representation (Fin 11) g.val v = v := by
    let w := v - augmentation (Fin 11) v • allOne (Fin 11)
    have hw : w ∈ core (Fin 11) := by
      change augmentation (Fin 11) w = 0
      have hodd : Odd (Fintype.card (Fin 11)) := by decide
      simp only [w, map_sub, map_smul, augmentation_allOne,
        hodd.natCast_zmod_two, smul_eq_mul, mul_one, sub_self]
    have he := congrArg Subtype.val (hc ⟨w, hw⟩)
    change representation (Fin 11) g.val w = w at he
    simpa only [w, map_sub, map_smul, permute_allOne, sub_left_inj] using he
  apply Subtype.ext
  apply _root_.Equiv.ext
  intro i
  have hi := congrFun (hf (Pi.single i 1)) (g.val i)
  simpa [Pi.single_apply] using hi.symm

/-- The reference restriction in the M₁₂ assembly is faithful, with its
literal M₁₁ marking. -/
theorem pointRepresentation_injective : Function.Injective pointRepresentation := by
  intro g h hgh
  apply augmentationRepresentation_injective
  apply LinearMap.ext
  intro v
  apply augmentationEquivPoint.injective
  exact (LinearMap.congr_fun (augmentationEquivPoint.isIntertwining' g) v).trans
    ((congrArg (fun f : Module.End (ZMod 2) M12Heart => f (augmentationEquivPoint v)) hgh).trans
      (LinearMap.congr_fun (augmentationEquivPoint.isIntertwining' h) v).symm)

/-- The actual point restriction is irreducible by its faithful order-eleven actor. -/
theorem pointRepresentation_isIrreducible : pointRepresentation.IsIrreducible :=
  irreducible_of_eleven_dvd pointRepresentation pointRepresentation_injective
    finrank_m12Heart.le (by rw [m11_order]; norm_num)

end Representation.MathieuSmall.M12Recognition.PointClassification
