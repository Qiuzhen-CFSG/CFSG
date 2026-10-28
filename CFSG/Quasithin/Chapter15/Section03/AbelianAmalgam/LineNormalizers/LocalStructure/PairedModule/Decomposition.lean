module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.Decomposition.Relations
public import Theory.Representation.BinaryInvolutionPairing

/-!
# The equivariant paired decomposition of the original line section

The images of `C_U(τ)` and `C_U(τ^y)` are complementary in `U/E`.
Right conjugation by `y` identifies the first with the second. In the
resulting coordinates `x = w₁ + y⁻¹ w₂`, the actual centralizer-image factor
acts diagonally. Its action on the first summand defines `sigma` through
the second marked quotient coordinate; the first S₃ factor acts trivially
in this representation. Composing the coordinates with the original section
projection is surjective and has precisely the line subspace as kernel.

This is conditional on the published `ActionData`, whose construction belongs
to the source assembly. It asserts no interchange of both summands by `y`.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1153,
PDF p.1170, proof of 15.3.67 before the temporary replacement.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
open Descent.QuotientIdentification
variable {G : Type*} [Group G]
variable (V E : Subgroup G) [IsElementaryAbelian 2 (lineV V E)]
variable {Y T : Subgroup G} (d : MarkedDecomposition Y T E)
variable (hcomm : ⁅lineV V E, lineQ E⁆ ≤ E) (a : ActionData V E d)

/-- The explicit binary coordinates in two copies of the first fixed image. -/
noncomputable def pairedEquiv :
    SectionSpace V E ≃ₗ[ZMod 2] fixedImage V E d.tau × fixedImage V E d.tau :=
  Representation.BinaryInvolutionPairing.equiv _ _ _
    (mem_first_fixedImage V E d a) (tau_action_square V E d hcomm a)
    (tau_rightConjugation_relation V E d hcomm a)

/-- The inverse uses right conjugation by the original selected element. -/
lemma pairedEquiv_symm_apply (w : fixedImage V E d.tau × fixedImage V E d.tau) :
    (pairedEquiv V E d hcomm a).symm w =
      (w.1 : SectionSpace V E) + sectionRepresentation V E a.y⁻¹ w.2 := rfl

include hcomm a in
/-- The two images span the whole original section. -/
lemma fixedImages_sup :
    fixedImage V E d.tau ⊔ fixedImage V E ((a.y : G)⁻¹ * d.tau * a.y) = ⊤ := by
  rw [← fixedImage_rightConjugate]
  exact Representation.BinaryInvolutionPairing.sup_map_eq_top _ _ _
    (mem_first_fixedImage V E d a) (tau_action_square V E d hcomm a)
    (tau_rightConjugation_relation V E d hcomm a)

include hcomm in
/-- The two images have trivial intersection. -/
lemma fixedImages_inf :
    fixedImage V E d.tau ⊓ fixedImage V E ((a.y : G)⁻¹ * d.tau * a.y) = ⊥ := by
  rw [← fixedImage_rightConjugate]
  exact Representation.BinaryInvolutionPairing.inf_map_eq_bot _ _ _
    (mem_first_fixedImage V E d a) (tau_rightConjugation_relation V E d hcomm a)

/-- Right conjugation as an actual linear automorphism of the section. -/
noncomputable def sectionRightConjugation (y : lineNormalizer E) :
    SectionSpace V E ≃ₗ[ZMod 2] SectionSpace V E :=
  LinearEquiv.ofLinearMap (sectionRepresentation V E y⁻¹) (sectionRepresentation V E y)
    (by ext x; simp only [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply, LinearMap.id_apply])
    (by ext x; simp only [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply, LinearMap.id_apply])

/-- The fixed-image equivalence induced by right conjugation. -/
noncomputable def fixedImageEquiv :
    fixedImage V E d.tau ≃ₗ[ZMod 2] fixedImage V E ((a.y : G)⁻¹ * d.tau * a.y) :=
  ((sectionRightConjugation V E a.y).submoduleMap (fixedImage V E d.tau)).trans
    (LinearEquiv.ofEq _ _ (fixedImage_rightConjugate V E a.y d.tau))

lemma fixedImageEquiv_apply (w : fixedImage V E d.tau) :
    (fixedImageEquiv V E d a w : SectionSpace V E) =
      sectionRepresentation V E a.y⁻¹ w := rfl

include a in
lemma secondFactor_preserves_first (c : centralizerImage E)
    (x : SectionSpace V E) (hx : x ∈ fixedImage V E d.tau) :
    markedRepresentation V E d hcomm (1, c) x ∈ fixedImage V E d.tau := by
  rw [mem_first_fixedImage V E d a]
  rw [first_action_commutes_second V E d hcomm _ (marked_tau_second E d),
    (mem_first_fixedImage V E d a x).mp hx]

lemma secondFactor_preserves_second (c : centralizerImage E)
    (x : SectionSpace V E) (hx : x ∈ fixedImage V E ((a.y : G)⁻¹ * d.tau * a.y)) :
    markedRepresentation V E d hcomm (1, c) x ∈
      fixedImage V E ((a.y : G)⁻¹ * d.tau * a.y) := by
  rw [← fixedImage_rightConjugate] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨markedRepresentation V E d hcomm (1, c) z,
    secondFactor_preserves_first V E d hcomm a c z hz, ?_⟩
  exact first_action_commutes_second V E d hcomm a.y⁻¹
    (by simp only [map_inv, Prod.snd_inv, a.y_second, inv_one]) c z

/-- The actual centralizer-image factor preserves the first summand. -/
noncomputable def firstSubrepresentation :
    Subrepresentation ((markedRepresentation V E d hcomm).comp
      (MonoidHom.inr (Equiv.Perm (Fin 3)) (centralizerImage E))) where
  toSubmodule := fixedImage V E d.tau
  apply_mem_toSubmodule c := secondFactor_preserves_first V E d hcomm a c

/-- The first-summand action, extended through the second quotient coordinate. -/
noncomputable def sigma :
    Representation (ZMod 2) (lineNormalizer E ⧸ pCore 2 (lineNormalizer E))
      (fixedImage V E d.tau) :=
  (firstSubrepresentation V E d hcomm a).toRepresentation.comp
    ((MonoidHom.snd _ _).comp d.equiv.toMonoidHom)

lemma sigma_apply (q : lineNormalizer E ⧸ pCore 2 (lineNormalizer E))
    (w : fixedImage V E d.tau) :
    (sigma V E d hcomm a q w : SectionSpace V E) =
      markedRepresentation V E d hcomm (1, (d.equiv q).2) w := rfl

/-- Every element of the first marked factor acts trivially in `sigma`. -/
lemma sigma_first_factor (r : Equiv.Perm (Fin 3)) :
    sigma V E d hcomm a (d.equiv.symm (r, 1)) = 1 := by
  change (firstSubrepresentation V E d hcomm a).toRepresentation
    (d.equiv (d.equiv.symm (r, 1))).2 = 1
  rw [MulEquiv.apply_symm_apply]
  exact map_one _

lemma sigma_centralizer (c : centralizer (E : Set G)) (w : fixedImage V E d.tau) :
    (sigma V E d hcomm a (quotientMap E
      (inclusion (centralizer_le_normalizer (E : Set G)) c)) w : SectionSpace V E) =
      sectionRepresentation V E (inclusion (centralizer_le_normalizer (E : Set G)) c) w := by
  have hc : d.equiv (quotientMap E
      (inclusion (centralizer_le_normalizer (E : Set G)) c)) =
      (1, centralizerImageMap E c) := d.centralizer_factor c
  rw [sigma_apply, hc]
  exact congrArg (fun F : Module.End (ZMod 2) (SectionSpace V E) => F w)
    (markedRepresentation_centralizer V E d hcomm c)

lemma pairedEquiv_secondFactor (c : centralizerImage E) (x : SectionSpace V E) :
    pairedEquiv V E d hcomm a (markedRepresentation V E d hcomm (1, c) x) =
      ((firstSubrepresentation V E d hcomm a).toRepresentation c
        (pairedEquiv V E d hcomm a x).1,
       (firstSubrepresentation V E d hcomm a).toRepresentation c
        (pairedEquiv V E d hcomm a x).2) :=
  Representation.BinaryInvolutionPairing.equiv_equivariant _ _ _
    (mem_first_fixedImage V E d a) (tau_action_square V E d hcomm a)
    (tau_rightConjugation_relation V E d hcomm a) _
    (secondFactor_preserves_first V E d hcomm a c)
    (first_action_commutes_second V E d hcomm _ (marked_tau_second E d) c)
    (first_action_commutes_second V E d hcomm a.y⁻¹
      (by simp only [map_inv, Prod.snd_inv, a.y_second, inv_one]) c) x

/-- The original centralizer acts diagonally in the paired coordinates. -/
lemma pairedEquiv_centralizer (c : centralizer (E : Set G)) (x : SectionSpace V E) :
    pairedEquiv V E d hcomm a
      (sectionRepresentation V E (inclusion (centralizer_le_normalizer (E : Set G)) c) x) =
      (sigma V E d hcomm a (quotientMap E
        (inclusion (centralizer_le_normalizer (E : Set G)) c)) (pairedEquiv V E d hcomm a x).1,
       sigma V E d hcomm a (quotientMap E
        (inclusion (centralizer_le_normalizer (E : Set G)) c)) (pairedEquiv V E d hcomm a x).2) := by
  rw [← markedRepresentation_centralizer V E d hcomm c, pairedEquiv_secondFactor]
  have hc : d.equiv (quotientMap E
      (inclusion (centralizer_le_normalizer (E : Set G)) c)) =
      (1, centralizerImageMap E c) := d.centralizer_factor c
  have hs : sigma V E d hcomm a (quotientMap E
      (inclusion (centralizer_le_normalizer (E : Set G)) c)) =
      (firstSubrepresentation V E d hcomm a).toRepresentation (centralizerImageMap E c) := by
    change (firstSubrepresentation V E d hcomm a).toRepresentation
      (d.equiv (quotientMap E (inclusion (centralizer_le_normalizer (E : Set G)) c))).2 = _
    rw [hc]
  rw [hs]
  rfl

/-- The paired projection from the original elementary abelian group. -/
noncomputable def pairedProjection :
    Additive (lineV V E) →ₗ[ZMod 2] fixedImage V E d.tau × fixedImage V E d.tau :=
  (pairedEquiv V E d hcomm a).toLinearMap.comp (sectionProjection V E)

lemma pairedProjection_surjective : Function.Surjective (pairedProjection V E d hcomm a) :=
  (pairedEquiv V E d hcomm a).surjective.comp (sectionProjection_surjective V E)

/-- The paired projection kills exactly the original line. -/
lemma pairedProjection_ker : (pairedProjection V E d hcomm a).ker = lineSubspace V E := by
  rw [pairedProjection, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot,
    sectionProjection_ker]

lemma pairedProjection_centralizer (c : centralizer (E : Set G)) (v : Additive (lineV V E)) :
    pairedProjection V E d hcomm a
      (spanRepresentation V E (inclusion (centralizer_le_normalizer (E : Set G)) c) v) =
      (sigma V E d hcomm a (quotientMap E
        (inclusion (centralizer_le_normalizer (E : Set G)) c)) (pairedProjection V E d hcomm a v).1,
       sigma V E d hcomm a (quotientMap E
        (inclusion (centralizer_le_normalizer (E : Set G)) c)) (pairedProjection V E d hcomm a v).2) :=
  pairedEquiv_centralizer V E d hcomm a c (sectionProjection V E v)

lemma fixedImages_secondFactor_invariant (c : centralizerImage E) :
    (fixedImage V E d.tau).map (markedRepresentation V E d hcomm (1, c)) =
        fixedImage V E d.tau ∧
    (fixedImage V E ((a.y : G)⁻¹ * d.tau * a.y)).map
        (markedRepresentation V E d hcomm (1, c)) =
      fixedImage V E ((a.y : G)⁻¹ * d.tau * a.y) := by
  have step (W : Submodule (ZMod 2) (SectionSpace V E))
      (hw : ∀ b : centralizerImage E, ∀ x ∈ W,
        markedRepresentation V E d hcomm (1, b) x ∈ W) :
      W.map (markedRepresentation V E d hcomm (1, c)) = W := by
    apply le_antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact hw c z hz
    · intro x hx
      refine ⟨markedRepresentation V E d hcomm (1, c⁻¹) x, hw c⁻¹ x hx, ?_⟩
      rw [← Module.End.mul_apply, ← map_mul]
      change markedRepresentation V E d hcomm ((1, c) * (1, c)⁻¹) x = x
      rw [mul_inv_cancel, map_one, Module.End.one_apply]
  exact ⟨step _ (secondFactor_preserves_first V E d hcomm a),
    step _ (secondFactor_preserves_second V E d hcomm a)⟩

include hcomm in
/-- Both summands are invariant under the actual centralizer. -/
lemma fixedImages_centralizer_invariant (c : centralizer (E : Set G)) :
    (fixedImage V E d.tau).map
        (sectionRepresentation V E (inclusion (centralizer_le_normalizer (E : Set G)) c)) =
      fixedImage V E d.tau ∧
    (fixedImage V E ((a.y : G)⁻¹ * d.tau * a.y)).map
        (sectionRepresentation V E (inclusion (centralizer_le_normalizer (E : Set G)) c)) =
      fixedImage V E ((a.y : G)⁻¹ * d.tau * a.y) := by
  rw [← markedRepresentation_centralizer V E d hcomm c]
  exact fixedImages_secondFactor_invariant V E d hcomm a (centralizerImageMap E c)

/-- The right-conjugation identification intertwines the centralizer actions. -/
lemma fixedImageEquiv_centralizer (c : centralizer (E : Set G))
    (w : fixedImage V E d.tau) :
    (fixedImageEquiv V E d a
      (sigma V E d hcomm a (quotientMap E
        (inclusion (centralizer_le_normalizer (E : Set G)) c)) w) : SectionSpace V E) =
      sectionRepresentation V E (inclusion (centralizer_le_normalizer (E : Set G)) c)
        (fixedImageEquiv V E d a w : SectionSpace V E) := by
  rw [fixedImageEquiv_apply, sigma_centralizer, fixedImageEquiv_apply,
    ← markedRepresentation_centralizer V E d hcomm c]
  exact first_action_commutes_second V E d hcomm a.y⁻¹
    (by simp only [map_inv, Prod.snd_inv, a.y_second, inv_one]) _ _

/-- In ambient group terms, a vector is killed exactly when it belongs to `E`. -/
lemma pairedProjection_eq_zero_iff (v : Additive (lineV V E)) :
    pairedProjection V E d hcomm a v = 0 ↔ (v.toMul : G) ∈ E := by
  rw [← LinearMap.mem_ker, pairedProjection_ker]
  rfl

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
