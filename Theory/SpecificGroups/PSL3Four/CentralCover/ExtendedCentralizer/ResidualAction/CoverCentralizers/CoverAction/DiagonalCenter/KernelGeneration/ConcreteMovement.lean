module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.KernelGeneration.DiagonalWords
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
/-!
# A diagonal lift moves a square class of the actual exceptional kernel

Project the concrete universal cover to its first permutation coordinate.
Quasisimplicity makes the projection kernel central, hence killed by the
projective matrix map. The checked diagonal words identify the second
coordinate over the diagonal-conjugated base map. Uniqueness for homomorphisms
from a perfect group through a central kernel then identifies this coordinate
with the first coordinate after any compatible lift. The central generator
trivial in the first coordinate has nonsquare image in the second.

This calculates the actual covering-kernel action needed in
Aschbacher--Smith 15.3.38, printed p.1136, using the exceptional cover of
I.1.3(6). No equivariant multiplier identification is assumed.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel.DiagonalWords
open Subgroup Theory.GroupTheory PerfectCentralCovering
open CentralWords

private def first : Group →* Equiv.Perm (Fin 224) :=
  (MonoidHom.fst _ _).comp ((MonoidHom.fst _ _).comp subgroup.subtype)
private def second : Group →* Equiv.Perm (Fin 224) :=
  (MonoidHom.snd _ _).comp ((MonoidHom.fst _ _).comp subgroup.subtype)

private theorem group_hom_ext {H : Type*} [_root_.Group H] (f g : Group →* H)
    (hx : f generatorX = g generatorX) (hy : f generatorY = g generatorY) : f = g := by
  apply MonoidHom.ext
  rintro ⟨t, ht⟩
  induction ht using Subgroup.closure_induction with
  | mem t ht =>
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact hx
    · have he : t = y := Set.mem_singleton_iff.mp ht
      subst t
      exact hy
  | one => exact (map_one f).trans (map_one g).symm
  | mul a b ha hb ihA ihB => exact (map_mul f _ _).trans ((congrArg₂ (· * ·) ihA ihB).trans (map_mul g _ _).symm)
  | inv a ha ih => exact (map_inv f _).trans ((congrArg Inv.inv ih).trans (map_inv g _).symm)

private theorem first_ker_le : first.ker ≤ projection.ker := by
  rcases IsQuasisimple.normal_le_center_or_eq_top first.ker with hc | ht
  · exact hc.trans (le_of_eq realization_ker_eq_center.symm)
  · have hx : first generatorX = 1 := (show generatorX ∈ first.ker by rw [ht]; trivial)
    have hne : first generatorX ≠ 1 := by
      intro h
      have h0 := Equiv.congr_fun h 0
      change x1 0 = 0 at h0
      revert h0
      decide +kernel
    exact (hne hx).elim

private theorem second_mem_first_range (g : Group) : second g ∈ first.range := by
  have hrX : second generatorX ∈ first.range :=
    ⟨wordX generatorX generatorY, by
      rw [map_wordX]
      exact wordX_perm⟩
  have hrY : second generatorY ∈ first.range :=
    ⟨wordY generatorX generatorY, by
      rw [map_wordY]
      exact wordY_perm⟩
  rcases g with ⟨t, ht⟩
  induction ht using Subgroup.closure_induction with
  | mem t ht =>
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact hrX
    · have he : t = y := Set.mem_singleton_iff.mp ht
      subst t
      exact hrY
  | one => exact (first.range.comap second).one_mem
  | mul a b ha hb ihA ihB => exact (first.range.comap second).mul_mem ihA ihB
  | inv a ha ih => exact (first.range.comap second).inv_mem ih

private def q1 : Group →* first.range := first.rangeRestrict
private def q2 : Group →* first.range := second.codRestrict _ second_mem_first_range
private theorem q1_surjective : Function.Surjective q1 := first.rangeRestrict_surjective
private theorem q1_ker_le : q1.ker ≤ projection.ker := by
  intro g hg
  apply first_ker_le
  exact congrArg Subtype.val hg

private noncomputable def baseProjection : first.range →* PSL3Four.PSL :=
  q1.liftOfSurjective q1_surjective ⟨projection, q1_ker_le⟩
private theorem baseProjection_q1 (g : Group) : baseProjection (q1 g) = projection g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

private theorem baseProjection_ker_le_center : baseProjection.ker ≤ center first.range := by
  intro v hv
  obtain ⟨g, rfl⟩ := q1_surjective v
  have hg : g ∈ projection.ker := by
    change baseProjection (q1 g) = 1 at hv
    rwa [baseProjection_q1] at hv
  apply mem_center_iff.mpr
  intro w
  obtain ⟨h, rfl⟩ := q1_surjective w
  exact (map_mul q1 h g).symm.trans ((congrArg q1
    (mem_center_iff.mp (realization.ker_le_center hg) h)).trans (map_mul q1 g h))

noncomputable def actor : MulAut PSL3Four.PSL :=
  (MulAut.congr (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv))
    (PSL3.OuterSolvable.linearConj F diagonal)

private theorem actor_projection (g : Group) : actor (projection g) =
    (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
      (QuotientGroup.mk (PSL3.OuterSolvable.linearConjSL F diagonal (matrixProjection g))) := by
  change (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
    ((PSL3.OuterSolvable.linearConj F diagonal)
      ((Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv).symm
        ((Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
          (QuotientGroup.mk (matrixProjection g))))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

private theorem baseProjection_q2 (g : Group) : baseProjection (q2 g) = actor (projection g) := by
  have he : baseProjection.comp q2 = actor.toMonoidHom.comp projection := by
    apply group_hom_ext
    · have hx : q2 generatorX = q1 (wordX generatorX generatorY) := by
        apply Subtype.ext
        exact wordX_perm.symm
      change baseProjection (q2 generatorX) = actor (projection generatorX)
      rw [hx, baseProjection_q1, actor_projection]
      change (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
        (QuotientGroup.mk (matrixProjection (wordX generatorX generatorY))) = _
      rw [map_wordX]
      change (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
        (QuotientGroup.mk (wordX matrixX matrixY)) = _
      rw [wordX_matrix]
      rfl
    · have hy : q2 generatorY = q1 (wordY generatorX generatorY) := by
        apply Subtype.ext
        exact wordY_perm.symm
      change baseProjection (q2 generatorY) = actor (projection generatorY)
      rw [hy, baseProjection_q1, actor_projection]
      change (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
        ((QuotientGroup.mk' (center SL)) (matrixProjection (wordY generatorX generatorY))) = _
      rw [map_wordY]
      change (Atlas.fieldEquivPSL 3 Representation.SL2FourNatural.fieldEquiv)
        ((QuotientGroup.mk' (center SL)) (wordY matrixX matrixY)) = _
      rw [wordY_matrix, map_mul, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff scalarZ).mpr scalarZ_central, one_mul]
      rfl
  exact DFunLike.congr_fun he g

private theorem first_lift (a : MulAut Group)
    (ha : ∀ g, projection (a g) = actor (projection g)) (g : Group) :
    first (a g) = second g := by
  have he : q1.comp a.toMonoidHom = q2 := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq baseProjection baseProjection_ker_le_center
    ext t
    exact (baseProjection_q1 (a t)).trans ((ha t).trans (baseProjection_q2 t).symm)
  exact congrArg Subtype.val (DFunLike.congr_fun he g)

/-- The distinguished central generator is moved modulo the squares of the
literal projection kernel by any compatible lift of the diagonal actor. -/
theorem moved_modulo_squares (a : MulAut Group)
    (ha : ∀ g, projection (a g) = actor (projection g)) :
    ¬ ∃ w : projection.ker, (w : Group) ^ 2 = a elementA * elementA⁻¹ := by
  rintro ⟨w, hw⟩
  obtain ⟨v, hv⟩ := (kernelEmbedding_bijective centralEmbedding
    projection_comp_centralEmbedding centralEmbedding_injective realization_card_le).surjective w
  have hv' : centralEmbedding v = w := congrArg Subtype.val hv
  have h := congrArg first hw
  rw [map_pow, map_mul, map_inv, first_lift a ha] at h
  have hA : first elementA = 1 := rfl
  have hB : second elementA = permB := rfl
  rw [hA, hB, inv_one, mul_one, ← hv'] at h
  change (centralEmbedding v).val.1.1 ^ 2 = permB at h
  rw [centralEmbedding_first] at h
  have hbad : ∀ b : ZMod 4, (permA ^ b.val) ^ 2 ≠ permB := by
    have hpoint : ∀ b : ZMod 4, ((permA ^ b.val) ^ 2) 0 ≠ permB 0 := by
      decide +kernel
    intro b he
    exact hpoint b (Equiv.congr_fun he 0)
  exact hbad v.1.2.toAdd h

/-- The unique compatible automorphism of the concrete universal cover. -/
noncomputable def liftedActor : MulAut Group := realization_isUniversal.liftMulAut actor

theorem liftedActor_compatible (g : Group) :
    projection (liftedActor g) = actor (projection g) :=
  congrArg (fun c : Covering Group PSL3Four.PSL => c g)
    (realization_isUniversal.liftMulAut_fac actor)

theorem liftedActor_moves_modulo_squares :
    ¬ ∃ w : projection.ker, (w : Group) ^ 2 = liftedActor elementA * elementA⁻¹ :=
  moved_modulo_squares liftedActor liftedActor_compatible

end Matrix.PSL3.ExceptionalFourCover.KernelModel.DiagonalWords
