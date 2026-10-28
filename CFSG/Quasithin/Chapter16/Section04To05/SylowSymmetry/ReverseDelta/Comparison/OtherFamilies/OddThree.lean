module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Excluding PSL₃(3) in the reverse residual comparison

The inner fixed subgroup is GL₂(3), whereas the permitted outer table gives
S₄ and hence the outer two-residual A₄. The determinant of every element of
O²(GL₂(3)) is one, since the field units form a two-group. The only nonidentity
determinant-one involution in dimension two is −I. Two distinct double
transpositions in A₄ therefore rule out an embedding in the inner residual.

The source component has trivial center. We use this to identify both actual
residuals faithfully with their images in the same quotient L/Z(L), and map
the containment from `Contrary.residual_normal` into that quotient. Containment
already gives the contradiction; the accompanying relative normality requires
no strengthening. The sole additional input is the earlier outer S₄ table row.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(1), printed p.1171, and the comparison in the proof of 16.4.11(2),
printed p.1193.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
open Subgroup Theory.GroupTheory
private abbrev GLThree := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)

private theorem det_eq_one (x : GLThree) (hx : x ∈ pResidual 2 GLThree) :
    Matrix.GeneralLinearGroup.det x = 1 := by
  have hu : IsPGroup 2 (ZMod 3)ˣ := IsPGroup.of_card (n := 1) (by
    norm_num [Nat.card_eq_fintype_card, ZMod.card_units,
      Nat.totient_prime Nat.prime_three])
  have hb : pResidual 2 (ZMod 3)ˣ = ⊥ :=
    le_bot_iff.mp (sInf_le ⟨inferInstance, hu.to_quotient ⊥⟩)
  have hm := map_pResidual_le 2 Matrix.GeneralLinearGroup.det
    (mem_map.mpr ⟨x, hx, rfl⟩)
  rwa [hb, mem_bot] at hm

private theorem residual_involution_unique (x y : pResidual 2 GLThree)
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  have scalar (a : pResidual 2 GLThree) (ha : orderOf a = 2) : (a : GLThree) = -1 := by
    apply (Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
      (by decide : (2 : ZMod 3) ≠ 0) (a : GLThree) ?_ (det_eq_one a a.property)).resolve_left
    · intro h
      have he : a = 1 := Subtype.ext h
      simp [he] at ha
    · exact congrArg Subtype.val (ha ▸ pow_orderOf_eq_one a)
  exact Subtype.ext ((scalar x hx).trans (scalar y hy).symm)

private theorem not_a4_residual_embedding
    (f : alternatingGroup (Fin 4) →* pResidual 2 GLThree) (hf : Function.Injective f) : False := by
  let x : alternatingGroup (Fin 4) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  let y : alternatingGroup (Fin 4) :=
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  have hx : orderOf x = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hy : orderOf y = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hxy : x ≠ y := by decide +kernel
  exact hxy (hf (residual_involution_unique (f x) (f y)
    ((orderOf_injective f hf x).trans hx) ((orderOf_injective f hf y).trans hy)))

/-- Transport the actual embedded residual through a full fixed-subgroup
identification. The first isomorphism reverses the faithful subtype image. -/
private noncomputable def residualModelEquiv {G H : Type*} [Group G] [Group H]
    {L : Subgroup G} {t : G} (ht : t ∈ normalizer (L : Set G))
    (e : (action ht).fixedSubgroup ≃* H) : residual L t ≃* pResidual 2 H :=
  ((pResidual 2 (L ⊓ centralizer ({t} : Set G) : Subgroup G)).equivMapOfInjective
    _ (Subgroup.subtype_injective _)).symm.trans
    (((fixedCentralizerEquiv ht).symm.trans e).subgroupMap _ |>.trans
      (MulEquiv.subgroupCongr (map_pResidual 2 ((fixedCentralizerEquiv ht).symm.trans e))))

/-- The PSL₃(3) branch of the residual comparison, conditional only on the
outer fixed-subgroup row of 16.1.5(1). The inner row and residual obstruction
are proved, and all residuals are transported through actual isomorphisms. -/
theorem not_pslThree_of_outer_table {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (d : Contrary T z L g R r) (hL : ClassicalGroup.IsPSL L 3 3)
    (table : ∀ a : MulAut Matrix.PSL3Three.PSL, orderOf a = 2 →
      (¬ ∃ x, a = MulAut.conj x) → Nonempty (a.fixedSubgroup ≃* Equiv.Perm (Fin 4))) :
    False := by
  let hi := d.setup.sylow_normalizes (d.setup.le_sylow d.mem)
  obtain ⟨ei⟩ := OtherPreliminaries.pslThree_inner_involution hL (action hi)
    d.inner_action_order d.inner_action
  have hZ := OtherPreliminaries.pslThree_center_eq_bot hL
  let eri := (centralImageEquiv ((residual_le L r).trans inf_le_left) hZ).symm.trans
    (residualModelEquiv hi ei)
  obtain ⟨e⟩ := OtherPreliminaries.equiv_pslThree_of_isPSL hL
  let ec : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  let eM := ec.symm.trans e
  let b := MulAut.congr eM (action d.z_normalizes)
  have hb : orderOf b = 2 :=
    ((MulAut.congr eM).orderOf_eq _).trans d.outer_action_order
  have hob : ¬ ∃ x, b = MulAut.conj x := fun h =>
    d.outer_action ((MulAut.congr_inner_iff eM _).mp h)
  obtain ⟨eo⟩ := table b hb hob
  let ero := (centralImageEquiv d.placement hZ).symm.trans
    ((residualModelEquiv d.z_normalizes
      ((MulAut.fixedSubgroupCongr eM _).trans eo)).trans
      (MulEquiv.subgroupCongr (Equiv.Perm.twoResidual_eq_alternating (Fin 4))))
  have hle : centralImage L (residual (L.conjBy g) z) ≤ centralImage L (residual L r) :=
    map_mono (subgroupOf_mono L d.residual_normal.1)
  let f := eri.toMonoidHom.comp
    ((inclusion hle).comp ero.symm.toMonoidHom)
  exact not_a4_residual_embedding f
    (eri.injective.comp ((inclusion_injective hle).comp ero.symm.injective))

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
