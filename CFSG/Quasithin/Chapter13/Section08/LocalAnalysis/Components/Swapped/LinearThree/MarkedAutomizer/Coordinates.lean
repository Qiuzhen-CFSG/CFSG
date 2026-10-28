module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.CubicOrders
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.ScalarMovement

/-!
# Coordinates for the actual marked automizer

The multiplication map of L₀/O₂(L₀) and L₁,₊/O₂(L₁,₊) gives coordinates
on the literal L₁/O₂(L₁). Both source marks are identified with the
intrinsic center and derived images in the cover parabolic. Its intrinsic
normalizer calculation therefore makes every element of N_M(L₁) preserve
both coordinate axes. The proved source inverter in T∩L fixes the first
axis and inverts the second.

The earlier factorization 13.2.2(3) is explicit; the cubic orders are
supplied by `CubicOrders` in the final assembly. Here `one L T V₁` is the
literal O²(N_{LT}(V₁)), definitionally equal to `markedResidual L T V₁`.

Source: Aschbacher–Smith, Notation 13.2.1 and Lemma 13.2.2, pp.877–878;
13.8.16(1), printed p.952 (PDF p.969).
-/

@[expose] public section
open Subgroup Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalAction
namespace Coordinates
variable {G : Type*} [Group G] [Finite G]
variable (L T V₁ : Subgroup G)
    (hn : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hf : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hz : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hx : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)

noncomputable def zeroEquiv : (zero L ⧸ pCore 2 (zero L)) ≃* Model.C3 :=
  mulEquivOfPrimeCardEq hz (by simp [Model.C3])
noncomputable def plusEquiv : (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) ≃* Model.C3 :=
  mulEquivOfPrimeCardEq hx (by simp [Model.C3])

/-- Cubic coordinates on the literal quotient, obtained by multiplying the two source marks. -/
noncomputable def equiv : (one L T V₁ ⧸ pCore 2 (one L T V₁)) ≃*
    Model.CubicPlane :=
  (markedProductEquiv L T V₁ hn hTV hf hx).symm.trans
    ((zeroEquiv L hz).prodCongr (plusEquiv L T V₁ hx))

theorem equiv_zero (z : zero L ⧸ pCore 2 (zero L)) :
    equiv L T V₁ hn hTV hf hz hx (zeroCoreMap L T V₁ hn hf z) = (zeroEquiv L hz z, 1) := by
  have he := markedProductEquiv_apply L T V₁ hn hTV hf hx z 1
  rw [map_one, mul_one] at he
  rw [← he]
  dsimp only [equiv, MulEquiv.trans_apply]
  rw [MulEquiv.symm_apply_apply]
  change (zeroEquiv L hz _, plusEquiv L T V₁ hx _) = _
  rw [map_one]

theorem equiv_plus (z : plus L T V₁ ⧸ pCore 2 (plus L T V₁)) :
    equiv L T V₁ hn hTV hf hz hx (plusCoreMap L T V₁ hTV z) = (1, plusEquiv L T V₁ hx z) := by
  have he := markedProductEquiv_apply L T V₁ hn hTV hf hx 1 z
  rw [map_one, one_mul] at he
  rw [← he]
  dsimp only [equiv, MulEquiv.trans_apply]
  rw [MulEquiv.symm_apply_apply]
  change (zeroEquiv L hz _, plusEquiv L T V₁ hx _) = _
  rw [map_one]

theorem zero_axis : (zeroCoreMap L T V₁ hn hf).range.map
    (equiv L T V₁ hn hTV hf hz hx).toMonoidHom = Model.scalarAxis := by
  ext q
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    change equiv L T V₁ hn hTV hf hz hx _ ∈ Model.scalarAxis
    rw [equiv_zero]
    exact ⟨mem_top _, rfl⟩
  · intro hq
    have hq2 : q.2 = 1 := hq.2
    obtain ⟨z, he⟩ := (zeroEquiv L hz).surjective q.1
    refine ⟨zeroCoreMap L T V₁ hn hf z, ⟨z, rfl⟩, ?_⟩
    change equiv L T V₁ hn hTV hf hz hx _ = q
    rw [equiv_zero, he, ← hq2]

theorem plus_axis : (plusCoreMap L T V₁ hTV).range.map
    (equiv L T V₁ hn hTV hf hz hx).toMonoidHom = Model.derivedAxis := by
  ext q
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    change equiv L T V₁ hn hTV hf hz hx _ ∈ Model.derivedAxis
    rw [equiv_plus]
    exact ⟨rfl, mem_top _⟩
  · intro hq
    have hq1 : q.1 = 1 := hq.1
    obtain ⟨z, he⟩ := (plusEquiv L T V₁ hx).surjective q.2
    refine ⟨plusCoreMap L T V₁ hTV z, ⟨z, rfl⟩, ?_⟩
    change equiv L T V₁ hn hTV hf hz hx _ = q
    rw [equiv_plus, he, ← hq1]

private theorem map_congr_invariant {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : MulAut A) (S : Subgroup A)
    (hS : S.map a.toMonoidHom = S) :
    (S.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom = S.map e.toMonoidHom := by
  have he : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp a.toMonoidHom := by
    ext x
    exact congrArg e (congrArg a (e.symm_apply_apply x))
  rw [map_map, he, ← map_map, hS]

/-- Both axes are invariant under the actual N_M(R) action, by the intrinsic
normalizer and the proved source-to-model marks. -/
theorem axes_preserved (V M : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : CoverPointModel L V hLV)
    (hML : M ≤ normalizer (L : Set G))
    (S : Sylow 2 (L ⊔ T : Subgroup G))
    (hS : (S : Subgroup (L ⊔ T : Subgroup G)) = T.subgroupOf (L ⊔ T))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) :
    (∀ m, Model.scalarAxis.map
      (coordinateAction (one L T V₁) M (equiv L T V₁ hn hTV hf hz hx) m).toMonoidHom =
        Model.scalarAxis) ∧
    (∀ m, Model.derivedAxis.map
      (coordinateAction (one L T V₁) M (equiv L T V₁ hn hTV hf hz hx) m).toMonoidHom =
        Model.derivedAxis) := by
  obtain ⟨x, hr, _, _, hzero, hplus⟩ :=
    d.exists_marked_section_with_marks T V₁ hn S hS hTV hV₁V hc
  have hRL : one L T V₁ ≤ L :=
    markedResidual_le_left L T V₁ (CoverPointModel.source_isPGroup T S hS) hn
  have hr' : (d.subgroupMap (one L T V₁) hRL).range = Model.residual x := hr
  let es : (one L T V₁ ⧸ pCore 2 (one L T V₁)) ≃* Model.Section x :=
    d.sectionEquiv (one L T V₁) hRL x hr'
  have hzmark : (zeroCoreMap L T V₁ hn hf).range.map es.toMonoidHom = Model.scalarLine x := by
    rw [zeroCoreMap, localCoreMap_range]
    exact hzero
  have hxmark : (plusCoreMap L T V₁ hTV).range.map es.toMonoidHom = Model.derivedLine x := by
    rw [plusCoreMap, localCoreMap_range]
    exact hplus
  have hact (m : (M ⊓ normalizer (one L T V₁ : Set G) : Subgroup G)) :
      MulAut.congr es (automizerAction (one L T V₁) M m) =
        Model.sectionAut x (coverAction d M hML (inclusion inf_le_left m))
          (d.coverAction_preserves_residual (one L T V₁) M hRL hML x hr' m) := by
    ext q
    change es (automizerAction _ M m (es.symm q)) = _
    rw [d.sectionEquiv_intertwines, MulEquiv.apply_symm_apply]
  have hp (A : Subgroup (one L T V₁ ⧸ pCore 2 (one L T V₁)))
      (m : (M ⊓ normalizer (one L T V₁ : Set G) : Subgroup G))
      (ha : (A.map es.toMonoidHom).map
        (MulAut.congr es (automizerAction _ M m)).toMonoidHom = A.map es.toMonoidHom) :
      A.map (automizerAction _ M m).toMonoidHom = A := by
    apply map_injective (f := es.toMonoidHom) es.injective
    rw [map_map]
    have he : es.toMonoidHom.comp (automizerAction _ M m).toMonoidHom =
        (MulAut.congr es (automizerAction _ M m)).toMonoidHom.comp es.toMonoidHom := by
      ext q
      change es (automizerAction _ M m q) = es (automizerAction _ M m (es.symm (es q)))
      rw [MulEquiv.symm_apply_apply]
    rw [he, ← map_map]
    exact ha
  constructor
  · intro m
    rw [← zero_axis L T V₁ hn hTV hf hz hx]
    apply map_congr_invariant
    apply hp
    rw [hzmark, hact]
    exact Model.sectionAut_scalarLine _ _ _
  · intro m
    rw [← plus_axis L T V₁ hn hTV hf hz hx]
    apply map_congr_invariant
    apply hp
    rw [hxmark, hact]
    exact Model.sectionAut_preserves_derivedLine _ _ _

/-- The source inverter acts as the second-coordinate sign change. -/
theorem derivedFlip_mem (M : Subgroup G) (hTM : T ≤ M) :
    Diagonal.diagonalAction Diagonal.derivedFlip ∈
      (coordinateAction (one L T V₁) M (equiv L T V₁ hn hTV hf hz hx)).range := by
  obtain ⟨t, ht, _⟩ := exists_plus_inverter L T V₁ hn hTV hf hx
  let m : (M ⊓ normalizer (one L T V₁ : Set G) : Subgroup G) :=
    ⟨t.val, hTM t.property.1, T_normalizes_one L T V₁ hTV t.property.1⟩
  let e := equiv L T V₁ hn hTV hf hz hx
  let a := coordinateAction (one L T V₁) M e m
  have hzero (z : zero L ⧸ pCore 2 (zero L)) :
      a (zeroEquiv L hz z, 1) = (zeroEquiv L hz z, 1) := by
    rw [← equiv_zero L T V₁ hn hTV hf hz hx]
    change e (automizerAction _ M m (e.symm (e _))) = e _
    rw [MulEquiv.symm_apply_apply]
    have he := zeroCoreMap_fixed L T V₁ hn hTV hf t z
    exact congrArg e he
  have hplus (z : plus L T V₁ ⧸ pCore 2 (plus L T V₁)) :
      a (1, plusEquiv L T V₁ hx z) = (1, (plusEquiv L T V₁ hx z)⁻¹) := by
    rw [← equiv_plus L T V₁ hn hTV hf hz hx]
    change e (automizerAction _ M m (e.symm (e _))) = _
    rw [MulEquiv.symm_apply_apply]
    have he := localCoreMap_equivariant (one L T V₁) (plus L T V₁)
      (plus_le_one L T V₁ hTV) (one_normalizes_plus L T V₁) t.val
      (T_normalizes_plus L T V₁ hn hTV t.property.1)
      (T_normalizes_one L T V₁ hTV t.property.1) z
    rw [ht] at he
    change plusCoreMap L T V₁ hTV z⁻¹ = automizerAction _ M m (plusCoreMap L T V₁ hTV z) at he
    rw [← he, equiv_plus, map_inv]
  refine ⟨m, ?_⟩
  apply MulEquiv.ext
  intro q
  obtain ⟨z, hz'⟩ := (zeroEquiv L hz).surjective q.1
  obtain ⟨x, hx'⟩ := (plusEquiv L T V₁ hx).surjective q.2
  have he := a.map_mul (q.1, 1) (1, q.2)
  change a q = (q.1, q.2⁻¹)
  conv_lhs => rw [← Prod.eta q]
  simpa only [Prod.mk_mul_mk, mul_one, one_mul, ← hz', ← hx', hzero, hplus] using he

end Coordinates
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer
end
