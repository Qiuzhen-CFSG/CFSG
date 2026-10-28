module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.CentralizerGeometry
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry

/-!
# Exchange of the transvection's two endpoint parabolics

The proper-overgroup cover of a transvection centralizer makes its line and
hyperplane stabilizers maximal. An automorphism fixing the transvection
therefore permutes these two subgroups. If it fixed both, it would preserve
both conjugacy classes of endpoint stabilizers. Stabilizer rigidity and
transitivity on subspaces of equal dimension then preserve dimensions one and
three. Applying this also to the inverse automorphism excludes every witness
that changes dimension, since a nonzero proper subspace has dimension one,
two or three. Hence the automorphism exchanges the two endpoints.

The only additional input is the explicitly stated proper-overgroup cover;
all geometric premises are proved here or in the intrinsic geometry leaf.
This proves the exchange input of `FourIntersection.Reduction`, for the actual
Dynkin-action convention of `Binary.Geometry`. The cover itself remains the
responsibility of the source theorem's assembly.

Source: Aschbacher–Smith 2.3.9(7)(g), combined manuscript of 1 March 2004,
printed pp.525–526 of `refs/quasithin.pdf`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.FourIntersection
open Subgroup
variable {G : Type*} [Group G] {L : Subgroup G}

private theorem stabilizer_le_imp_eq (e : L ≃* PSL 4) {W U : Space 4}
    (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤)
    (h : subspaceStabilizer e W ≤ subspaceStabilizer e U) : W = U := by
  apply BinaryLinear.FourParabolicAction.parabolic_le_imp_eq hU0 hU1
  intro g hg
  obtain ⟨x, rfl⟩ := (linearModel e).surjective g
  exact h hg

private theorem stabilizer_ne_top (e : L ≃* PSL 4) {W : Space 4}
    (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) : subspaceStabilizer e W ≠ ⊤ := by
  intro ht
  apply BinaryLinear.FourParabolicAction.parabolic_ne_top hW0 hW1
  apply top_unique
  intro g _
  obtain ⟨x, rfl⟩ := (linearModel e).surjective g
  exact show x ∈ subspaceStabilizer e W from ht ▸ mem_top x

private theorem map_conjugate (α : MulAut L) (K : Subgroup L) (a : L) :
    (K.map (MulAut.conj a).toMonoidHom).map α.toMonoidHom =
      (K.map α.toMonoidHom).map (MulAut.conj (α a)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private theorem finrank_preserved_on_fixed_class (e : L ≃* PSL 4) (α : MulAut L)
    (B : Space 4) (hfix : (subspaceStabilizer e B).map α.toMonoidHom =
      subspaceStabilizer e B) {W W' : Space 4}
    (hd : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) B)
    (hW'0 : W' ≠ ⊥) (hW'1 : W' ≠ ⊤)
    (hmap : (subspaceStabilizer e W).map α.toMonoidHom = subspaceStabilizer e W') :
    Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) W' := by
  obtain ⟨g, hg⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_eq B W hd.symm
  let a := (linearModel e).symm g
  have ha : (subspaceStabilizer e B).map (MulAut.conj a).toMonoidHom =
      subspaceStabilizer e W := by
    rw [conjugate_subspaceStabilizer]
    simpa [a] using congrArg (subspaceStabilizer e) hg
  have hconj : (subspaceStabilizer e B).map (MulAut.conj (α a)).toMonoidHom =
      subspaceStabilizer e W' := by
    calc
      _ = ((subspaceStabilizer e B).map α.toMonoidHom).map
          (MulAut.conj (α a)).toMonoidHom := by rw [hfix]
      _ = ((subspaceStabilizer e B).map (MulAut.conj a).toMonoidHom).map
          α.toMonoidHom := (map_conjugate α _ a).symm
      _ = _ := by rw [ha, hmap]
  rw [conjugate_subspaceStabilizer] at hconj
  have heq := stabilizer_le_imp_eq e hW'0 hW'1 hconj.le
  calc
    Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) B := hd
    _ = Module.finrank (ZMod 2) (B.map (linearModel e (α a)).toLinearMap) :=
      (LinearEquiv.finrank_map_eq _ _).symm
    _ = Module.finrank (ZMod 2) W' := congrArg (fun U : Space 4 => Module.finrank (ZMod 2) U) heq

private theorem changed_dimension_is_two (e : L ≃* PSL 4) (α : MulAut L)
    (B₁ B₃ : Space 4) (hd₁ : Module.finrank (ZMod 2) B₁ = 1)
    (hd₃ : Module.finrank (ZMod 2) B₃ = 3)
    (hfix₁ : (subspaceStabilizer e B₁).map α.toMonoidHom = subspaceStabilizer e B₁)
    (hfix₃ : (subspaceStabilizer e B₃).map α.toMonoidHom = subspaceStabilizer e B₃)
    {W W' : Space 4} (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) (hW'0 : W' ≠ ⊥) (hW'1 : W' ≠ ⊤)
    (hd : Module.finrank (ZMod 2) W ≠ Module.finrank (ZMod 2) W')
    (hmap : (subspaceStabilizer e W).map α.toMonoidHom = subspaceStabilizer e W') :
    Module.finrank (ZMod 2) W = 2 := by
  have hne0 : Module.finrank (ZMod 2) W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hle : Module.finrank (ZMod 2) W ≤ 4 := by
    simpa only [Module.finrank_fin_fun] using Submodule.finrank_le W
  have hne4 : Module.finrank (ZMod 2) W ≠ 4 := by
    intro h
    apply hW1
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Module.finrank_fin_fun] using h
  have hne1 : Module.finrank (ZMod 2) W ≠ 1 := by
    intro h
    exact hd (finrank_preserved_on_fixed_class e α B₁ hfix₁ (h.trans hd₁.symm) hW'0 hW'1 hmap)
  have hne3 : Module.finrank (ZMod 2) W ≠ 3 := by
    intro h
    exact hd (finrank_preserved_on_fixed_class e α B₃ hfix₃ (h.trans hd₃.symm) hW'0 hW'1 hmap)
  omega

private theorem permutes_cover (C P Q : Subgroup L)
    (hP : P ≠ ⊤) (hQ : Q ≠ ⊤) (hPQ : ¬ P ≤ Q) (hQP : ¬ Q ≤ P)
    (hCP : C ≤ P) (hCQ : C ≤ Q)
    (hcover : ∀ K : Subgroup L, C ≤ K → K ≠ ⊤ → K ≤ P ∨ K ≤ Q)
    (α : MulAut L) (hC : C.map α.toMonoidHom = C) :
    ((P.map α.toMonoidHom = P ∧ Q.map α.toMonoidHom = Q) ∨
      (P.map α.toMonoidHom = Q ∧ Q.map α.toMonoidHom = P)) := by
  have hmaxP : IsCoatom P := by
    apply isCoatom_iff_ge_of_le.mpr
    refine ⟨hP, ?_⟩
    intro K hKt hPK
    rcases hcover K (hCP.trans hPK) hKt with h | h
    · exact h
    · exact (hPQ (hPK.trans h)).elim
  have hmaxQ : IsCoatom Q := by
    apply isCoatom_iff_ge_of_le.mpr
    refine ⟨hQ, ?_⟩
    intro K hKt hQK
    rcases hcover K (hCQ.trans hQK) hKt with h | h
    · exact (hQP (hQK.trans h)).elim
    · exact h
  have hmaxP' : IsCoatom (P.map α.toMonoidHom) := (OrderIso.isCoatom_iff α.mapSubgroup P).mpr hmaxP
  have hmaxQ' : IsCoatom (Q.map α.toMonoidHom) := (OrderIso.isCoatom_iff α.mapSubgroup Q).mpr hmaxQ
  have hCP' : C ≤ P.map α.toMonoidHom := by
    simpa only [hC] using map_mono (f := α.toMonoidHom) hCP
  have hCQ' : C ≤ Q.map α.toMonoidHom := by
    simpa only [hC] using map_mono (f := α.toMonoidHom) hCQ
  have hp : P.map α.toMonoidHom = P ∨ P.map α.toMonoidHom = Q := by
    rcases hcover _ hCP' hmaxP'.ne_top with h | h
    · exact Or.inl ((hmaxP'.le_iff_eq hP).mp h).symm
    · exact Or.inr ((hmaxP'.le_iff_eq hQ).mp h).symm
  have hq : Q.map α.toMonoidHom = P ∨ Q.map α.toMonoidHom = Q := by
    rcases hcover _ hCQ' hmaxQ'.ne_top with h | h
    · exact Or.inl ((hmaxQ'.le_iff_eq hP).mp h).symm
    · exact Or.inr ((hmaxQ'.le_iff_eq hQ).mp h).symm
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact (hPQ (map_injective α.injective (hp.trans hq.symm)).le).elim
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hq⟩
  · exact (hPQ (map_injective α.injective (hp.trans hq.symm)).le).elim

/-- Given the proper-overgroup cover, a dimension-changing automorphism fixing
 the transvection exchanges its image-line and fixed-hyperplane stabilizers.
 This has exactly the `hexchange` contract in `intersection_eq_of_geometric_inputs`. -/
theorem parabolics_exchanged_of_dimension_change (e : L ≃* PSL 4) {t : L}
    (c : TransvectionCoordinates e t)
    (hcover : ∀ K : Subgroup L, centralizer ({t} : Set L) ≤ K → K ≠ ⊤ →
      K ≤ subspaceStabilizer e c.line ∨ K ≤ subspaceStabilizer e c.hyperplane)
    (α : MulAut L) (ht : α t = t) (W W' : Space 4)
    (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) (hW'0 : W' ≠ ⊥) (hW'1 : W' ≠ ⊤)
    (hd : Module.finrank (ZMod 2) W ≠ Module.finrank (ZMod 2) W')
    (hmap : (subspaceStabilizer e W).map α.toMonoidHom = subspaceStabilizer e W') :
    (subspaceStabilizer e c.line).map α.toMonoidHom = subspaceStabilizer e c.hyperplane ∧
      (subspaceStabilizer e c.hyperplane).map α.toMonoidHom = subspaceStabilizer e c.line := by
  have hd₁ := c.line_finrank
  have hd₃ : Module.finrank (ZMod 2) c.hyperplane = 3 := by
    have := c.hyperplane_finrank
    omega
  have hl0 : c.line ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hd₁
    contradiction
  have hl1 : c.line ≠ ⊤ := by
    intro h
    rw [h, finrank_top, Module.finrank_fin_fun] at hd₁
    contradiction
  have hh0 : c.hyperplane ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hd₃
    contradiction
  have hh1 : c.hyperplane ≠ ⊤ := by
    intro h
    rw [h, finrank_top, Module.finrank_fin_fun] at hd₃
    contradiction
  have hdistinct : c.line ≠ c.hyperplane := by
    intro h
    rw [h, hd₃] at hd₁
    contradiction
  have hPQ : ¬ subspaceStabilizer e c.line ≤ subspaceStabilizer e c.hyperplane :=
    fun h => hdistinct (stabilizer_le_imp_eq e hh0 hh1 h)
  have hQP : ¬ subspaceStabilizer e c.hyperplane ≤ subspaceStabilizer e c.line :=
    fun h => hdistinct (stabilizer_le_imp_eq e hl0 hl1 h).symm
  have hC : (centralizer ({t} : Set L)).map α.toMonoidHom = centralizer ({t} : Set L) := by
    ext x
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      simpa only [map_mul, MulEquiv.apply_symm_apply, ht] using congrArg α h
    · intro h
      apply α.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply, ht] using h
  have hCP : centralizer ({t} : Set L) ≤ subspaceStabilizer e c.line := by
    rw [c.centralizer_eq]
    exact inf_le_left
  have hCQ : centralizer ({t} : Set L) ≤ subspaceStabilizer e c.hyperplane := by
    rw [c.centralizer_eq]
    exact inf_le_right
  rcases permutes_cover _ _ _ (stabilizer_ne_top e hl0 hl1) (stabilizer_ne_top e hh0 hh1)
    hPQ hQP hCP hCQ hcover α hC with ⟨hfix₁, hfix₃⟩ | hexchange
  · have htwo := changed_dimension_is_two e α c.line c.hyperplane hd₁ hd₃
      hfix₁ hfix₃ hW0 hW1 hW'0 hW'1 hd hmap
    have hfix₁' : (subspaceStabilizer e c.line).map α.symm.toMonoidHom =
        subspaceStabilizer e c.line := (map_symm_eq_iff_map_eq _).mpr hfix₁
    have hfix₃' : (subspaceStabilizer e c.hyperplane).map α.symm.toMonoidHom =
        subspaceStabilizer e c.hyperplane := (map_symm_eq_iff_map_eq _).mpr hfix₃
    have hmap' : (subspaceStabilizer e W').map α.symm.toMonoidHom =
        subspaceStabilizer e W := (map_symm_eq_iff_map_eq _).mpr hmap
    have htwo' := changed_dimension_is_two e α.symm c.line c.hyperplane hd₁ hd₃
      hfix₁' hfix₃' hW'0 hW'1 hW0 hW1 hd.symm hmap'
    exact (hd (htwo.trans htwo'.symm)).elim
  · exact hexchange

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.FourIntersection

end
