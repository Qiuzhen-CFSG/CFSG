module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.ResidualNormalizers.EndpointActions
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular

/-!
# The last-node action on the invariant three-space

The last single-node parabolic of binary five-space preserves the first
three cuts of the marked flag. Restrict its action to the three-space and
use the first three marked basis vectors as coordinates. Preservation of
the lower cuts makes every resulting matrix upper triangular. Its diagonal
entries are nonzero by invertibility, hence all equal one over the binary
field. The action image therefore embeds in the unitriangular two-group.

This proves the last endpoint action-image input for the residual-normalizer
calculation used in Aschbacher–Smith, 13.8.25, combined manuscript of
1 March 2004, printed p.960 (PDF p.977). It retains the actual restricted
action and does not require surjectivity onto the unitriangular subgroup.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
namespace BinaryLinear.SmallParabolicLevi.ResidualNormalizers

private theorem head_span (b : FiveBasis) :
    Submodule.span (ZMod 2) (Set.range (fun i : Fin 3 => b (i.castLE (by decide)))) =
      flagSpace b 2 := by
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i.castLE (by decide), ?_, rfl⟩
    exact Nat.le_of_lt_succ i.isLt
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, by change i.val ≤ 2 at hi; omega⟩, rfl⟩

private noncomputable def headBasis (b : FiveBasis) :
    Module.Basis (Fin 3) (ZMod 2) (flagSpace b 2) :=
  (Module.Basis.span (b.linearIndependent.comp
    (fun i : Fin 3 => i.castLE (by decide)) (Fin.castLE_injective (by decide)))).map
      (LinearEquiv.ofEq _ _ (head_span b))

private theorem headBasis_apply (b : FiveBasis) (i : Fin 3) :
    (headBasis b i : Space 5) = b (i.castLE (by decide)) := by
  simp [headBasis]

private theorem headBasis_repr (b : FiveBasis) (w : flagSpace b 2) (i : Fin 3) :
    (headBasis b).repr w i = b.repr w (i.castLE (by decide)) := by
  have he : (headBasis b).coord i =
      (b.coord (i.castLE (by decide))).comp (flagSpace b 2).subtype := by
    apply (headBasis b).ext
    intro j
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, headBasis_apply]
    congr 1
    exact propext (Fin.castLE_injective (show 3 ≤ 5 by decide)).eq_iff.symm
  exact LinearMap.congr_fun he w

private noncomputable def headSL (b : FiveBasis) :
    BinaryLinear.GL (flagSpace b 2) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (linearGroupCongr (headBasis b).equivFun).trans (slEquivLinear 3).symm

private theorem headSL_apply (b : FiveBasis) (g : BinaryLinear.GL (flagSpace b 2))
    (i j : Fin 3) :
    (headSL b g).val i j = (headBasis b).repr (g (headBasis b j)) i := by
  have hm : (headSL b g).val.mulVec (Pi.single j 1) =
      (headBasis b).equivFun (g ((headBasis b).equivFun.symm (Pi.single j 1))) := by
    rw [← slEquivLinear_apply]
    change slEquivLinear 3 ((slEquivLinear 3).symm
      (linearGroupCongr (headBasis b).equivFun g)) _ = _
    rw [MulEquiv.apply_symm_apply, linearGroupCongr_apply]
  have hb : (headBasis b).equivFun.symm (Pi.single j 1) = headBasis b j := by
    apply (headBasis b).equivFun.injective
    ext k
    simp [Pi.single_apply]
  have he := congrFun hm i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, hb, Module.Basis.equivFun_apply] using he

private theorem headSL_upper (b : FiveBasis)
    (g : flagStabilizer b ({3} : Set (Fin 4))ᶜ) :
    (headSL b (lastHeadAction b g)).val.IsUpperTriangular := by
  intro i j hji
  rw [headSL_apply, headBasis_repr]
  change b.repr (g.val (headBasis b j : Space 5)) (i.castLE (by decide)) = 0
  rw [headBasis_apply]
  let k : Fin 4 := ⟨j.val, by omega⟩
  have hk : k ∈ ({3} : Set (Fin 4))ᶜ := by
    change k ≠ 3
    intro h
    have he := congrArg Fin.val h
    dsimp [k] at he
    omega
  have hm : g.val (b (j.castLE (by decide))) ∈ flagSpace b k :=
    (mem_flagStabilizer_iff_maps b _ g.val).mp g.property k hk _
      ((basis_mem_flagSpace_iff b k _).mpr le_rfl)
  have hs := b.mem_span_image.mp hm
  by_contra hn
  have hle := hs (Finsupp.mem_support_iff.mpr hn)
  change i.val ≤ j.val at hle
  exact (not_le_of_gt hji) hle

private theorem headSL_mem_unipotent (b : FiveBasis)
    (g : flagStabilizer b ({3} : Set (Fin 4))ᶜ) :
    headSL b (lastHeadAction b g) ∈
      Theory.SpecificGroups.LinearSylowNormalizers.unipotent 3 (ZMod 2) := by
  rw [Theory.SpecificGroups.LinearSylowNormalizers.mem_unipotent]
  have hu := headSL_upper b g
  refine ⟨(Theory.SpecificGroups.LinearSylowNormalizers.mem_borel 3 (ZMod 2) _).mpr hu,
    fun i => ?_⟩
  have hd := (headSL b (lastHeadAction b g)).property
  rw [Matrix.det_of_isUpperTriangular hu] at hd
  have hp : (∏ j : Fin 3, (headSL b (lastHeadAction b g)).val j j) ≠ 0 := by
    rw [hd]
    exact one_ne_zero
  have hi := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hi

/-- The last-node parabolic acts through a two-group on its invariant three-space. -/
theorem lastHeadAction_range_isPGroup (b : FiveBasis) :
    IsPGroup 2 (lastHeadAction b).range := by
  apply ((Theory.SpecificGroups.LinearSylowNormalizers.unipotent_isPGroup
    3 (ZMod 2) (by decide)).comap_of_injective
      (headSL b).toMonoidHom (headSL b).injective).to_le
  rintro _ ⟨g, rfl⟩
  exact headSL_mem_unipotent b g

end BinaryLinear.SmallParabolicLevi.ResidualNormalizers

end
