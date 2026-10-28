module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.Basic

/-!
# From an equivariant coset comparison to both marked endpoint ranges

An equivariant isomorphism of the typed coset graphs makes the comparison
homomorphism injective, by the trivial-kernel theorem. Transport the image
of the standard incident flag back to the native flag. The resulting two
endpoint inclusions are equalities, since faithfulness fixes their orders.
Their generation then makes the homomorphism surjective.

Thus no agreement with every marked endpoint element is imposed. This is
the quasiequivalence conclusion needed in Aschbacher–Smith F.4.8(2), and
hence in the PSL₃(4) specialization of F.4.26. The geometric comparison and
whole-overlap identity remain explicit premises, to be proved from the
source involutions by the smallness and plane-recognition arguments.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
open Subgroup.CosetGeometry
open Theory.GroupTheory

variable {G H : Type*} [Group G] [Group H] [Finite H]
variable (c : Completion G) (d : Completion H)

/-- A type-preserving equivariant graph comparison determines a range-preserving
isomorphism of the completions. -/
theorem exists_range_preserving_equiv_of_equivariant_graphIso
    (ho : c.left.range ⊓ c.right.range = c.middle.range)
    (q : c.graph ≃g d.graph) (f : G →* H)
    (hqt : ∀ v, (q v).type = v.type)
    (he : ∀ g v, q (g • v) = f g • q v) :
    ∃ e : G ≃* H,
      c.left.range.map e.toMonoidHom = d.left.range ∧
      c.right.range.map e.toMonoidHom = d.right.range := by
  have hf : Function.Injective f := by
    intro a b hab
    apply c.vertex_action_injective_of_overlap ho
    apply Equiv.Perm.ext
    intro v
    apply q.injective
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, he, hab]
  let x := RankTwo.base c.family false
  let l := RankTwo.base c.family true
  have hxl : c.graph.Adj x l := ⟨Bool.false_ne_true, incident_base c.family false true⟩
  obtain ⟨k, hkx, hkl⟩ := RankTwo.incident_common_translate d.family
    (q.toHom.map_adj hxl).2
  have hx : (q x).type = false := hqt x
  have hl : (q l).type = true := hqt l
  change k • RankTwo.base d.family (q x).type = q x at hkx
  change k • RankTwo.base d.family (q l).type = q l at hkl
  rw [hx] at hkx
  rw [hl] at hkl
  let f' : G →* H := (MulAut.conj k⁻¹).toMonoidHom.comp f
  have hf' : Function.Injective f' := (MulAut.conj k⁻¹).injective.comp hf
  have htransport (i : Bool)
      (hk : k • RankTwo.base d.family i = q (RankTwo.base c.family i)) :
      (c.family i).map f' ≤ d.family i := by
    rintro _ ⟨g, hg, rfl⟩
    have hfix : g • RankTwo.base c.family i = RankTwo.base c.family i := by
      change g ∈ MulAction.stabilizer G (RankTwo.base c.family i)
      simpa only [RankTwo.base, stabilizer_base, SetLike.mem_coe] using hg
    rw [← stabilizer_base d.family i]
    change (k⁻¹ * f g * (k⁻¹)⁻¹) • RankTwo.base d.family i = _
    rw [inv_inv, mul_smul, mul_smul, hk, ← he, hfix, ← hk, inv_smul_smul]
  have hleft : c.left.range.map f' = d.left.range := by
    apply Subgroup.eq_of_le_of_card_ge (htransport false hkx)
    rw [Subgroup.card_map_of_injective hf', family_false, family_false,
      RankTwoAmalgam.FaithfulCompletion.left_card c,
      RankTwoAmalgam.FaithfulCompletion.left_card d]
  have hright : c.right.range.map f' = d.right.range := by
    apply Subgroup.eq_of_le_of_card_ge (htransport true hkl)
    rw [Subgroup.card_map_of_injective hf', family_true, family_true,
      RankTwoAmalgam.FaithfulCompletion.right_card c,
      RankTwoAmalgam.FaithfulCompletion.right_card d]
  have hsurj : Function.Surjective f' := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← d.generated, ← hleft, ← hright]
    exact sup_le (Subgroup.map_le_range _ _) (Subgroup.map_le_range _ _)
  exact ⟨MulEquiv.ofBijective f' ⟨hf', hsurj⟩, hleft, hright⟩

/-- Native-model specialization, with the two actual projective parabolics. -/
theorem exists_parabolic_preserving_equiv_of_equivariant_graphIso
    (ho : c.left.range ⊓ c.right.range = c.middle.range)
    (q : c.graph ≃g modelCompletion.graph) (f : G →* Matrix.PSL3Four.PSL)
    (hqt : ∀ v, (q v).type = v.type)
    (he : ∀ g v, q (g • v) = f g • q v) :
    ∃ e : G ≃* Matrix.PSL3Four.PSL,
      c.left.range.map e.toMonoidHom =
        Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F ∧
      c.right.range.map e.toMonoidHom =
        Matrix.PSL3.LinearThree.lineParabolic Matrix.PSL3Four.F := by
  obtain ⟨e, hl, hr⟩ := c.exists_range_preserving_equiv_of_equivariant_graphIso
    modelCompletion ho q f hqt he
  exact ⟨e, hl.trans model_left_range, hr.trans model_right_range⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
