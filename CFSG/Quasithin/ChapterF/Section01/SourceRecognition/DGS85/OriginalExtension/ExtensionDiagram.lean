module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.RestoredCompletion
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Basic

/-!
# Restoring the original marked extension diagram

Kernel descent realizes the original full Borel in the automorphism group
of the reduced concrete completion. The inner-preimage theorem shows that
each restored endpoint meets the inner automorphism group in precisely its
reduced endpoint image. Products of an inner actor and a full-Borel actor
preserve both native parabolic conjugacy classes and factor through the
whole original overlap. This constructs the algebraic source-extension
contract, rather than assuming its endpoint/intersection clauses.

The final isomorphism retains both reduced endpoint restrictions and every
element of the original Borel. Kernel preservation and the concrete reduced
marking remain explicit inputs, to be supplied by the corresponding native
lift and recognition theorems.

Source: DGS, *Groups and Graphs* (1985), (15.2), pp.226–228;
Aschbacher–Smith F.4.3, printed p.274, for the extension-diagram conventions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment SourceCompletion.UnitaryNonbinary
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S)
  (c : FaithfulCompletion (reducedAmalgam L S) (G := X))
  (hk : PreservesCompletionKernel h c)
  (ho : c.left.range ⊓ c.right.range = c.middle.range)
  (hN : ∀ i, normalizer ((completionEndpoint c i).range : Set X) =
    (completionEndpoint c i).range)

private theorem endpoint_action_normalizes (i : Fin 2) :
    (completionAction h c hk).range ≤ normalizer (innerEndpoint c i : Set (MulAut X)) := by
  rintro a ⟨b,rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he : (MulAut.conj (completionAction h c hk b)).toMonoidHom.comp MulAut.conj =
      MulAut.conj.comp (completionAction h c hk b).toMonoidHom := by
    ext x y
    simp
  change ((completionEndpoint c i).range.map MulAut.conj).map
    (MulAut.conj (completionAction h c hk b)).toMonoidHom = _
  rw [map_map, he, ← map_map, completionAction_endpoint_range]
  rfl

include ho hN in
theorem restoredEndpoint_inf_inner (i : Fin 2) :
    (innerEndpoint c i ⊔ (completionAction h c hk).range) ⊓ MulAut.innerSubgroup X =
      innerEndpoint c i := by
  apply le_antisymm _ (le_inf le_sup_left (map_le_range _ _))
  rintro a ⟨ha,hi⟩
  have hp : a ∈ (innerEndpoint c i : Set (MulAut X)) * (completionAction h c hk).range := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (endpoint_action_normalizes h c hk i)]
    exact ha
  obtain ⟨x,hx,_,⟨b,rfl⟩,rfl⟩ := hp
  have hb : completionAction h c hk b ∈ MulAut.innerSubgroup X := by
    simpa only [inv_mul_cancel_left] using
      (MulAut.innerSubgroup X).mul_mem
        ((MulAut.innerSubgroup X).inv_mem ((map_le_range _ _) hx)) hi
  have hb₀ := (completionAction_mem_inner_iff h c hk ho hN b).mp hb
  exact (innerEndpoint c i).mul_mem hx
    ((completionAction_mem_innerEndpoint_iff h c hk ho hN i b).mpr hb₀)

private theorem map_mul_actor (P : Subgroup X) (a b : MulAut X) :
    P.map (a*b).toMonoidHom = (P.map b.toMonoidHom).map a.toMonoidHom := by
  rw [map_map]
  rfl

theorem automorphismExtension_preserves_types (a : MulAut X)
    (ha : a ∈ automorphismExtension h c hk) : PreservesTypes c.left.range c.right.range a := by
  have hp : a ∈ (MulAut.innerSubgroup X : Set (MulAut X)) *
      (completionAction h c hk).range := by
    rw [← normal_mul]
    exact ha
  obtain ⟨_,⟨x,rfl⟩,_,⟨b,rfl⟩,rfl⟩ := hp
  have hh (i : Fin 2) :
      (completionEndpoint c i).range.map (MulAut.conj x * completionAction h c hk b).toMonoidHom =
        (completionEndpoint c i).range.map (MulAut.conj x).toMonoidHom := by
    rw [map_mul_actor, completionAction_endpoint_range]
  exact ⟨⟨x,hh 0⟩,⟨x,hh 1⟩⟩

include h hk ho hN
/-- The restored original group as an actual type-preserving extension of
the reduced endpoint images, with the entire original Borel as overlap. -/
@[expose] def restoredSourceExtension : SourceExtension c.left.range c.right.range where
  carrier := automorphismExtension h c hk
  left := innerEndpoint c 0 ⊔ (completionAction h c hk).range
  right := innerEndpoint c 1 ⊔ (completionAction h c hk).range
  left_le := sup_le ((map_le_range _ _).trans le_sup_left) le_sup_right
  right_le := sup_le ((map_le_range _ _).trans le_sup_left) le_sup_right
  contains_inner := inner_le_automorphismExtension h c hk
  preserves_types := automorphismExtension_preserves_types h c hk
  left_inner := restoredEndpoint_inf_inner h c hk ho hN 0
  right_inner := restoredEndpoint_inf_inner h c hk ho hN 1
  factor := by
    intro a ha
    have hp : a ∈ (MulAut.innerSubgroup X : Set (MulAut X)) *
        (completionAction h c hk).range := by
      rw [← normal_mul]
      exact ha
    obtain ⟨_,⟨x,rfl⟩,b,hb,rfl⟩ := hp
    exact ⟨x,b,⟨(show (completionAction h c hk).range ≤ _ from le_sup_right) hb,
      (show (completionAction h c hk).range ≤ _ from le_sup_right) hb⟩,rfl⟩

theorem restoredSourceExtension_middle :
    (restoredSourceExtension h c hk ho hN).middle = (completionAction h c hk).range :=
  restoredEndpoint_intersection h c hk ho hN

/-- Both original endpoints map into the same extension; the whole original
Borel map and both literal reduced restrictions are retained. -/
theorem exists_original_sourceExtension_iso :
    ∃ e : Iso (originalAmalgam L S) (restoredSourceExtension h c hk ho hN).amalgam,
      (∀ b : commonBorel L S, (e.middle b : MulAut X) = completionAction h c hk b) ∧
      (∀ x : parabolic L (reducedSylow L S) 0,
        (e.left (inclusion (reduced_parabolic_le h 0) x) : MulAut X) = MulAut.conj (c.left x)) ∧
      (∀ x : parabolic L (reducedSylow L S) 1,
        (e.right (inclusion (reduced_parabolic_le h 1) x) : MulAut X) = MulAut.conj (c.right x)) := by
  obtain ⟨e,he,hl,hr⟩ := exists_original_automorphism_iso h c hk ho hN
  let d : Iso
      (ofSubgroups (innerEndpoint c 0 ⊔ (completionAction h c hk).range)
        (completionAction h c hk).range
        (innerEndpoint c 1 ⊔ (completionAction h c hk).range) le_sup_right le_sup_right)
      (restoredSourceExtension h c hk ho hN).amalgam := {
    left := MulEquiv.refl _
    middle := MulEquiv.subgroupCongr (restoredSourceExtension_middle h c hk ho hN).symm
    right := MulEquiv.refl _
    left_commutes := fun _ => Subtype.ext rfl
    right_commutes := fun _ => Subtype.ext rfl }
  refine ⟨e.trans d,?_,hl,hr⟩
  intro b
  change (e.middle b : MulAut X) = _
  rw [he]
  rfl

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
