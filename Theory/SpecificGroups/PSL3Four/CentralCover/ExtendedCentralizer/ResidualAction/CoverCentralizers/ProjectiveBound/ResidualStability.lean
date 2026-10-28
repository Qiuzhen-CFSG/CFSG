module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.Counting

/-!
# The projective centralizer preserves the actual linear residual

Automorphisms of a perfect central cover descend faithfully. Thus an element
centralizing the projective image of w induces an automorphism of L commuting
with conjugation by w, even when that element does not commute with w in I.
It consequently preserves C_L(w), its two-residual, and the image of that
residual under the specified covering map.

Restriction gives an action of the full standard projective centralizer on
this projected residual. Its kernel embeds in the standard pointwise fixer.
No representative of w, or of either marked involution, is changed.

Source: the centralizer calculation in Aschbacher--Smith 15.3.38, printed
pp.1136--1137, manuscript of 1 March 2004. This reduction uses the actual
perfect covering map, not a simultaneous graph/field conjugacy.
-/

public section

open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.ProjectiveBound
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

/-- Projectively commuting elements induce commuting automorphisms of L. -/
theorem preimage_conjNormal_commute (d : Overgroup L) (w : I)
    (x : projectiveCentralizerPreimage d w) :
    Commute (MulAut.conjNormal (x : I) : MulAut L) (MulAut.conjNormal w) := by
  apply d.cover.toCover.autMap_injective d.cover.ker_eq_center
  simpa only [projectiveAction, MonoidHom.comp_apply, map_mul] using
    mem_centralizer_singleton_iff.mp x.property

private def linearMap (w x : I)
    (h : Commute (MulAut.conjNormal x : MulAut L) (MulAut.conjNormal w)) :
    linearCentralizer (L := L) w →* linearCentralizer (L := L) w := by
  let a : MulAut L := MulAut.conjNormal w
  let b : MulAut L := MulAut.conjNormal x
  let f : a.fixedSubgroup →* a.fixedSubgroup := {
    toFun y := ⟨b y, by
      rw [MulAut.mem_fixedSubgroup]
      have he := congrArg (fun u : MulAut L => u y.val) h.eq
      change b (a y.val) = a (b y.val) at he
      rw [(MulAut.mem_fixedSubgroup _ _).mp y.property] at he
      exact he.symm⟩
    map_one' := Subtype.ext (map_one b)
    map_mul' y z := Subtype.ext (map_mul b y.val z.val) }
  let e := fixedEquivLinearCentralizer (L := L) w
  exact e.toMonoidHom.comp (f.comp e.symm.toMonoidHom)

private theorem preimage_preserves_residual (d : Overgroup L) (w : I)
    (x : projectiveCentralizerPreimage d w) (r : projectedResidual d.cover w) :
    projectiveAction L d.cover (x : I) (r : PSL) ∈ projectedResidual d.cover w := by
  have h := preimage_conjNormal_commute d w x
  obtain ⟨s, hs⟩ := r.property
  obtain ⟨y, hy, he⟩ := s.property
  let f := linearMap w (x : I) h
  have hf : f y ∈ pResidual 2 (linearCentralizer (L := L) w) :=
    map_pResidual_le 2 f (mem_map.mpr ⟨y, hy, rfl⟩)
  let t : residualIn (L := L) w := ⟨f y, mem_map_of_mem _ hf⟩
  refine ⟨t, ?_⟩
  rw [← hs]
  change d.cover.toMonoidHom (residualToLinear w t) =
    d.cover.toCover.autMap d.cover.ker_eq_center (MulAut.conjNormal (x : I))
      (d.cover.toMonoidHom (residualToLinear w s))
  rw [d.cover.toCover.autMap_apply]
  apply congrArg d.cover.toMonoidHom
  apply Subtype.ext
  change (f y).val.val = (x : I) * s.val.val * (x : I)⁻¹
  rw [← he]
  rfl

/-- Every projective centralizer element preserves the given residual image. -/
theorem preserves_residual (d : Overgroup L) (w : I)
    (a : projectiveCentralizer d w) (r : projectedResidual d.cover w) :
    a.val (r : PSL) ∈ projectedResidual d.cover w := by
  have ha : a.val ∈ (projectiveCentralizerPreimage d w).map
      (projectiveAction L d.cover) := by
    simpa only [projectiveCentralizerPreimage_map] using a.property
  obtain ⟨x, hx, he⟩ := ha
  rw [← he]
  exact preimage_preserves_residual d w ⟨x, hx⟩ r

/-- Setwise stability retains the literal projected subgroup of PSL₃(4). -/
theorem map_residual (d : Overgroup L) (w : I)
    (a : projectiveCentralizer d w) :
    (projectedResidual d.cover w).map a.val.toMonoidHom =
      projectedResidual d.cover w := by
  apply le_antisymm
  · rintro r ⟨s, hs, rfl⟩
    exact preserves_residual d w a ⟨s, hs⟩
  · intro r hr
    refine ⟨a.val.symm r, preserves_residual d w a⁻¹ ⟨r, hr⟩, ?_⟩
    exact a.val.apply_symm_apply r

/-- Restriction of the projective centralizer's actual action to the residual. -/
@[expose] noncomputable def action (d : Overgroup L) (w : I) :
    projectiveCentralizer d w →* MulAut (projectedResidual d.cover w) where
  toFun a := (a.val.subgroupMap (projectedResidual d.cover w)).trans
    (MulEquiv.subgroupCongr (map_residual d w a))
  map_one' := by ext r; rfl
  map_mul' _ _ := by ext r; rfl

/-- The restriction acts through the original projective automorphism. -/
theorem action_apply (d : Overgroup L) (w : I)
    (a : projectiveCentralizer d w) (r : projectedResidual d.cover w) :
    (action d w a r : PSL) = a.val r := by rfl

private noncomputable def kernelToFixer (d : Overgroup L) (w : I) :
    (action d w).ker →* projectedResidualFixer d.cover w where
  toFun x := ⟨x.val.val, ⟨x.val.property.1, fun r => by
    have hx : action d w x.val = 1 := x.property
    exact congrArg (fun b : MulAut (projectedResidual d.cover w) => (b r : PSL)) hx⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The action kernel is bounded by the standard pointwise fixer. -/
theorem kernel_card_dvd_fixer (d : Overgroup L) (w : I) :
    Nat.card (action d w).ker ∣ Nat.card (projectedResidualFixer d.cover w) := by
  apply card_dvd_of_injective (kernelToFixer d w)
  intro x y h
  have hv : x.val.val = y.val.val :=
    congrArg (fun z : projectedResidualFixer d.cover w => z.val) h
  exact Subtype.ext (Subtype.ext hv)

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.ProjectiveBound
