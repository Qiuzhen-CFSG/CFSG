module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The intrinsic binary MS input and its component quotient

The hypotheses are the binary specialization of C.1.31(MS1), (MS2)(a), and
(MS3). The quotient is the actual special linear group, with its quotient map;
no module shape or classification alternative is an input.

A subnormal perfect subgroup with a two-group supplement is the two-residual,
hence normal. Its intrinsic two-core is its intersection with the ambient
one. Centerlessness then identifies the kernel of the quotient conjugation
action with the ambient two-core.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137. These are preliminary reductions, not MS93 exhaustiveness.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup Theory.GroupTheory
universe u
variable {J : Type u} [Group J]

/-- All intrinsic binary MS hypotheses, with a specified genuine quotient
isomorphism. Centerlessness and perfectness below discharge the derived
rank-two clause of (MS1), using `centralPreimage` for `O₂,Z`. -/
structure Input (κ : GroupClass.{u}) (L R : Subgroup J) where
  sqtk : IsSQTK κ J
  fitting : generalizedFitting J = pCore 2 J
  product : ∀ j : J, ∃ l ∈ L, ∃ r ∈ R, l * r = j
  component : L.IsCComponent
  radical : MSOddIndexRadical R
  characteristic : MSCharacteristicCondition R
  quotientEquiv : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

/-- The actual core in C.1.34, taken inside J. -/
abbrev commutatorCore (L : Subgroup J) : Subgroup J := ⁅pCore 2 J, L⁆

variable {κ : GroupClass.{u}} {L R : Subgroup J} (h : Input κ L R)

/-- The binary rank-two matrix group equals its derived subgroup. -/
theorem binary_perfect :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  Atlas.sl_perfect 3 (by decide)

include h

/-- Centerlessness is transported through the specified quotient isomorphism. -/
theorem Input.quotient_center : center (L ⧸ pCore 2 L) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hz := (centerCongr h.quotientEquiv ⟨x, hx⟩).property
  have he : h.quotientEquiv x = 1 := Matrix.PSL3Two.center_eq_bot.le hz
  exact h.quotientEquiv.map_eq_one_iff.mp he

/-- The source's central preimage O₂,Z(L) is exactly O₂(L) in this case. -/
theorem Input.centralPreimage_eq : centralPreimage (pCore 2 L) = pCore 2 L := by
  change (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' _) = _
  rw [h.quotient_center]
  exact QuotientGroup.ker_mk' _

/-- The literal quotient in (MS1) is isomorphic to the derived subgroup of
SL₃(2), not merely assigned a Lie-family tag. -/
noncomputable def Input.derivedQuotientEquiv :
    (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  letI := binary_perfect
  exact (QuotientGroup.quotientMulEquivOfEq h.centralPreimage_eq).trans
    (h.quotientEquiv.trans (topEquiv.symm.trans
      (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)))

/-- The specified quotient has order 168. -/
theorem Input.quotient_card : Nat.card (L ⧸ pCore 2 L) = 168 :=
  (Nat.card_congr h.quotientEquiv.toEquiv).trans Matrix.PSL3Two.card_SL

variable [Finite J]

omit h in
private theorem perfect_twoPerfect {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] : IsPPerfect 2 G := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The component is the actual two-residual of J. No normalization of R
by L is assumed. -/
theorem Input.residual_eq : pResidual 2 J = L := by
  let := h.component.perfect
  exact pResidual_eq_of_subnormal_product L R h.component.subnormal
    perfect_twoPerfect h.radical.isPGroup h.product

/-- In particular the component is characteristic, and hence normal, in J. -/
theorem Input.component_characteristic : L.Characteristic := by
  rw [← h.residual_eq]
  infer_instance

theorem Input.component_normal : L.Normal := by
  let := h.component_characteristic
  infer_instance

omit [Finite J] in
/-- The literal product also generates J. -/
theorem Input.sup_eq_top : L ⊔ R = ⊤ := by
  apply eq_top_iff.mpr
  intro j _
  obtain ⟨l, hl, r, hr, rfl⟩ := h.product j
  exact mul_mem (mem_sup_left hl) (mem_sup_right hr)

/-- Explicit comparison of intrinsic and ambient two-cores. -/
theorem Input.componentCore_eq_inf : (pCore 2 L).map L.subtype = pCore 2 J ⊓ L := by
  rw [pCore_subnormal_eq_comap 2 h.component.subnormal, map_comap_eq, L.range_subtype,
    inf_comm]

/-- The commutator core lies in the mapped intrinsic two-core of L. -/
theorem Input.commutatorCore_le : commutatorCore L ≤ (pCore 2 L).map L.subtype := by
  let := h.component_normal
  rw [h.componentCore_eq_inf]
  exact commutator_le_inf _ _

/-- The commutator core agrees with the ambient image of the intrinsic
core commutator of L. This uses two-perfectness, not a core-shape assumption. -/
theorem Input.commutatorCore_eq_internal :
    commutatorCore L = (⁅pCore 2 L, (⊤ : Subgroup L)⁆).map L.subtype := by
  let := h.component.perfect
  apply le_antisymm
  · exact commutator_le_core_commutator_of_isSubnormal L (pCore 2 J)
      h.component.subnormal perfect_twoPerfect pCore_isPGroup
      (by rw [normalizer_eq_top]; exact le_top)
  · rw [map_commutator, ← MonoidHom.range_eq_map, L.range_subtype]
    exact commutator_mono (h.componentCore_eq_inf.le.trans inf_le_left) le_rfl

/-- The actual core is generated again by its commutators with L. -/
theorem Input.commutatorCore_idempotent :
    ⁅commutatorCore L, L⁆ = commutatorCore L := by
  let := h.component.perfect
  exact commutator_isPPerfect_idempotent L (pCore 2 J) perfect_twoPerfect
    pCore_isPGroup (by rw [normalizer_eq_top]; exact le_top)

/-- Characteristic two follows from the genuine generalized-Fitting hypothesis. -/
theorem Input.core_selfCentralizing : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
  simpa only [h.fitting] using
    (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := J))

/-- The radical is nontrivial; a trivial core would make J trivial. -/
theorem Input.radical_ne_bot : R ≠ ⊥ := by
  intro hr
  have hn : pCore 2 J = ⊥ := le_bot_iff.mp (hr ▸ h.radical.twoCore_le)
  have ht : (⊤ : Subgroup J) ≤ ⊥ := by
    intro j _
    have hc : j ∈ centralizer (pCore 2 J : Set J) := by
      rw [hn]
      intro x hx
      have hx1 : x = 1 := hx
      simp only [hx1, one_mul, mul_one]
    exact hn ▸ h.core_selfCentralizing hc
  exact h.component.ne_bot (le_bot_iff.mp (le_top.trans ht))

/-- The join carrier is identified with J by its inclusion, not an arbitrary
isomorphism of groups of the same order. -/
noncomputable def Input.joinEquiv : (L ⊔ R : Subgroup J) ≃* J :=
  (MulEquiv.subgroupCongr h.sup_eq_top).trans topEquiv

omit [Finite J] in
@[simp] theorem Input.joinEquiv_apply (x : (L ⊔ R : Subgroup J)) :
    h.joinEquiv x = (x : J) := by rfl

omit [Finite J] in
@[simp] theorem Input.joinEquiv_symm_apply (x : J) :
    (h.joinEquiv.symm x : J) = x := by rfl

private theorem radical_normalizes : R ≤ normalizer L := by
  let := h.component_normal
  rw [normalizer_eq_top]
  exact le_top

/-- The actual conjugation action on L/O₂(L), defined using the normal join. -/
noncomputable def Input.quotientAction : J →* MulAut (L ⧸ pCore 2 L) :=
  (pCoreJoinAction 2 (radical_normalizes h)).comp h.joinEquiv.symm.toMonoidHom

/-- Representatives are sent to their actual J-conjugates. -/
theorem Input.quotientAction_mk (j : J) (l : L) :
    h.quotientAction j (QuotientGroup.mk' (pCore 2 L) l) =
      QuotientGroup.mk' (pCore 2 L)
        ⟨j * (l : J) * j⁻¹, h.component_normal.conj_mem l l.property j⟩ := by
  exact pCoreJoinAction_mk 2 (radical_normalizes h) (h.joinEquiv.symm j) l

/-- The action kernel is exactly the intrinsic ambient two-core. -/
theorem Input.quotientAction_kernel : h.quotientAction.ker = pCore 2 J := by
  change (pCoreJoinAction 2 (radical_normalizes h)).ker.comap
    h.joinEquiv.symm.toMonoidHom = _
  rw [pCoreJoinAction_kernel 2 (radical_normalizes h) h.radical.isPGroup h.quotient_center]
  rw [← pCore_map_iso 2 h.joinEquiv.symm]
  exact comap_map_eq_self_of_injective h.joinEquiv.symm.injective _

/-- Restriction to L is its ordinary inner action on the quotient. -/
theorem Input.quotientAction_component (l : L) :
    h.quotientAction l = MulAut.conj (QuotientGroup.mk' (pCore 2 L) l) :=
  pCoreJoinAction_on_component 2 (radical_normalizes h) l

/-- The core quotient is identified with the actual conjugation image. -/
noncomputable def Input.quotientEquivRange :
    (J ⧸ pCore 2 J) ≃* h.quotientAction.range :=
  (QuotientGroup.quotientMulEquivOfEq h.quotientAction_kernel.symm).trans
    (QuotientGroup.quotientKerEquivRange h.quotientAction)

/-- Every inner automorphism occurs in the action image. -/
theorem Input.inner_le_range :
    MulAut.innerSubgroup (L ⧸ pCore 2 L) ≤ h.quotientAction.range := by
  rintro a ⟨x, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
  exact ⟨l, h.quotientAction_component l⟩

end CFSG.Quasithin.ChapterC.BinaryMS
