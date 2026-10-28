module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Setup
public import Stellmacher.BaumannIntermediate
public import Theory.GroupTheory.PCoreImage

/-!
# The centralizing and transposition branches of C.1.37

The original natural S6 action makes O₂(K) the module centralizer. A trivial
Thompson image therefore gives the characteristic-normal alternative by
B.2.10. When the Baumann image is a transposition, adjoining O₂(K) preserves
its Baumann subgroup, so the proved natural-six form of C.1.24(c) applies.
Both conclusions concern the original point-parabolic Baumann subgroup.

Source: Aschbacher--Smith C.1.37, printed pp.141--143.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Theory.GroupTheory Stellmacher
universe u
variable {K : Type u} [Group K] [Finite K]
variable {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
namespace SourceData
variable (d : SourceData L V T)
include d

omit [Finite K] in
theorem core_le_point : pCore 2 K ≤ d.P := by
  rw [← d.centralizer_eq_core]
  intro g hg
  apply mem_centralizer_iff.mpr
  intro x hx
  obtain rfl : x = (d.v : K) := Set.mem_singleton_iff.mp hx
  exact mem_centralizer_iff.mp hg d.v d.v.property

omit [Finite K] in
theorem core_le_radical : pCore 2 K ≤ d.R :=
  le_pCoreIn_of_normalizes pCore_isPGroup d.core_le_point (by rw [normalizer_eq_top];exact le_top)

omit [Finite K] in
theorem radical_le_sylow : d.R ≤ (T : Subgroup K) := by
  have h := pCoreIn_le_sylow d.P (T.subtype d.sylow_le_point)
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le d.sylow_le_point] using h

omit [Finite K] in
theorem module_le_radical : V ≤ d.R := by
  let := d.elementary
  have hv : V ≤ pCore 2 K := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 V⟩
  exact hv.trans d.core_le_radical

omit [Finite K] in
theorem radical_ne_bot : d.R ≠ ⊥ := by
  intro hz
  have hm : (d.v : K) ∈ d.R := d.module_le_radical d.v.property
  rw [hz] at hm
  exact d.v_ne (Subtype.ext hm)

omit [Finite K] in
theorem product (g : K) : ∃ l ∈ L, ∃ t ∈ (T : Subgroup K), l*t=g :=
  mem_sup_of_normal_left.mp (d.generation.symm ▸ mem_top g)

noncomputable def componentEquiv : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6) := by
  let f := d.q.comp L.subtype
  have hk : f.ker = pCore 2 L := by
    rw [pCore_subnormal_eq_comap 2 d.component.subnormal,← d.ker_eq]
    rfl
  have hr : f.range = alternatingGroup (Fin 6) := by
    rw [MonoidHom.range_comp,range_subtype]
    exact d.image_component
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hr))

theorem component_quasisimple : IsQuasisimple (L ⧸ pCore 2 L) := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  exact IsQuasisimple.of_mulEquiv d.componentEquiv.symm

omit [Finite K] in
theorem module_moved : ⁅V,L⁆ ≠ ⊥ := by
  intro hz
  have hL : L ≤ d.q.ker := by
    rw [d.kernel_centralizer]
    exact commutator_eq_bot_iff_le_centralizer.mp (commutator_comm V L ▸ hz)
  have hbot : alternatingGroup (Fin 6) = ⊥ :=
    d.image_component.symm.trans ((Subgroup.map_eq_bot_iff L).mpr hL)
  have hm : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 ∈ alternatingGroup (Fin 6) := by decide
  rw [hbot] at hm
  exact (by decide : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 ≠ 1) hm

/-- The centralizing Thompson case gives the literal characteristic-normal
alternative on the original Baumann subgroup. -/
theorem characteristic_of_thompson_image_bot
    (hz : (elementaryAbelianMaxJ d.R).map d.q = ⊥) :
    ∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal := by
  let := d.elementary
  have hc : pCore 2 K = d.R ⊓ centralizer (V : Set K) := by
    rw [d.centralizer_eq_core,inf_eq_right.mpr d.core_le_radical]
  have hJ : ChapterB.thompsonJ d.R 0 ≤ centralizer (V : Set K) := by
    rw [ChapterB.thompsonJ_zero,← d.kernel_centralizer]
    exact (Subgroup.map_eq_bot_iff _).mp hz
  have hn : d.B.Normal :=
    (ChapterB.lemma_B_2_10_centralizing V d.R d.module_le_radical d.core_le_radical hc hJ).2.2.2
  have hne : d.B ≠ ⊥ := RankOne.SymmetricSix.baumann_ne_bot d.R (isPGroup_pCoreIn 2 _) d.radical_ne_bot
  let : Nontrivial d.B := (nontrivial_iff_ne_bot _).mpr hne
  exact ⟨⊤,inferInstance,top_ne_bot,by simpa only [←MonoidHom.range_eq_map,range_subtype] using hn⟩

/-- If the original Baumann image is a transposition, the intermediate group
B O₂(K) has the same Baumann subgroup and C.1.24(c) applies literally. -/
theorem characteristic_or_block_of_baumann_image_swap
    (r : Equiv.Perm (Fin 6)) (hr : r.IsSwap) (hB : d.B.map d.q = zpowers r) :
    (∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal) ∨ IsAlternatingBlock L 6 := by
  let := d.elementary
  let : IsQuasisimple (L ⧸ pCore 2 L) := d.component_quasisimple
  let R0 := d.B ⊔ pCore 2 K
  have hR0 : R0 ≤ d.R := sup_le inf_le_left d.core_le_radical
  have hb : ChapterB.baumann R0 = d.B :=
    baumann_eq_of_intermediate d.R R0 le_sup_left hR0
  have hm : R0.map d.q = zpowers r := by
    rw [Subgroup.map_sup,hB,(Subgroup.map_eq_bot_iff _).mpr d.ker_eq.symm.le,sup_bot_eq]
  have h := RankOne.SymmetricSix.normal_characteristic_or_alternatingBlock_of_natural_six
    L V R0 d.component d.fitting d.component_fitting T le_sup_right
    (hR0.trans d.radical_le_sylow) d.product d.q d.image_component
    d.eV d.action d.module_moved r hr hm
  change (∃ C : Subgroup (ChapterB.baumann R0), C.Characteristic ∧ C ≠ ⊥ ∧
    (C.map (ChapterB.baumann R0).subtype).Normal) ∨ IsAlternatingBlock L 6 at h
  rw [hb] at h
  exact h

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl
