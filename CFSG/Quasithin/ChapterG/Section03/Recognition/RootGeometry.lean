module

public import CFSG.Quasithin.ChapterG.Section03.Source
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.Completion
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Root geometry for the recognition in G.3.1

The root groups are restricted to the intrinsic finite group before applying
I.6.2(1). Distinct centers give disjoint subgroups; conjugation proves the TI
condition and equal orders on a single orbit. Consequently fixation between
two centers is symmetric.

The radical of the span of the ambient orbit is normal inside `G` and is a
2-group. The source quotient-rank hypothesis therefore forces every root
group to move another center. Two mutually moving transvections conjugate
the centers, so that they lie in the same canonical block. In particular every
block span is finite dimensional and has dimension at least two, even when
the ambient vector space is infinite dimensional.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, G.3.1, printed pp.337--338; I.6.2(1), pp.424--425.
-/

@[expose] public section

open BinaryLinear BinaryTransvectionGroups
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterI.Section06To08
namespace CFSG.Quasithin.ChapterG.Section03
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

abbrev rootIn (G : Subgroup (GL V)) (x : V) : Subgroup G :=
  (rootGroup G x).subgroupOf G

theorem rootIn_conjugate (G : Subgroup (GL V)) (g : G) (x : V) :
    (rootIn G x).map (MulAut.conj g).toMonoidHom = rootIn G (g.val x) := by
  apply le_antisymm
  · rintro t ⟨s, hs, rfl⟩
    exact conjugate_mem_rootGroup g.property hs
  · intro t ht
    change t.val ∈ rootGroup G (g.val x) at ht
    refine ⟨g⁻¹ * t * g, ?_, ?_⟩
    · change g.val⁻¹ * t.val * g.val ∈ rootGroup G x
      simpa only [inv_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using
        conjugate_mem_rootGroup (G.inv_mem g.property) ht
    · change g * (g⁻¹ * t * g) * g⁻¹ = t
      group

theorem rootIn_disjoint (G : Subgroup (GL V)) {x y : V} (hxy : x ≠ y) :
    Disjoint (rootIn G x) (rootIn G y) := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro t ht
  exact Subtype.ext ((rootGroup_disjoint G hxy).le_bot ht)

theorem rootIn_isTI (G : Subgroup (GL V)) (x : V) : IsTISubgroup (rootIn G x) := by
  apply (isTISubgroup_iff _).mpr
  intro g hg t ht hconj
  have hx : g.val x ≠ x := by
    intro h
    apply hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (rootIn G x).map (MulAut.conj g).toMonoidHom = rootIn G x
    rw [rootIn_conjugate, h]
  have ht' : g * t * g⁻¹ ∈ rootIn G (g.val x) := conjugate_mem_rootGroup g.property ht
  have h1 : g * t * g⁻¹ = 1 := (rootIn_disjoint G hx).le_bot ⟨ht', hconj⟩
  simpa [mul_assoc] using congrArg (fun a : G => g⁻¹ * a * g) h1


theorem Hypotheses.rootIn_card_eq {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) {x y : V} (hx : x ∈ Δ) (hy : y ∈ Δ) :
    Nat.card (rootIn G x) = Nat.card (rootIn G y) := by
  obtain ⟨a, rfl⟩ := h.orbit
  have hyx : y ∈ MulAction.orbit G x := by
    rw [MulAction.orbit_eq_iff.mpr hx]
    exact hy
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hyx
  change g.val x = y at hg
  rw [← hg, ← rootIn_conjugate G g x]
  exact Nat.card_congr ((MulAut.conj g).subgroupMap (rootIn G x)).toEquiv

theorem Hypotheses.rootIn_not_le_twoCore {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) {x : V} (hx : x ∈ Δ) : ¬ rootIn G x ≤ pCore 2 G := by
  intro hle
  have hb : rootQuotientImage G x = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [QuotientGroup.ker_mk'] using hle
  have hr : Group.rank (rootQuotientImage G x) = 0 := by
    rw [hb]
    exact Group.rank_eq_zero _
  have := h.rank_gt_one x hx
  omega

theorem Hypotheses.rootIn_ne_bot {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) {x : V} (hx : x ∈ Δ) : rootIn G x ≠ ⊥ := by
  intro he
  exact h.rootIn_not_le_twoCore hx (he ▸ bot_le)

theorem Hypotheses.rootGroups_commute_of_fixed {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (h : Hypotheses G Δ) {x y : V} (hx : x ∈ Δ) (hy : y ∈ Δ)
    (hfix : ∀ a ∈ rootGroup G y, a x = x) :
    ∀ a ∈ rootGroup G x, ∀ b ∈ rootGroup G y, Commute a b := by
  let := rootGroup_elementaryAbelian G x
  let := rootGroup_elementaryAbelian G y
  let : IsElementaryAbelian 2 (rootIn G x) :=
    IsElementaryAbelian.subgroupOf (rootGroup_le G x)
  let : IsElementaryAbelian 2 (rootIn G y) :=
    IsElementaryAbelian.subgroupOf (rootGroup_le G y)
  by_cases he : x = y
  · subst y
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm (⟨a, ha⟩ : rootGroup G x) ⟨b, hb⟩)
  have hn : rootIn G y ⊓ Subgroup.normalizer (rootIn G x : Set G) = rootIn G y := by
    apply inf_eq_left.mpr
    intro b hb
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (rootIn G x).map (MulAut.conj b).toMonoidHom = rootIn G x
    rw [rootIn_conjugate, hfix b.val hb]
  have hc := ti_pair_commute_of_full_normalizer (rootIn G y) (rootIn G x)
    (rootIn_disjoint G (Ne.symm he)) (rootIn_isTI G y) (rootIn_isTI G x)
    (h.rootIn_card_eq hy hx) hn
  intro a ha b hb
  exact congrArg Subtype.val (hc (show (⟨b, hb.1⟩ : G) ∈ rootIn G y from hb)
    (⟨a, ha.1⟩ : G) ha)

theorem Hypotheses.fixed_rootGroup_symm {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (h : Hypotheses G Δ) {x y : V} (hx : x ∈ Δ) (hy : y ∈ Δ)
    (hfix : ∀ a ∈ rootGroup G y, a x = x) :
    ∀ a ∈ rootGroup G x, a y = y := by
  intro a ha
  by_contra hay
  have hd := rootIn_disjoint G hay
  have hc := h.rootGroups_commute_of_fixed hx hy hfix
  apply h.rootIn_ne_bot hy
  apply bot_unique
  intro b hb
  apply hd.le_bot
  refine ⟨?_, hb⟩
  have hc' : a * b.val * a⁻¹ = b.val := by
    rw [show a * b.val = b.val * a from (hc a ha b.val hb).eq]
    simp [mul_assoc]
  change b.val ∈ rootGroup G (a y)
  rw [← hc']
  exact conjugate_mem_rootGroup ha.1 hb

theorem Hypotheses.le_parabolic_span {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) : G ≤ parabolic (Submodule.span (ZMod 2) Δ) := by
  have hs (g : GL V) (hg : g ∈ G) :
      Submodule.span (ZMod 2) Δ ≤ (Submodule.span (ZMod 2) Δ).comap g.toLinearMap :=
    Submodule.span_le.mpr fun x hx => Submodule.subset_span (h.stable g hg x hx)
  intro g hg v
  constructor
  · intro hv
    have := hs g⁻¹ (G.inv_mem hg) hv
    simpa only [Submodule.mem_comap, LinearEquiv.coe_coe,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using this
  · exact fun hv => hs g hg hv

theorem Hypotheses.radical_span_le_twoCore {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (h : Hypotheses G Δ) :
    (radical (Submodule.span (ZMod 2) Δ)).subgroupOf G ≤ pCore 2 G := by
  let D := (radical (Submodule.span (ZMod 2) Δ)).subgroupOf G
  have hn : D.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (h.le_parabolic_span.trans (parabolic_le_normalizer _))
  let : IsElementaryAbelian 2 D := elementaryAbelian_of_le_radical
    (G.subtype.comp D.subtype) (Subtype.val_injective.comp Subtype.val_injective)
    (Submodule.span (ZMod 2) Δ) (fun a => a.property)
  exact le_sSup ⟨hn, IsElementaryAbelian.isPGroup 2 D⟩

theorem Hypotheses.root_mem_twoCore_of_fixes_centers {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (h : Hypotheses G Δ) {x : V} (hx : x ∈ Δ) {a : G}
    (ha : a ∈ rootIn G x) (hfix : ∀ y ∈ Δ, a.val y = y) : a ∈ pCore 2 G := by
  apply h.radical_span_le_twoCore
  refine ⟨?_, ?_⟩
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy => exact hfix y hy
    | zero => exact a.val.map_zero
    | add v w _ _ hv hw => simp only [map_add, hv, hw]
    | smul c v _ hv => simp only [map_smul, hv]
  · intro v
    exact (Submodule.span_mono (Set.singleton_subset_iff.mpr hx)) (ha.2.2 v)

theorem Hypotheses.exists_moved_center {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (h : Hypotheses G Δ) {x : V} (hx : x ∈ Δ) :
    ∃ y ∈ Δ, ∃ a ∈ rootGroup G x, a y ≠ y := by
  by_contra hn
  push Not at hn
  apply h.rootIn_not_le_twoCore hx
  intro a ha
  exact h.root_mem_twoCore_of_fixes_centers hx ha (fun y hy => hn y hy a.val ha)

theorem root_move_eq_add {G : Subgroup (GL V)} {x y : V} {a : GL V}
    (ha : a ∈ rootGroup G x) (hmove : a y ≠ y) : a y = y + x := by
  have hd := (mem_centerLine_iff x (a y - y)).mp (ha.2.2 y)
  rcases hd with hd | hd
  · exact (hmove (sub_eq_zero.mp hd)).elim
  · exact (eq_add_of_sub_eq hd).trans (add_comm x y)

theorem Hypotheses.same_orbit_of_moved {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (h : Hypotheses G Δ) {x y : V} (hx : x ∈ Δ) (hy : y ∈ Δ)
    {a : GL V} (ha : a ∈ rootGroup G x) (hmove : a y ≠ y) :
    y ∈ MulAction.orbit (generated G Δ) x := by
  have hb : ∃ b ∈ rootGroup G y, b x ≠ x := by
    by_contra hn
    push Not at hn
    exact hmove (h.fixed_rootGroup_symm hx hy hn a ha)
  obtain ⟨b, hb, hbx⟩ := hb
  refine MulAction.mem_orbit_iff.mpr
    ⟨⟨a * b, (generated G Δ).mul_mem (rootGroup_le_generated G hx ha)
      (rootGroup_le_generated G hy hb)⟩, ?_⟩
  change a (b x) = y
  rw [root_move_eq_add hb hbx, map_add,
    ha.2.1 x (Submodule.mem_span_singleton_self x), root_move_eq_add ha hmove]
  have hh : x + x = 0 := by
    have ht : (1 + 1 : ZMod 2) = 0 := by decide
    simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c => c • x) ht
  calc
    x + (y + x) = y + (x + x) := by abel
    _ = y := by rw [hh, add_zero]

theorem orbitBlock_finite {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (i : OrbitBlock G Δ) : i.val.Finite := by
  obtain ⟨x, _, hi⟩ := i.property
  rw [hi]
  exact Finite.finite_mulAction_orbit x

instance finiteDimensional_blockSpace {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (i : OrbitBlock G Δ) : FiniteDimensional (ZMod 2) (blockSpace G Δ i) :=
  Module.Finite.span_of_finite _ (orbitBlock_finite i)

theorem orbitBlock_eq_orbit {G : Subgroup (GL V)} {Δ : Set V}
    (i : OrbitBlock G Δ) {x : V} (hx : x ∈ i.val) :
    i.val = MulAction.orbit (generated G Δ) x := by
  obtain ⟨u, _, hi⟩ := i.property
  have hx' : x ∈ MulAction.orbit (generated G Δ) u := hi ▸ hx
  exact hi.trans (MulAction.orbit_eq_iff.mpr hx').symm

theorem Hypotheses.exists_moved_center_in_block {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (h : Hypotheses G Δ) (i : OrbitBlock G Δ) {x : V} (hx : x ∈ i.val) :
    ∃ y ∈ i.val, ∃ a ∈ rootGroup G x, a y ≠ y := by
  have hxΔ := block_subset h i hx
  obtain ⟨y, hy, a, ha, hay⟩ := h.exists_moved_center hxΔ
  refine ⟨y, ?_, a, ha, hay⟩
  rw [orbitBlock_eq_orbit i hx]
  exact h.same_orbit_of_moved hxΔ hy ha hay

theorem Hypotheses.block_dimension_ge_two {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (h : Hypotheses G Δ) (i : OrbitBlock G Δ) :
    2 ≤ Module.finrank (ZMod 2) (blockSpace G Δ i) := by
  obtain ⟨x, hxΔ, hix⟩ := i.property
  have hx : x ∈ i.val := hix ▸ MulAction.mem_orbit_self x
  obtain ⟨y, hy, a, ha, hay⟩ := h.exists_moved_center_in_block i hx
  have hyline : y ∉ centerLine x := by
    intro hyline
    exact hay (ha.2.1 y hyline)
  have hle : centerLine x ≤ blockSpace G Δ i :=
    Submodule.span_mono (Set.singleton_subset_iff.mpr hx)
  have hlt : centerLine x < blockSpace G Δ i := lt_of_le_of_ne hle (by
    intro he
    exact hyline (he ▸ Submodule.subset_span hy))
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_span_singleton (h.nonzero x hxΔ)] at hd
  exact hd

end CFSG.Quasithin.ChapterG.Section03
