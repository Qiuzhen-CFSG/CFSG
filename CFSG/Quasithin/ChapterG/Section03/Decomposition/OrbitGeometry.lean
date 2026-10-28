module

public import CFSG.Quasithin.ChapterG.Section03.Source
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.Completion

/-!
# Canonical orbit geometry for G.3.1

The root groups are intrinsic TI-subgroups of the finite group `G`, and
conjugate centers give root groups of equal order. I.6.2(1) therefore turns
one-sided fixation of centers into commutation and mutual fixation. If two
centers move each other, two root elements carry one center to the other.
Consequently distinct generated-group orbits centralize each other's spans
and generated subgroups.

The orbit family is finite, covers the original orbit, and is permuted
transitively by `G`. Conjugation here uses normality inside `G`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, G.3.1, printed pp. 337--338 (PDF pp. 348--349).
-/

@[expose] public section

open BinaryLinear BinaryTransvectionGroups
open CFSG.Quasithin.ChapterI.Section06To08
namespace CFSG.Quasithin.ChapterG.Section03.DecompositionProof
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (GL V)}

private theorem root_normalizer_of_fixed (g : G) (x : V) (hx : g.val x = x) :
    g ∈ Subgroup.normalizer (((rootGroup G x).subgroupOf G : Subgroup G) : Set G) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro t
  constructor
  · intro ht
    change g.val * t.val * g.val⁻¹ ∈ rootGroup G x
    simpa only [hx] using conjugate_mem_rootGroup (t := t.val) g.property ht
  · intro ht
    have hx' : g.val⁻¹ x = x := by
      apply g.val.injective
      simpa using hx.symm
    have hh := conjugate_mem_rootGroup (G.inv_mem g.property) ht
    change g.val⁻¹ * (g.val * t.val * g.val⁻¹) * (g.val⁻¹)⁻¹ ∈
      rootGroup G (g.val⁻¹ x) at hh
    change t.val ∈ rootGroup G x
    simpa [hx', mul_assoc] using hh

theorem intrinsic_root_ti (x : V) : IsTISubgroup ((rootGroup G x).subgroupOf G) := by
  apply (isTISubgroup_iff _).mpr
  intro g hg t ht hgt
  have hgx : g.val x ≠ x := fun he => hg (root_normalizer_of_fixed g x he)
  have hd := rootGroup_disjoint G hgx
  have hone : g.val * t.val * g.val⁻¹ = 1 :=
    hd.le_bot ⟨conjugate_mem_rootGroup g.property ht, hgt⟩
  apply Subtype.ext
  have hh := congrArg (fun z : GL V => g.val⁻¹ * z * g.val) hone
  simpa [mul_assoc] using hh

theorem intrinsic_root_card (x : V) :
    Nat.card ((rootGroup G x).subgroupOf G) = Nat.card (rootGroup G x) := by
  rw [← Subgroup.card_map_of_injective G.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le (rootGroup_le G x)]

theorem root_card_eq [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    {x y : V} (hx : x ∈ Δ) (hy : y ∈ Δ) :
    Nat.card ((rootGroup G x).subgroupOf G) =
      Nat.card ((rootGroup G y).subgroupOf G) := by
  obtain ⟨a, ha⟩ := h.orbit
  rw [ha] at hx hy
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  have he : (k.val * g.val⁻¹) (g.val a) = k.val a := by simp
  rw [intrinsic_root_card, intrinsic_root_card]
  change Nat.card (rootGroup G (g.val a)) = Nat.card (rootGroup G (k.val a))
  rw [← he, ← rootGroup_conjugate (G.mul_mem k.property (G.inv_mem g.property)),
    Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem roots_commute_of_fixed [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    {x y : V} (hx : x ∈ Δ) (hy : y ∈ Δ) (hne : x ≠ y)
    (hfix : ∀ t ∈ rootGroup G y, t x = x) :
    ∀ s ∈ rootGroup G x, ∀ t ∈ rootGroup G y, Commute s t := by
  let X := (rootGroup G x).subgroupOf G
  let Y := (rootGroup G y).subgroupOf G
  let := rootGroup_elementaryAbelian G x
  let := rootGroup_elementaryAbelian G y
  let := IsElementaryAbelian.subgroupOf (p := 2) (rootGroup_le G x)
  let := IsElementaryAbelian.subgroupOf (p := 2) (rootGroup_le G y)
  have hd : Disjoint Y X := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro t ht
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact (rootGroup_disjoint G hne.symm).le_bot ht
  have hfull : Y ⊓ Subgroup.normalizer (X : Set G) = Y := by
    apply inf_eq_left.mpr
    intro t ht
    exact root_normalizer_of_fixed t x (hfix t.val ht)
  have hc := ti_pair_commute_of_full_normalizer Y X hd (intrinsic_root_ti y)
    (intrinsic_root_ti x) (root_card_eq h hy hx) hfull
  intro s hs t ht
  exact congrArg Subtype.val (hc (show (⟨t, ht.1⟩ : G) ∈ Y from ht)
    (⟨s, hs.1⟩ : G) hs)


theorem root_ne_bot [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    {x : V} (hx : x ∈ Δ) : rootGroup G x ≠ ⊥ := by
  intro hb
  have hq : rootQuotientImage G x = ⊥ := by simp [rootQuotientImage, hb]
  have hr := h.rank_gt_one x hx
  rw [hq, Group.rank_eq_zero] at hr
  omega

theorem fixed_symm [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    {x y : V} (hx : x ∈ Δ) (hy : y ∈ Δ) (hne : x ≠ y)
    (hfix : ∀ t ∈ rootGroup G y, t x = x) :
    ∀ s ∈ rootGroup G x, s y = y := by
  intro s hs
  by_contra hsy
  obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (root_ne_bot h hy)
  have hc := roots_commute_of_fixed h hx hy hne hfix s hs t.val t.property
  have he : s * t.val * s⁻¹ = t.val := by rw [hc.eq, mul_inv_cancel_right]
  have hm := conjugate_mem_rootGroup hs.1 t.property
  rw [he] at hm
  have ht1 : t.val = 1 := (rootGroup_disjoint G hsy).le_bot ⟨hm, t.property⟩
  exact ht (Subtype.ext ht1)

theorem block_eq_orbit {Δ : Set V} (i : OrbitBlock G Δ) {x : V} (hx : x ∈ i.val) :
    i.val = MulAction.orbit (generated G Δ) x := by
  obtain ⟨a, _, hi⟩ := i.property
  rw [hi] at hx ⊢
  exact (MulAction.orbit_eq_iff.mpr hx).symm

theorem block_eq_of_mem {Δ : Set V} {i j : OrbitBlock G Δ} {x : V}
    (hi : x ∈ i.val) (hj : x ∈ j.val) : i = j :=
  Subtype.ext ((block_eq_orbit i hi).trans (block_eq_orbit j hj).symm)

theorem block_mem_smul {Δ : Set V} (i : OrbitBlock G Δ) {x : V} (hx : x ∈ i.val)
    (g : generated G Δ) : g.val x ∈ i.val := by
  rw [block_eq_orbit i hx]
  exact MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩

theorem root_cross_fix [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    {i j : OrbitBlock G Δ} (hij : i ≠ j) {x y : V} (hx : x ∈ i.val) (hy : y ∈ j.val) :
    ∀ t ∈ rootGroup G y, t x = x := by
  have hxΔ := block_subset h i hx
  have hyΔ := block_subset h j hy
  have hxy : x ≠ y := fun he => hij (block_eq_of_mem (he ▸ hx) hy)
  by_contra hn
  push Not at hn
  obtain ⟨t, ht, htx⟩ := hn
  have hs : ¬ ∀ s ∈ rootGroup G x, s y = y := by
    intro hs
    exact htx (fixed_symm h hyΔ hxΔ hxy.symm hs t ht)
  push Not at hs
  obtain ⟨s, hs, hsy⟩ := hs
  have htx' : t x = x + y := by
    rcases (mem_centerLine_iff y (t x - x)).mp (ht.2.2 x) with hh | hh
    · exact (htx (sub_eq_zero.mp hh)).elim
    · exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm y x)
  have hsy' : s y = y + x := by
    rcases (mem_centerLine_iff x (s y - y)).mp (hs.2.2 y) with hh | hh
    · exact (hsy (sub_eq_zero.mp hh)).elim
    · exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm x y)
  have hsx : s x = x := hs.2.1 x (Submodule.mem_span_singleton_self x)
  have hxx : x + x = 0 := by
    calc
      x + x = ((1 : ZMod 2) + 1) • x := by rw [add_smul, one_smul]
      _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]
  have hst : (s * t) x = y := by
    rw [LinearEquiv.mul_apply, htx', map_add, hsx, hsy']
    simpa [add_assoc, add_comm, add_left_comm] using congrArg (y + ·) hxx
  have hyi := block_mem_smul i hx
    (⟨s * t, (generated G Δ).mul_mem
      (rootGroup_le_generated G hxΔ hs) (rootGroup_le_generated G hyΔ ht)⟩ : generated G Δ)
  rw [hst] at hyi
  exact hij (block_eq_of_mem hyi hy)


theorem blocks_cross_fix [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    {i j : OrbitBlock G Δ} (hij : i ≠ j) :
    ∀ g ∈ blockGroup G Δ i, ∀ v ∈ blockSpace G Δ j, g v = v := by
  have hg : blockGroup G Δ i ≤ pointwiseFixer (blockSpace G Δ j) := by
    apply iSup_le
    intro x
    apply iSup_le
    intro hx t ht v hv
    have hW : blockSpace G Δ j ≤ (t.toLinearMap - LinearMap.id).ker := by
      apply Submodule.span_le.mpr
      intro y hy
      exact sub_eq_zero.mpr (root_cross_fix h hij.symm hy hx t ht)
    exact sub_eq_zero.mp (hW hv)
  exact hg

theorem blocks_commute [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    {i j : OrbitBlock G Δ} (hij : i ≠ j) :
    ∀ s ∈ blockGroup G Δ i, ∀ t ∈ blockGroup G Δ j, Commute s t := by
  have hc : blockGroup G Δ i ≤ Subgroup.centralizer (blockGroup G Δ j : Set (GL V)) := by
    apply iSup_le
    intro x
    apply iSup_le
    intro hx s hs
    have ht : blockGroup G Δ j ≤ Subgroup.centralizer ({s} : Set (GL V)) := by
      apply iSup_le
      intro y
      apply iSup_le
      intro hy t ht
      have hxy : x ≠ y := fun he => hij (block_eq_of_mem (he ▸ hx) hy)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((roots_commute_of_fixed h (block_subset h i hx) (block_subset h j hy)
          hxy (root_cross_fix h hij hx hy) s hs t ht).symm)
    intro t ht'
    exact (Subgroup.mem_centralizer_singleton_iff.mp (ht ht'))
  intro s hs t ht
  exact (hc hs t ht).symm

theorem finite_blocks [Finite G] {Δ : Set V} (h : Hypotheses G Δ) :
    Finite (OrbitBlock G Δ) := by
  have hΔ : Δ.Finite := by
    obtain ⟨a, rfl⟩ := h.orbit
    exact Finite.finite_mulAction_orbit a
  let : Finite Δ := hΔ.to_subtype
  let f : Δ → OrbitBlock G Δ := fun x =>
    ⟨MulAction.orbit (generated G Δ) x.val, x.val, x.property, rfl⟩
  apply Finite.of_surjective f
  intro i
  obtain ⟨x, hx, hi⟩ := i.property
  exact ⟨⟨x, hx⟩, Subtype.ext hi.symm⟩

theorem blocks_span [Finite G] {Δ : Set V} (h : Hypotheses G Δ) :
    (⨆ i : OrbitBlock G Δ, blockSpace G Δ i) = Submodule.span (ZMod 2) Δ := by
  apply le_antisymm
  · exact iSup_le fun i => Submodule.span_mono (block_subset h i)
  · apply Submodule.span_le.mpr
    intro x hx
    let i : OrbitBlock G Δ := ⟨MulAction.orbit (generated G Δ) x, x, hx, rfl⟩
    exact (le_iSup (blockSpace G Δ) i)
      (Submodule.subset_span (MulAction.mem_orbit_self x))

theorem blocks_join [Finite G] {Δ : Set V} (h : Hypotheses G Δ) :
    (⨆ i : OrbitBlock G Δ, blockGroup G Δ i) = generated G Δ := by
  apply le_antisymm
  · exact iSup_le (blockGroup_le_generated h)
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    let i : OrbitBlock G Δ := ⟨MulAction.orbit (generated G Δ) x, x, hx, rfl⟩
    exact (rootGroup_le_generated G (MulAction.mem_orbit_self x)).trans
      (le_iSup (blockGroup G Δ) i)

theorem exists_move [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    {x y : V} (hx : x ∈ Δ) (hy : y ∈ Δ) : ∃ g : G, g.val x = y := by
  obtain ⟨a, ha⟩ := h.orbit
  rw [ha] at hx hy
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  refine ⟨k * g⁻¹, ?_⟩
  change (k.val * g.val⁻¹) (g.val a) = k.val a
  simp

theorem generated_conj_mem [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    (g : G) {k : GL V} (hk : k ∈ generated G Δ) :
    g.val * k * g.val⁻¹ ∈ generated G Δ := by
  exact (generated_normal G Δ h.stable).conj_mem
    (⟨k, generated_le G Δ hk⟩ : G) hk g

theorem orbit_image [Finite G] {Δ : Set V} (h : Hypotheses G Δ) (g : G) (x : V) :
    g.val '' MulAction.orbit (generated G Δ) x =
      MulAction.orbit (generated G Δ) (g.val x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hz
    refine MulAction.mem_orbit_iff.mpr
      ⟨⟨g.val * k.val * g.val⁻¹, generated_conj_mem h g k.property⟩, ?_⟩
    change (g.val * k.val * g.val⁻¹) (g.val x) = g.val (k.val x)
    simp
  · intro hy
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    refine ⟨g.val⁻¹ (k.val (g.val x)), ?_, ?_⟩
    · refine MulAction.mem_orbit_iff.mpr
        ⟨⟨g.val⁻¹ * k.val * g.val, generated_conj_mem h g⁻¹ k.property⟩, rfl⟩
    · exact g.val.apply_symm_apply _

theorem blocks_conjugate [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    (i j : OrbitBlock G Δ) : ∃ g : G, g.val '' i.val = j.val := by
  obtain ⟨x, hx, hi⟩ := i.property
  obtain ⟨y, hy, hj⟩ := j.property
  obtain ⟨g, hg⟩ := exists_move h hx hy
  exact ⟨g, by rw [hi, hj, orbit_image h, hg]⟩

theorem block_spaces_conjugate [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    (i j : OrbitBlock G Δ) : ∃ g ∈ G,
    (blockSpace G Δ i).map g.toLinearMap = blockSpace G Δ j := by
  obtain ⟨g, hg⟩ := blocks_conjugate h i j
  refine ⟨g.val, g.property, ?_⟩
  simp only [blockSpace, Submodule.map_span, LinearEquiv.coe_coe, hg]

theorem generated_image (g : G) (Γ : Set V) :
    (generated G Γ).map (MulAut.conj g.val).toMonoidHom = generated G (g.val '' Γ) := by
  simp only [generated, Subgroup.map_iSup, rootGroup_conjugate g.property]
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    exact le_iSup_of_le (g.val x) (le_iSup_of_le ⟨x, hx, rfl⟩ le_rfl)
  · apply iSup_le
    intro y
    apply iSup_le
    rintro ⟨x, hx, rfl⟩
    exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

theorem block_groups_conjugate [Finite G] {Δ : Set V} (h : Hypotheses G Δ)
    (i j : OrbitBlock G Δ) : ∃ g ∈ G,
    (blockGroup G Δ i).map (MulAut.conj g).toMonoidHom = blockGroup G Δ j := by
  obtain ⟨g, hg⟩ := blocks_conjugate h i j
  exact ⟨g.val, g.property, by rw [blockGroup, generated_image, hg]; rfl⟩

end CFSG.Quasithin.ChapterG.Section03.DecompositionProof
