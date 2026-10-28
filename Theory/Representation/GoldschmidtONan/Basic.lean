module

public import Theory.Representation.GoldschmidtONan.Defs
public import Mathlib.FieldTheory.Finiteness

/-!
# Fixed and moved spaces of Goldschmidt–O'Nan pairs

Odd-order averaging splits the binary space into its fixed and displacement
subspaces. Cyclicity and transitivity make the moved action regular, since a
point stabilizer then fixes every moved vector and faithfulness kills it.
Counting a regular orbit gives the order formula, and splitting gives the
common fixed spaces of all nonidentity elements of the cyclic subgroup.

These prove GLS, Number 2, Chapter C, equations (14.1)–(14.3), and the
stabilizer invariance used just before (14.4). Source:
`refs/KGroup/GLS2/ChapterC.tex`, Definition 14.1 and Proposition 14.2.
The four alternatives of Proposition 14.2 are not asserted here.
-/

public section

open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
namespace Representation.GoldschmidtONan
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

/-- An odd-order binary action splits into its fixed and displacement subspaces. -/
theorem isCompl_fixed_moved_of_odd [Finite Y] (hodd : Odd (Nat.card Y)) :
    IsCompl (fixedSpace ρ Y) (displacementSpan ρ Y ⊤) := by
  classical
  let := Fintype.ofFinite Y
  have hcard : (Fintype.card Y : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [← Nat.card_eq_fintype_card, hk]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one, zero_add]
  let N : V →ₗ[ZMod 2] V := ∑ y : Y, ρ y
  have hN (v : V) : N v = ∑ y : Y, ρ y v := LinearMap.sum_apply _ _ _
  have hleft (y : Y) (v : V) : ρ y (N v) = N v := by
    simp only [hN, map_sum, ← Module.End.mul_apply, ← map_mul]
    change (∑ z : Y, ρ ((y * z : Y) : X) v) = ∑ z : Y, ρ z v
    exact (Group.mulLeft_bijective y).sum_comp (fun z : Y => ρ z v)
  have hright (y : Y) (v : V) : N (ρ y v) = N v := by
    simp only [hN, ← Module.End.mul_apply, ← map_mul]
    change (∑ z : Y, ρ ((z * y : Y) : X) v) = ∑ z : Y, ρ z v
    exact (Group.mulRight_bijective y).sum_comp (fun z : Y => ρ z v)
  have hfixed (v : V) (hv : v ∈ fixedSpace ρ Y) : N v = v := by
    rw [hN]
    simp only [show ∀ y : Y, ρ y v = v from hv, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hcard, one_smul]
  have hkill : displacementSpan ρ Y ⊤ ≤ N.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, v, _, rfl⟩
    change N (ρ y v - v) = 0
    rw [map_sub, hright ⟨y, hy⟩, sub_self]
  have hsub (v : V) : N v - v ∈ displacementSpan ρ Y ⊤ := by
    have hm : (∑ y : Y, (ρ y v - v)) ∈ displacementSpan ρ Y ⊤ :=
      Submodule.sum_mem _ fun y _ => Submodule.subset_span ⟨y, y.property, v, by trivial, rfl⟩
    rw [Finset.sum_sub_distrib, ← hN, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (ZMod 2), hcard, one_smul] at hm
    exact hm
  apply isCompl_iff.mpr
  constructor
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro v hv
    exact (Submodule.mem_bot (R := ZMod 2)).mpr
      ((hfixed v hv.1).symm.trans (hkill hv.2))
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    refine Submodule.mem_sup.mpr ⟨N v, fun y => hleft y v, v - N v, ?_, by abel⟩
    simpa only [neg_sub] using (displacementSpan ρ Y ⊤).neg_mem (hsub v)

/-- Odd-order averaging gives the fixed/moved direct sum (14.2). -/
theorem Input.split [Finite X] (h : Input ρ Y) :
    IsCompl (fixedSpace ρ Y) (displacementSpan ρ Y ⊤) :=
  isCompl_fixed_moved_of_odd h.odd

/-- A nontrivial faithful actor has a nonzero moved space. -/
theorem Input.moved_ne_bot (h : Input ρ Y) : displacementSpan ρ Y ⊤ ≠ ⊥ := by
  intro he
  apply h.nontrivial
  apply le_antisymm ?_ bot_le
  intro y hy
  apply Subgroup.mem_bot.mpr
  apply h.faithful
  ext v
  have hv : ρ y v - v ∈ displacementSpan ρ Y ⊤ :=
    Submodule.subset_span ⟨y, hy, v, by trivial, rfl⟩
  rw [he, Submodule.mem_bot] at hv
  simpa using sub_eq_zero.mp hv

/-- Cyclic transitivity is regular: faithfulness rules out a point stabilizer. -/
theorem Input.regular [Finite X] (h : Input ρ Y)
    (v : V) (hv : v ∈ displacementSpan ρ Y ⊤) (hv0 : v ≠ 0)
    (w : V) (hw : w ∈ displacementSpan ρ Y ⊤) (hw0 : w ≠ 0) :
    ∃! y : Y, ρ y v = w := by
  let : IsCyclic Y := h.cyclic
  let : CommGroup Y := IsCyclic.commGroup
  obtain ⟨y, hy⟩ := h.transitive v hv hv0 w hw hw0
  refine ⟨y, hy, ?_⟩
  intro z hz
  apply Subtype.ext
  apply h.faithful
  apply LinearMap.ext
  intro u
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    (show u ∈ fixedSpace ρ Y ⊔ displacementSpan ρ Y ⊤ by
      rw [h.split.sup_eq_top]; trivial)
  rw [map_add, map_add, show ρ z a = a from ha z, show ρ y a = a from ha y]
  congr 1
  by_cases hb0 : b = 0
  · simp [hb0]
  obtain ⟨c, hc⟩ := h.transitive v hv hv0 b hb hb0
  have hcomm (d : Y) : ρ d (ρ c v) = ρ c (ρ d v) := by
    simp only [← Module.End.mul_apply, ← map_mul]
    exact congrArg (fun x : X => ρ x v) (congrArg Subtype.val (mul_comm d c))
  rw [← hc, hcomm, hcomm, hz, hy]

/-- Each element acts injectively on the given representation. -/
theorem action_injective (x : X) : Function.Injective (ρ x) := by
  intro v w he
  have hh := congrArg (ρ x⁻¹) he
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using hh

/-- The actor preserves its displacement subspace. -/
theorem moved_mem_action (y : Y) {v : V} (hv : v ∈ displacementSpan ρ Y ⊤) :
    ρ y v ∈ displacementSpan ρ Y ⊤ := by
  have hm := Submodule.mem_map_of_mem (f := ρ y) hv
  rwa [displacementSpan_map_of_normalized ρ Y y
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Y.le_normalizer y.property))] at hm

/-- Formula (14.3): the order of Y is the number of nonzero moved vectors. -/
theorem Input.card_eq [Finite X] [Finite V] (h : Input ρ Y) :
    Nat.card Y = 2 ^ Module.finrank (ZMod 2) (displacementSpan ρ Y ⊤) - 1 := by
  classical
  let D := displacementSpan ρ Y ⊤
  let : Nontrivial D := Submodule.nontrivial_iff_ne_bot.mpr h.moved_ne_bot
  obtain ⟨v, hv⟩ := exists_ne (0 : D)
  have hv0 : (v : V) ≠ 0 := fun he => hv (Subtype.ext he)
  let f : Y → {w : D // w ≠ 0} := fun y =>
    ⟨⟨ρ y v, moved_mem_action y v.property⟩, fun he =>
      hv0 (action_injective (ρ := ρ) (y : X) (by simpa using congrArg (fun w : D => (w : V)) he))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c d he
      have hf' : ρ c v = ρ d v := congrArg (fun w : {w : D // w ≠ 0} => (w.val : V)) he
      obtain ⟨x, hx, hu⟩ := h.regular v v.property hv0 (ρ d v)
        (moved_mem_action d v.property)
        (fun hd => hv0 (action_injective (ρ := ρ) (d : X) (by simpa using hd)))
      exact (hu c hf').trans (hu d rfl).symm
    · intro w
      obtain ⟨c, hc, _⟩ := h.regular v v.property hv0 w.val w.val.property
        (fun he => w.property (Subtype.ext he))
      exact ⟨c, Subtype.ext (Subtype.ext hc)⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  let := Fintype.ofFinite D
  let := Fintype.ofFinite {w : D // w ≠ 0}
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- A nontrivial odd cyclic faithful actor moves at least two binary dimensions. -/
theorem Input.moved_dimension_gt_one [Finite X] [Finite V] (h : Input ρ Y) :
    1 < Module.finrank (ZMod 2) (displacementSpan ρ Y ⊤) := by
  have hcard := h.card_eq
  have hgt := Y.one_lt_card_iff_ne_bot.mpr h.nontrivial
  by_contra hn
  have hd : Module.finrank (ZMod 2) (displacementSpan ρ Y ⊤) = 0 ∨
      Module.finrank (ZMod 2) (displacementSpan ρ Y ⊤) = 1 := by omega
  rcases hd with hd | hd <;> simp only [hd, pow_zero, pow_one] at hcard <;> omega

/-- Formula (14.1): the whole faithful module has dimension at least three. -/
theorem Input.dimension_ge_three [Finite X] [Finite V] (h : Input ρ Y) :
    3 ≤ Module.finrank (ZMod 2) V := by
  let : Nontrivial (fixedSpace ρ Y) := Submodule.nontrivial_iff_ne_bot.mpr h.fixed_nontrivial
  have hf := Module.finrank_pos (R := ZMod 2) (M := fixedSpace ρ Y)
  have hd := h.moved_dimension_gt_one
  have hs := Submodule.finrank_add_eq_of_isCompl h.split
  omega

/-- The fixed space is proper. -/
theorem Input.fixed_ne_top [Finite X] (h : Input ρ Y) : fixedSpace ρ Y ≠ ⊤ := by
  intro hf
  have hh := h.split.inf_eq_bot
  rw [hf, top_inf_eq] at hh
  exact h.moved_ne_bot hh

/-- The moved space is proper. -/
theorem Input.moved_ne_top [Finite X] (h : Input ρ Y) : displacementSpan ρ Y ⊤ ≠ ⊤ := by
  intro hd
  have hh := h.split.inf_eq_bot
  rw [hd, inf_top_eq] at hh
  exact h.fixed_nontrivial hh

/-- The two distinguished spaces are distinct. -/
theorem Input.fixed_ne_moved [Finite X] (h : Input ρ Y) :
    fixedSpace ρ Y ≠ displacementSpan ρ Y ⊤ := by
  intro he
  have hh := h.split.inf_eq_bot
  rw [← he, inf_idem] at hh
  exact h.fixed_nontrivial hh

/-- The fixed-space stabilizer preserves the moved space as well. -/
theorem Input.moved_map_of_fixed_map (h : Input ρ Y) (x : X)
    (hx : (fixedSpace ρ Y).map (ρ x) = fixedSpace ρ Y) :
    (displacementSpan ρ Y ⊤).map (ρ x) = displacementSpan ρ Y ⊤ :=
  displacementSpan_map_of_normalized ρ Y x (h.normal_in_stabilizer x hx)

/-- A nonidentity element of Y fixes no nonzero moved vector. -/
theorem Input.eq_zero_of_mem_moved_of_fixed [Finite X] (h : Input ρ Y) {y : Y} (hy : y ≠ 1)
    {v : V} (hv : v ∈ displacementSpan ρ Y ⊤) (hfix : ρ y v = v) : v = 0 := by
  by_contra hv0
  obtain ⟨x, hx, hu⟩ := h.regular v hv hv0 v hv hv0
  exact hy ((hu y hfix).trans (hu 1 (by simp)).symm)

/-- Every nonidentity element of Y has the same fixed space as Y, as in (14.3). -/
theorem Input.fixedSpace_zpowers [Finite X] (h : Input ρ Y) {y : X} (hy : y ∈ Y) (hne : y ≠ 1) :
    fixedSpace ρ (Subgroup.zpowers y) = fixedSpace ρ Y := by
  apply le_antisymm
  · intro v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ fixedSpace ρ Y ⊔ displacementSpan ρ Y ⊤ by
        rw [h.split.sup_eq_top]; trivial)
    have hfix : ρ y w = w := by
      have hf := hv ⟨y, Subgroup.mem_zpowers y⟩
      change ρ y (u + w) = u + w at hf
      rwa [map_add, (show ρ y u = u from hu ⟨y, hy⟩), add_right_inj] at hf
    have hw0 := h.eq_zero_of_mem_moved_of_fixed
      (y := ⟨y, hy⟩) (fun he => hne (congrArg Subtype.val he)) hw hfix
    simpa only [hw0, add_zero] using hu
  · intro v hv a
    exact hv ⟨a, (Subgroup.zpowers_le.mpr hy) a.property⟩

end Representation.GoldschmidtONan
