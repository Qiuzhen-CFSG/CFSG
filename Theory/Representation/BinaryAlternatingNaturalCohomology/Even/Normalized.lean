module

public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even.Displacement

/-!
# Point-stabilizer-normalized alternating natural-module cocycles

In even degree at least six, a cocycle vanishing on a point stabilizer is a
scalar multiple of the coordinate displacement. This gives the normalized
calculation for the binary natural modules of A₆ and A₈.

Normalization makes each value depend only on the image of the base point.
The value at a moving element is fixed by the stabilizer of the base point and
its image. A representative of this value is genuinely fixed, since a constant
displacement vanishes at the base point. Transitivity on the remaining
coordinates, followed by the augmentation equation, identifies the fixed space
as the coordinate-pair line. Transitivity of the point stabilizer on the other
points then propagates this one value to the entire cocycle.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §B.3 and Lemma I.1.6(1), printed p.408 (PDF p.419),
citing Exercise 6.3 of Aschbacher, *Finite Group Theory* (1986).
-/

@[expose] public section

open Representation Representation.OneCohomology Equiv Equiv.Perm
namespace BinaryPermutation
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

private theorem supported_transitive (s : Finset Ω) (hs : 3 ≤ s.card)
    (i j : s) : ∃ g : alternatingGroup Ω, g.val i = j ∧
      ∀ k, k ∉ s → g.val k = k := by
  let := alternatingGroup.isPretransitive_of_three_le_card s (by simpa using hs)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup s) i j
  refine ⟨alternatingGroup.ofSubtype s g, ?_, ?_⟩
  · change Equiv.Perm.ofSubtype g.val i = j
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ i.property]
    exact congrArg Subtype.val hg
  · intro k hk
    exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hk

private theorem normalized_same_image (b : Ω)
    (f : cocycles (alternatingNaturalRepresentation Ω))
    (hz : ∀ g : alternatingGroup Ω, g.val b = b → f.val g = 0)
    (g h : alternatingGroup Ω) (he : g.val b = h.val b) : f.val g = f.val h := by
  have hfix : (h⁻¹ * g).val b = b := by
    change h.val.symm (g.val b) = b
    rw [he, Equiv.symm_apply_apply]
  have hc := f.property h (h⁻¹ * g)
  simpa [hz _ hfix] using hc

private theorem normalized_pair_fixed (b : Ω)
    (f : cocycles (alternatingNaturalRepresentation Ω))
    (hz : ∀ g : alternatingGroup Ω, g.val b = b → f.val g = 0)
    (g h : alternatingGroup Ω) (hb : h.val b = b) (hc : h.val (g.val b) = g.val b) :
    alternatingNaturalRepresentation Ω h (f.val g) = f.val g := by
  have he := normalized_same_image b f hz (h * g) g hc
  rw [f.property, hz h hb, add_zero] at he
  exact he

private theorem fixed_representative (b : Ω) (g : alternatingGroup Ω)
    (hb : g.val b = b) (w : Full Ω)
    (hw : deletedRepresentation Ω g.val ((constants Ω).mkQ w) = (constants Ω).mkQ w) :
    representation Ω g.val w = w := by
  have hd : representation Ω g.val w - w ∈ constants Ω := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (constants Ω).mkQ (representation Ω g.val w - w) = 0
    rw [map_sub, ← deletedRepresentation_mk, hw, sub_self]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd
  have hzero : c = 0 := by
    have h := congrFun hc b
    have hi : g.val.symm b = b := (Equiv.symm_apply_eq _).mpr hb.symm
    simpa [allOne, hi] using h
  rw [hzero, zero_smul] at hc
  exact sub_eq_zero.mp hc.symm

private theorem pair_fixed_line (hcard : 5 ≤ Fintype.card Ω)
    (heven : Even (Fintype.card Ω)) (b c : Ω) (hbc : b ≠ c)
    (v : natural Ω)
    (hv : ∀ g : alternatingGroup Ω, g.val b = b → g.val c = c →
      alternatingNaturalRepresentation Ω g v = v) :
    ∃ a : ZMod 2, (v : Deleted Ω) =
      a • (constants Ω).mkQ (Pi.single c 1 - Pi.single b 1) := by
  classical
  obtain ⟨w, hw, hwv⟩ := v.property
  let s := (Finset.univ.erase b).erase c
  have hs : 3 ≤ s.card := by
    have hc_mem : c ∈ Finset.univ.erase b := by simp [hbc.symm]
    dsimp [s]
    rw [Finset.card_erase_of_mem hc_mem,
      Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]
    omega
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  have hconst (i : Ω) (hi : i ∈ s) : w i = w d := by
    obtain ⟨g, hgi, hgfix⟩ := supported_transitive s hs ⟨i, hi⟩ ⟨d, hd⟩
    have hb : g.val b = b := hgfix b (by simp [s])
    have hc : g.val c = c := hgfix c (by simp [s])
    have he : deletedRepresentation Ω g.val ((constants Ω).mkQ w) =
        (constants Ω).mkQ w := by
      rw [hwv]
      exact congrArg Subtype.val (hv g hb hc)
    have hh := congrFun (fixed_representative b g hb w he) d
    have hi' : g.val.symm d = i := (Equiv.symm_apply_eq _).mpr hgi.symm
    simpa [hi'] using hh
  let u := w - w d • allOne Ω
  have hu : u ∈ core Ω := (core Ω).sub_mem hw
    ((constants_le_core_iff Ω).mpr heven
      ((constants Ω).smul_mem _ (Submodule.subset_span (by simp))))
  have hu0 (i : Ω) (hi : i ∈ s) : u i = 0 := by
    change w i - w d * 1 = 0
    rw [hconst i hi, mul_one, sub_self]
  have hu_eq : u = Pi.single b (u b) + Pi.single c (u c) := by
    funext i
    by_cases hib : i = b
    · subst i
      simp [hbc]
    by_cases hic : i = c
    · subst i
      simp [hbc.symm]
    · simp [hib, hic, hu0 i (by simp [s, hib, hic])]
  have hsum : u b + u c = 0 := by
    change augmentation Ω u = 0 at hu
    rw [hu_eq] at hu
    simpa [augmentation, Finset.sum_add_distrib] using hu
  have hcb : u c = u b := by
    have := eq_neg_of_add_eq_zero_right hsum
    simpa only [CharTwo.neg_eq] using this
  have hu_form : u = u b • (Pi.single c 1 - Pi.single b 1) := by
    calc
      u = Pi.single b (u b) + Pi.single c (u c) := hu_eq
      _ = u b • (Pi.single c 1 - Pi.single b 1) := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
          Pi.single_apply, hcb, CharTwo.sub_eq_add]
        split_ifs <;> simp [CharTwo.add_self_eq_zero]
  refine ⟨u b, ?_⟩
  rw [← hwv, ← map_smul, ← hu_form]
  change (constants Ω).mkQ w = (constants Ω).mkQ (w - w d • allOne Ω)
  rw [map_sub]
  have hc0 : (constants Ω).mkQ (w d • allOne Ω) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (constants Ω).smul_mem _ (Submodule.subset_span (by simp))
  rw [hc0, sub_zero]

private theorem normalized_determined (hcard : 4 ≤ Fintype.card Ω) (b : Ω)
    (f F : cocycles (alternatingNaturalRepresentation Ω))
    (hf : ∀ g : alternatingGroup Ω, g.val b = b → f.val g = 0)
    (hF : ∀ g : alternatingGroup Ω, g.val b = b → F.val g = 0)
    (t : alternatingGroup Ω) (ht : t.val b ≠ b) (he : f.val t = F.val t) : f = F := by
  apply Subtype.ext
  funext g
  by_cases hg : g.val b = b
  · rw [hf g hg, hF g hg]
  let s := Finset.univ.erase b
  have hs : 3 ≤ s.card := by
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]
    omega
  obtain ⟨h, hh, hfix⟩ := supported_transitive s hs
    ⟨t.val b, by simp [s, ht]⟩ ⟨g.val b, by simp [s, hg]⟩
  have hb : h.val b = b := hfix b (by simp [s])
  have himage : (h * t).val b = g.val b := hh
  rw [← normalized_same_image b f hf (h * t) g himage,
    ← normalized_same_image b F hF (h * t) g himage,
    f.property, F.property, he, hf h hb, hF h hb]

/-- A point-stabilizer-normalized cocycle in even degree at least six is a
scalar multiple of the coordinate displacement. -/
theorem alternatingNatural_normalized_eq_coordinate_of_even
    (hcard : 5 ≤ Fintype.card Ω) (heven : Even (Fintype.card Ω)) (b : Ω)
    (f : cocycles (alternatingNaturalRepresentation Ω))
    (hz : ∀ g : alternatingGroup Ω, g.val b = b → f.val g = 0) :
    ∃ a : ZMod 2, f = a • naturalCoordinateCocycle Ω b := by
  have hs : 0 < (Finset.univ.erase b).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hs
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  let := alternatingGroup.isPretransitive_of_three_le_card Ω (by
    rw [Nat.card_eq_fintype_card]; omega)
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq (alternatingGroup Ω) b c
  change t.val b = c at ht
  obtain ⟨a, ha⟩ := pair_fixed_line hcard heven b c hcb.symm (f.val t) (by
    intro g hb hc
    apply normalized_pair_fixed b f hz t g hb
    simpa only [ht] using hc)
  refine ⟨a, normalized_determined (by omega) b f (a • naturalCoordinateCocycle Ω b)
    hz ?_ t (by simpa only [ht] using hcb) ?_⟩
  · intro g hg
    change a • (naturalCoordinateCocycle Ω b).val g = 0
    rw [naturalCoordinateCocycle_apply_of_fixed Ω b g hg, smul_zero]
  · apply Subtype.ext
    change (f.val t : Deleted Ω) = a • (constants Ω).mkQ
      (representation Ω t.val (Pi.single b 1) - Pi.single b 1)
    have hp : representation Ω t.val (Pi.single b 1) = Pi.single c 1 := by
      funext i
      simp [Pi.single_apply, Equiv.symm_apply_eq, ht]
    rw [hp]
    exact ha

/-- The normalized cocycle calculation for the two even natural modules in
Aschbacher--Smith I.1.6(1). -/
theorem alternatingNatural_normalized_eq_coordinate (n : ℕ) (hn : n = 6 ∨ n = 8)
    (b : Fin n) (f : cocycles (alternatingNaturalRepresentation (Fin n)))
    (hzero : ∀ g : alternatingGroup (Fin n), g.val b = b → f.val g = 0) :
    ∃ a : ZMod 2, f = a • naturalCoordinateCocycle (Fin n) b := by
  apply alternatingNatural_normalized_eq_coordinate_of_even _ _ b f hzero
  · simpa only [Fintype.card_fin] using (show 5 ≤ n by omega)
  · rcases hn with rfl | rfl <;> decide

end BinaryPermutation
