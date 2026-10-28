module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.Contracts
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover

/-!
# From finite seed-extension certificates to arbitrary Atlas elements

A left seed factorization of each Sylow element, together with its inverse,
refines the existing eighteen Sylow double cosets to seed double cosets.
Multiplying an adjoined element on either side by seed elements preserves the
extension. The three parabolic double cosets are discharged here; the other
fifteen require the independent explicit witnesses in `Contracts`.

A recovered Sylow conjugate has odd index. Lagrange transports the other two
witness orders to the literal extension. This proves the finite reduction,
not the unconditional obstruction, whose two certificate families remain open.
Source: the Parrott (1972), section 5, p.683 marking and `source/README.md`.
-/

public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions
open Subgroup ExceptionalParabolics

private theorem basePlaces_mem (t : Fin 18) :
    (0 : Fin 38) ∈ placePattern t ∧ (17 : Fin 38) ∈ placePattern t := by
  revert t
  decide +kernel

private theorem place_zero : place 0 = first := by
  change first.map (MulAut.conj (1 : Atlas1600Group)).toMonoidHom = first
  rw [map_one]
  exact Subgroup.map_id first

private theorem place_seventeen : place 17 = second := by
  change second.map (MulAut.conj (1 : Atlas1600Group)).toMonoidHom = second
  rw [map_one]
  exact Subgroup.map_id second

/-- The three parabolic Sylow double cosets need no extension computation. -/
theorem representative_first_three (i : Fin 122) (a b : Fin 32) (k : Fin 18)
    (hk : k.val < 3) : RepresentativeWitness i a b k := by
  have ha : transversal i a ∈ S := atlas1600SylowTwoNormalForm_mem _
  have hb : (transversal i b)⁻¹ ∈ S := S.inv_mem (atlas1600SylowTwoNormalForm_mem _)
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl | rfl
  · refine Or.inl ⟨0, (basePlaces_mem (seedPattern i)).1, ?_, ?_⟩
    · rw [place_zero]; exact (seed_le_sylow i).trans sylow_le_first
    · rw [place_zero]
      simpa only [representative, ConverseLocalCoverage.doubleCosetRep_zero, mul_one] using
        first.mul_mem (sylow_le_first ha) (sylow_le_first hb)
  · refine Or.inl ⟨0, (basePlaces_mem (seedPattern i)).1, ?_, ?_⟩
    · rw [place_zero]; exact (seed_le_sylow i).trans sylow_le_first
    · rw [place_zero]
      simpa only [representative, ConverseLocalCoverage.doubleCosetRep_one] using
        first.mul_mem (first.mul_mem (sylow_le_first ha) reflection_mem_first)
          (sylow_le_first hb)
  · refine Or.inl ⟨17, (basePlaces_mem (seedPattern i)).2, ?_, ?_⟩
    · rw [place_seventeen]; exact (seed_le_sylow i).trans sylow_le_second
    · rw [place_seventeen]
      simpa only [representative, ConverseLocalCoverage.doubleCosetRep_two] using
        second.mul_mem (second.mul_mem (sylow_le_second ha) reflection_mem_second)
          (sylow_le_second hb)

private theorem adjoined_mem (i : Fin 122) (x : Atlas1600Group) :
    x ∈ singleExtension i x :=
  mem_sup_right (subset_closure (Set.mem_singleton x))

private theorem extension_le {i : Fin 122} {x : Atlas1600Group}
    {H : Subgroup Atlas1600Group} (hq : seed i ≤ H) (hx : x ∈ H) :
    singleExtension i x ≤ H :=
  sup_le hq ((closure_le _).mpr (Set.singleton_subset_iff.mpr hx))

/-- Multiplication on both sides by seed elements preserves the literal extension. -/
theorem singleExtension_seed_mul (i : Fin 122) (q t : seed i) (r : Atlas1600Group) :
    singleExtension i (q.val * r * t.val) = singleExtension i r := by
  apply le_antisymm
  · apply extension_le le_sup_left
    exact mul_mem (mul_mem (mem_sup_left q.property) (adjoined_mem i r))
      (mem_sup_left t.property)
  · apply extension_le le_sup_left
    have he : r = q.val⁻¹ * (q.val * r * t.val) * t.val⁻¹ := by group
    have hm : q.val⁻¹ * (q.val * r * t.val) * t.val⁻¹ ∈
        singleExtension i (q.val * r * t.val) :=
      mul_mem (mul_mem (inv_mem (mem_sup_left q.property))
        (adjoined_mem i _)) (inv_mem (mem_sup_left t.property))
    exact (congrArg (fun z => z ∈ singleExtension i (q.val * r * t.val)) he).mpr hm

/-- The existing Sylow double-coset theorem supplies all ambient coverage. -/
theorem seed_doubleCoset_cover (hf : SylowFactorizations)
    (i : Fin 122) (x : Atlas1600Group) :
    ∃ (q t : seed i) (a b : Fin 32) (k : Fin 18),
      x = q.val * representative i a b k * t.val := by
  obtain ⟨s, u, k, hx⟩ := ConverseLocalCoverage.doubleCoset_cover x
  obtain ⟨n, hn⟩ := atlas1600SylowTwoNormalForm_surjective s.property
  obtain ⟨m, hm⟩ := atlas1600SylowTwoNormalForm_surjective (S.inv_mem u.property)
  obtain ⟨q, a, ha⟩ := hf i n
  obtain ⟨t, b, hb⟩ := hf i m
  have hs : s.val = q.val * transversal i a := hn.symm.trans ha
  have hu : u.val = (transversal i b)⁻¹ * t.val⁻¹ := by
    have h := hm.symm.trans hb
    have hh := congrArg Inv.inv h
    simpa only [inv_inv, mul_inv_rev] using hh
  refine ⟨q, t⁻¹, a, b, k, ?_⟩
  rw [hx, hs, hu]
  change q.val * transversal i a * ConverseLocalCoverage.doubleCosetRep k *
    ((transversal i b)⁻¹ * t.val⁻¹) =
    q.val * (transversal i a * ConverseLocalCoverage.doubleCosetRep k *
      (transversal i b)⁻¹) * t.val⁻¹
  group

private theorem obstruction_of_sylow {H : Subgroup Atlas1600Group}
    (g : Atlas1600Group) (h : S.map (MulAut.conj g).toMonoidHom ≤ H) :
    ¬ 2 ∣ H.index := by
  intro hd
  have he := hd.trans (Subgroup.index_dvd_of_le h)
  have hi := Subgroup.index_map_of_bijective
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).bijective S
  rw [hi, atlas1600SylowTwoSubgroup_index] at he
  exact (by decide : ¬ (2 : Nat) ∣ 8775) he

/-- Finite witness recovery is sufficient for the exact, unconditional target
once both independent certificate families are supplied. -/
theorem obstruction_of_certificates (hf : SylowFactorizations)
    (hw : ∀ (i : Fin 122) (a b : Fin 32) (c : Fin 15),
      RepresentativeWitness i a b ⟨c.val + 3, by omega⟩)
    (i : Fin 122) (x : Atlas1600Group) (hx : ∀ j ∈ placeIds i, x ∉ place j) :
    ¬ 2 ∣ (singleExtension i x).index ∨
      25 ∣ Nat.card (singleExtension i x) ∨ 13 ∣ Nat.card (singleExtension i x) := by
  obtain ⟨q, t, a, b, k, hfactor⟩ := seed_doubleCoset_cover hf i x
  have hE : singleExtension i x = singleExtension i (representative i a b k) := by
    rw [hfactor, singleExtension_seed_mul]
  have hrep : RepresentativeWitness i a b k := by
    by_cases hk : k.val < 3
    · exact representative_first_three i a b k hk
    · simpa only [Nat.sub_add_cancel (show 3 ≤ k.val by omega)] using
        hw i a b ⟨k.val - 3, by omega⟩
  rcases hrep with hp | hs | h25 | h13
  · obtain ⟨j, hj, hq, hr⟩ := hp
    exact (hx j hj (hfactor.symm ▸ (place j).mul_mem
      ((place j).mul_mem (hq q.property) hr) (hq t.property))).elim
  · obtain ⟨g, hg⟩ := hs
    rw [hE]
    exact Or.inl (obstruction_of_sylow g hg)
  · obtain ⟨L, hL, hc⟩ := h25
    rw [hE]
    exact Or.inr (Or.inl (hc ▸ Subgroup.card_dvd_of_le hL))
  · obtain ⟨y, hy, ho⟩ := h13
    rw [hE]
    exact Or.inr (Or.inr (ho ▸ Subgroup.orderOf_dvd_natCard _ hy))

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions
