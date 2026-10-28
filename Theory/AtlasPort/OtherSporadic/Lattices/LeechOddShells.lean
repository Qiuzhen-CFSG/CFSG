/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechOddShells.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechOddCounts

/-!
Exact finite descriptions and counts of the three small odd Leech shells.
Reconstruction from magnitude supports proves exhaustion and disjointness of the counted families.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

theorem signedOddProfile_parity (T F : Finset Omega) (c : golay) (i : Omega) :
    signedOddProfile T F c i % 2 = 1 := by
  have h := oddProfileBase_parity T F i
  change (if c.val i = 0 then oddProfileBase T F i else -oddProfileBase T F i) % 2 = 1
  split_ifs <;> omega

theorem reconstruct_noFive (x : IntegerCoordinates) (hx : x ∈ leech)
    (hp : ∀ i, x i % 2 = 1) (hn : integerDot x x ≤ 64) (t : ℕ)
    (hT : (oddThreeSupport x).card = t) (hF : (oddFiveSupport x).card = 0) :
    x ∈ oddNoFiveVectors t := by
  obtain ⟨c,hc⟩ := odd_profile_reconstruction x hx hp hn
  have hf := Finset.card_eq_zero.mp hF
  apply Finset.mem_image.mpr
  exact ⟨(⟨oddThreeSupport x,hT⟩,c),Finset.mem_univ _,by simpa [noFiveVector,hf] using hc.symm⟩

theorem reconstruct_oneFive (x : IntegerCoordinates) (hx : x ∈ leech)
    (hp : ∀ i, x i % 2 = 1) (hn : integerDot x x ≤ 64) (t : ℕ)
    (hT : (oddThreeSupport x).card = t) (hF : (oddFiveSupport x).card = 1) :
    x ∈ oddOneFiveVectors t := by
  obtain ⟨c,hc⟩ := odd_profile_reconstruction x hx hp hn
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hF
  have hd : ∀ i ∈ oddThreeSupport x, i ≠ a := by
    intro i hi he
    exact Finset.disjoint_left.mp (odd_supports_disjoint x) hi (by simp [ha,he])
  let T := (oddThreeSupport x).subtype (fun i => i ≠ a)
  have hm : oneFiveSupport a T = oddThreeSupport x := Finset.subtype_map_of_mem hd
  have ht : T.card = t := by
    have hh := congrArg Finset.card hm
    simpa [oneFiveSupport,hT] using hh
  apply Finset.mem_biUnion.mpr
  refine ⟨a,Finset.mem_univ _,Finset.mem_image.mpr ?_⟩
  exact ⟨(⟨T,ht⟩,c),Finset.mem_univ _,by simpa [oneFiveVector,hm,ha] using hc.symm⟩

theorem oddNoFiveVectors_properties (t : ℕ) (ht : (-(t : ℤ)) % 2 = 1)
    (x : IntegerCoordinates) (hx : x ∈ oddNoFiveVectors t) :
    x ∈ leech ∧ (∀ i, x i % 2 = 1) ∧ integerDot x x = 24 + 8 * (t : ℤ) := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  refine ⟨signedOddProfile_mem _ _ ?_ p.2,signedOddProfile_parity _ _ _,?_⟩
  · simpa [p.1.prop] using ht
  · simpa [noFiveVector,p.1.prop] using signedOddProfile_norm p.1.val ∅ (by simp) p.2

theorem oddOneFiveVectors_properties (t : ℕ) (ht : (1 - (t : ℤ)) % 2 = 1)
    (x : IntegerCoordinates) (hx : x ∈ oddOneFiveVectors t) :
    x ∈ leech ∧ (∀ i, x i % 2 = 1) ∧ integerDot x x = 48 + 8 * (t : ℤ) := by
  obtain ⟨a,_,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  refine ⟨signedOddProfile_mem _ _ ?_ p.2,signedOddProfile_parity _ _ _,?_⟩
  · simpa [oneFiveSupport,p.1.prop] using ht
  · have hh := signedOddProfile_norm _ _ (oneFiveSupport_disjoint a p.1.val) p.2
    simp only [oneFiveSupport,Finset.card_map,p.1.prop,Finset.card_singleton] at hh
    change integerDot (signedOddProfile _ _ _) (signedOddProfile _ _ _) = _
    simp only [oneFiveSupport]
    rw [hh]; ring

theorem odd_minimal_shell_iff (x : IntegerCoordinates) :
    (x ∈ leech ∧ (∀ i, x i % 2 = 1) ∧ integerDot x x = 32) ↔ x ∈ oddNoFiveVectors 1 := by
  constructor
  · rintro ⟨hx,hp,hn⟩
    obtain ⟨ht,hf⟩ := odd_minimal_profile x hx hp hn
    exact reconstruct_noFive x hx hp (by omega) 1 ht hf
  · intro hx
    simpa using oddNoFiveVectors_properties 1 (by decide) x hx

theorem odd_six_shell_iff (x : IntegerCoordinates) :
    (x ∈ leech ∧ (∀ i, x i % 2 = 1) ∧ integerDot x x = 48) ↔
    x ∈ oddNoFiveVectors 3 ∪ oddOneFiveVectors 0 := by
  constructor
  · rintro ⟨hx,hp,hn⟩
    rcases odd_six_profiles x hx hp hn with ⟨ht,hf⟩ | ⟨ht,hf⟩
    · exact Finset.mem_union_left _ (reconstruct_noFive x hx hp (by omega) 3 ht hf)
    · exact Finset.mem_union_right _ (reconstruct_oneFive x hx hp (by omega) 0 ht hf)
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simpa using oddNoFiveVectors_properties 3 (by decide) x hx
    · simpa using oddOneFiveVectors_properties 0 (by decide) x hx

theorem odd_eight_shell_iff (x : IntegerCoordinates) :
    (x ∈ leech ∧ (∀ i, x i % 2 = 1) ∧ integerDot x x = 64) ↔
    x ∈ oddNoFiveVectors 5 ∪ oddOneFiveVectors 2 := by
  constructor
  · rintro ⟨hx,hp,hn⟩
    rcases odd_eight_profiles x hx hp hn with ⟨ht,hf⟩ | ⟨ht,hf⟩
    · exact Finset.mem_union_left _ (reconstruct_noFive x hx hp (by omega) 5 ht hf)
    · exact Finset.mem_union_right _ (reconstruct_oneFive x hx hp (by omega) 2 ht hf)
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simpa using oddNoFiveVectors_properties 5 (by decide) x hx
    · simpa using oddOneFiveVectors_properties 2 (by decide) x hx

theorem odd_shapes_disjoint (t u : ℕ) :
    Disjoint (oddNoFiveVectors t) (oddOneFiveVectors u) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨a,_,hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨q,_,he⟩ := Finset.mem_image.mp hy
  have hh := congrArg oddFiveSupport he
  simp only [oneFiveVector,noFiveVector,
    signedOddProfile_five_support _ _ (oneFiveSupport_disjoint _ _),
    signedOddProfile_five_support _ ∅ (by simp)] at hh
  exact Finset.singleton_ne_empty a hh

abbrev OddShell (r : ℤ) :=
  {x : IntegerCoordinates // x ∈ leech ∧ (∀ i, x i % 2 = 1) ∧ integerDot x x = 8 * r}

theorem oddShell_card_of_finset (r : ℤ) (s : Finset IntegerCoordinates)
    (h : ∀ x, (x ∈ leech ∧ (∀ i, x i % 2 = 1) ∧ integerDot x x = 8 * r) ↔ x ∈ s) :
    Nat.card (OddShell r) = s.card := by
  let e : OddShell r ≃ {x // x ∈ s} := Equiv.subtypeEquivRight h
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]

theorem odd_minimal_shell_card : Nat.card (OddShell 4) = 98304 := by
  rw [oddShell_card_of_finset 4 (oddNoFiveVectors 1) odd_minimal_shell_iff]
  exact odd_minimal_shape_card

theorem odd_six_shell_card : Nat.card (OddShell 6) = 8388608 := by
  rw [oddShell_card_of_finset 6 _ odd_six_shell_iff,
    Finset.card_union_of_disjoint (odd_shapes_disjoint 3 0),
    odd_six_shape_cards.1,odd_six_shape_cards.2]

theorem odd_eight_shell_card : Nat.card (OddShell 8) = 198967296 := by
  rw [oddShell_card_of_finset 8 _ odd_eight_shell_iff,
    Finset.card_union_of_disjoint (odd_shapes_disjoint 5 2),
    odd_eight_shape_cards.1,odd_eight_shape_cards.2]

end Atlas.Lattices
