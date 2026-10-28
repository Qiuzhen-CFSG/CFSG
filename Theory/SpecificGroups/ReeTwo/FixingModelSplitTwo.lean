module
public import Theory.SpecificGroups.ReeTwo.FixingModelTwoStructure

/-!
# The fixed marked involution for split fixing action two

The number of square-one elements commuting with an element is invariant under
all automorphisms. The embedded root 2 squares to the mark and has 40 such
commuting elements; square roots of either other nonidentity central element
never have that count. The center classification therefore forces the mark to
be fixed.

Source: Shinoda (1975), pp.81–83, through the verified core multiplication and
fixing action census row 2 in `FixingModelTwoStructure`.
-/

namespace ReeTwo.FixingModel
open Two

private def count (x : Model 2 false) : ℕ := Fintype.card {p : Params //
  cmul (elt false p) (elt false p) = 1 ∧ cmul (elt false p) x = cmul x (elt false p)}

private noncomputable def involutionCount (x : firstCore 2 false) : ℕ :=
  Nat.card {y : firstCore 2 false // y ^ 2 = 1 ∧ y * x = x * y}

private theorem involutionCount_eq (x : firstCore 2 false) :
    involutionCount x = count x.val := by
  unfold involutionCount count
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine (parameterEquiv false).subtypeEquiv ?_
  intro y
  have he : elt false (parameterEquiv false y) = y.val :=
    congrArg Subtype.val ((parameterEquiv false).symm_apply_apply y)
  simp only [cmul_eq, he, pow_two]
  exact and_congr Subtype.ext_iff Subtype.ext_iff

private theorem involutionCount_aut (a : MulAut (firstCore 2 false))
    (x : firstCore 2 false) : involutionCount (a x) = involutionCount x := by
  symm
  apply Nat.card_congr
  refine a.toEquiv.subtypeEquiv ?_
  intro y
  change (y ^ 2 = 1 ∧ y * x = x * y) ↔
    ((a y) ^ 2 = 1 ∧ a y * a x = a x * a y)
  rw [← map_pow, ← map_one a, ← map_mul, ← map_mul, a.injective.eq_iff,
    a.injective.eq_iff]
  simp only [map_one]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem witness_count : count (root false 2) = 40 := by decide +kernel

private def decode (n : Nat) : Model 2 false :=
  ⟨Core.CensusPacked.decode (n % 1024), ⟨n / 1024 % 4, Nat.mod_lt _ (by decide)⟩⟩

private def code (x : Model 2 false) : Nat :=
  Core.CensusPacked.code x.core + 1024 * x.idx.val

private def representative : Fin 14 → Nat := ![31, 53, 78, 181, 2062, 2107, 2144, 14, 21, 63, 85, 2058, 2111, 2250]

-- Each entry gives a conjugator and an index into the preceding transversal.
private def certificate : Nat → Nat × Fin 14
  | 14 => (0, 7)
  | 21 => (0, 8)
  | 31 => (0, 0)
  | 46 => (1038, 8)
  | 53 => (0, 1)
  | 63 => (0, 9)
  | 78 => (0, 2)
  | 85 => (0, 10)
  | 95 => (9, 9)
  | 110 => (3075, 1)
  | 117 => (1024, 2)
  | 127 => (9, 0)
  | 142 => (17, 2)
  | 149 => (1028, 7)
  | 159 => (7, 9)
  | 174 => (3086, 1)
  | 181 => (0, 3)
  | 191 => (7, 0)
  | 206 => (9, 7)
  | 213 => (2062, 8)
  | 223 => (17, 0)
  | 238 => (1027, 8)
  | 245 => (2051, 1)
  | 255 => (46, 9)
  | 270 => (3072, 8)
  | 277 => (10, 1)
  | 287 => (10, 9)
  | 302 => (1037, 10)
  | 309 => (10, 8)
  | 319 => (10, 0)
  | 334 => (1024, 1)
  | 341 => (1041, 2)
  | 351 => (3, 0)
  | 366 => (1028, 3)
  | 373 => (13, 10)
  | 383 => (3, 9)
  | 398 => (1034, 1)
  | 405 => (3, 3)
  | 415 => (45, 0)
  | 430 => (1031, 3)
  | 437 => (1045, 7)
  | 447 => (18, 9)
  | 462 => (3082, 8)
  | 469 => (2062, 1)
  | 479 => (4, 9)
  | 494 => (1024, 10)
  | 501 => (2051, 8)
  | 511 => (4, 0)
  | 526 => (21, 7)
  | 533 => (14, 8)
  | 543 => (32, 0)
  | 558 => (1024, 8)
  | 565 => (14, 1)
  | 575 => (31, 9)
  | 590 => (13, 2)
  | 597 => (9, 10)
  | 607 => (22, 9)
  | 622 => (3082, 1)
  | 629 => (1037, 2)
  | 639 => (41, 0)
  | 654 => (4, 2)
  | 661 => (1033, 7)
  | 671 => (39, 9)
  | 686 => (3072, 1)
  | 693 => (7, 3)
  | 703 => (24, 0)
  | 718 => (4, 7)
  | 725 => (2048, 8)
  | 735 => (14, 0)
  | 750 => (1034, 8)
  | 757 => (2058, 1)
  | 767 => (14, 9)
  | 782 => (3086, 8)
  | 789 => (3, 1)
  | 799 => (42, 9)
  | 814 => (1027, 10)
  | 821 => (3, 8)
  | 831 => (21, 0)
  | 846 => (1038, 1)
  | 853 => (1028, 2)
  | 863 => (28, 0)
  | 878 => (1027, 3)
  | 885 => (3, 10)
  | 895 => (35, 9)
  | 910 => (1027, 1)
  | 917 => (4, 3)
  | 927 => (13, 0)
  | 942 => (1024, 3)
  | 949 => (1024, 7)
  | 959 => (13, 9)
  | 974 => (3075, 8)
  | 981 => (2048, 1)
  | 991 => (27, 9)
  | 1006 => (1033, 10)
  | 1013 => (2058, 8)
  | 1023 => (36, 0)
  | 2058 => (0, 11)
  | 2062 => (0, 4)
  | 2107 => (0, 5)
  | 2111 => (0, 12)
  | 2129 => (28, 11)
  | 2133 => (56, 4)
  | 2144 => (0, 6)
  | 2148 => (18, 12)
  | 2193 => (3, 11)
  | 2197 => (3, 4)
  | 2208 => (10, 6)
  | 2212 => (41, 12)
  | 2250 => (0, 13)
  | 2254 => (21, 4)
  | 2299 => (13, 6)
  | 2303 => (14, 12)
  | 2331 => (22, 6)
  | 2335 => (17, 12)
  | 2346 => (27, 11)
  | 2350 => (32, 4)
  | 2368 => (31, 6)
  | 2372 => (13, 12)
  | 2417 => (7, 13)
  | 2421 => (41, 4)
  | 2432 => (17, 6)
  | 2436 => (9, 12)
  | 2481 => (13, 13)
  | 2485 => (13, 4)
  | 2523 => (4, 5)
  | 2527 => (4, 12)
  | 2538 => (27, 13)
  | 2542 => (53, 4)
  | 2570 => (4, 13)
  | 2574 => (10, 4)
  | 2619 => (7, 6)
  | 2623 => (49, 12)
  | 2641 => (3, 13)
  | 2645 => (9, 4)
  | 2656 => (22, 5)
  | 2660 => (60, 12)
  | 2705 => (28, 13)
  | 2709 => (45, 4)
  | 2720 => (3, 5)
  | 2724 => (3, 12)
  | 2762 => (4, 11)
  | 2766 => (4, 4)
  | 2811 => (21, 5)
  | 2815 => (36, 12)
  | 2843 => (10, 5)
  | 2847 => (27, 12)
  | 2858 => (21, 13)
  | 2862 => (17, 4)
  | 2880 => (9, 5)
  | 2884 => (28, 12)
  | 2929 => (13, 11)
  | 2933 => (24, 4)
  | 2944 => (13, 5)
  | 2948 => (35, 12)
  | 2993 => (7, 11)
  | 2997 => (7, 4)
  | 3035 => (3, 6)
  | 3039 => (10, 12)
  | 3050 => (21, 11)
  | 3054 => (31, 4)
  | _ => (0, 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem representative_counts : ∀ i : Fin 14,
    count (decode (representative i)) ≠ 40 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem certificate_valid : ∀ p : Params,
    (cmul (elt false p) (elt false p) = special false ∨
      cmul (elt false p) (elt false p) = cmul (special false) (root false 9)) →
    let w := certificate (code (elt false p))
    let g := decode w.1
    g.core.b0 + g.core.b1 + g.core.b3 + g.core.b4 = 0 ∧
    cmul g (elt false p) = cmul (decode (representative w.2)) g := by
  decide +kernel

private theorem other_square_involutionCount (x : firstCore 2 false)
    (hx : (x ^ 2).val = special false ∨
      (x ^ 2).val = special false * root false 9) :
    involutionCount x ≠ 40 := by
  let p := parameterEquiv false x
  have he : elt false p = x.val :=
    congrArg Subtype.val ((parameterEquiv false).symm_apply_apply x)
  have hv := certificate_valid p
  simp only [cmul_eq, he] at hv
  obtain ⟨hg, hc⟩ := hv (by simpa only [pow_two, Subgroup.coe_mul] using hx)
  let w := certificate (code x.val)
  let g : firstCore 2 false := inside false (decode w.1) hg
  have hc' : (MulAut.conj g x).val = decode (representative w.2) := by
    change g.val * x.val * g.val⁻¹ = _
    change g.val * x.val = decode (representative w.2) * g.val at hc
    rw [hc, mul_inv_cancel_right]
  have hh := involutionCount_aut (MulAut.conj g) x
  rw [involutionCount_eq, hc'] at hh
  rw [← hh]
  exact representative_counts w.2

/-- Every automorphism of the split action-two first core fixes the marked involution. -/
public theorem two_false_fixed (a : MulAut (firstCore 2 false)) :
    a (centralInvolution 2 false) = centralInvolution 2 false := by
  let r : firstCore 2 false := inside false (root false 2) rfl
  have hr : r ^ 2 = centralInvolution 2 false := by
    apply Subtype.ext
    change (root false 2 : Model 2 false) ^ 2 = root false 9
    decide +kernel
  have hcount : involutionCount (a r) = 40 := by
    rw [involutionCount_aut, involutionCount_eq]
    exact witness_count
  have hsq : (a r) ^ 2 = a (centralInvolution 2 false) := by rw [← map_pow, hr]
  have hc : a (centralInvolution 2 false) ∈ Subgroup.center (firstCore 2 false) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := a.surjective y
    simpa only [map_mul] using congrArg a
      (Subgroup.mem_center_iff.mp (centralInvolution_mem_center 2 false) x)
  rcases firstCore_center_cases false (a (centralInvolution 2 false)) hc with h | h | h | h
  · exact False.elim (centralInvolution_ne_one 2 false (a.injective (by
      rw [map_one]
      exact Subtype.ext h)))
  · exact False.elim (other_square_involutionCount (a r) (Or.inl (by rw [hsq]; exact h)) hcount)
  · exact Subtype.ext h
  · exact False.elim (other_square_involutionCount (a r) (Or.inr (by rw [hsq]; exact h)) hcount)

end ReeTwo.FixingModel
