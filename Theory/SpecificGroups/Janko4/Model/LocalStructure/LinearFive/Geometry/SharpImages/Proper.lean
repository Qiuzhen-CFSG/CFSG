module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.SharpImages.Data

/-!
# Proper subgroups of the exceptional octad kernel give a strict bound

Within the sixteen retained vertices, a 121-node certificate gives a strict
product bound for any power-of-two clique of size at most eight. Thus equality
in the large elementary bound requires the whole octad kernel, not merely a
subgroup of it. All fixed masks use the same certified native action tables.

Source application: Kleidman--Wilson (1988), Lemma 1.1.2(ii), p.485.
-/
@[expose] public section
namespace Janko4.LocalStructure.LinearFive.Geometry.SharpImages.Proper
open ElementaryNormalizerCover.ElementaryBound

def check (neighbors masks : Fin 192 → ℕ) : ElementaryNormalizerCover.ElementaryBound.Tree → List (Fin 192) → ℕ → Bool
  | .small, u, _ => decide (u.length < 2)
  | .bound k bs, u, w => decide
      ((u.length < 2 ^ (k+1) ∨ 8 < 2 ^ (k+1)) ∧ w = encode (sums bs) ∧ 2 ^ k * 2 ^ bs.length < 1024)
  | .branch v l r, u, w =>
      check neighbors masks l (u.filter (fun a => a != v)) w &&
      check neighbors masks r (u.filter (fun a => (neighbors v).testBit a.val))
        (w &&& masks v)

theorem check_sound (neighbors masks : Fin 192 → ℕ)
    (t : ElementaryNormalizerCover.ElementaryBound.Tree) (u : List (Fin 192)) (w : ℕ)
    (ht : check neighbors masks t u w = true)
    (s : Finset (Fin 192)) (a : Finset (Fin 2048))
    (hs : ∀ v ∈ s, v ∈ u) (ha : ∀ m ∈ a, w.testBit m.val = true)
    (hsize : s.card ≤ 8) (hne : 2 ≤ s.card) (hpow : ∃ d, s.card = 2 ^ d)
    (hc : ∀ v ∈ s, ∀ v' ∈ s, (neighbors v).testBit v'.val = true)
    (hf : ∀ v ∈ s, ∀ m ∈ a, (masks v).testBit m.val = true) :
    s.card * a.card < 1024 := by
  have hslen (u : List (Fin 192)) (hs : ∀ v ∈ s, v ∈ u) : s.card ≤ u.length :=
    (Finset.card_le_card (fun v hv => List.mem_toFinset.mpr (hs v hv))).trans
      (List.toFinset_card_le u)
  induction t generalizing u w with
  | small =>
    have hlt : u.length < 2 := of_decide_eq_true ht
    have := hslen u hs
    omega
  | bound k bs =>
    have hb : (u.length < 2 ^ (k+1) ∨ 8 < 2 ^ (k+1)) ∧ w = encode (sums bs) ∧
        2 ^ k * 2 ^ bs.length < 1024 := of_decide_eq_true ht
    obtain ⟨d, hd⟩ := hpow
    have hdlt : 2 ^ d < 2 ^ (k+1) := hd ▸ (hb.1.elim ((hslen u hs).trans_lt) hsize.trans_lt)
    have hdle : d ≤ k := by
      have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hdlt
      omega
    have hsc : s.card ≤ 2 ^ k := hd ▸ Nat.pow_le_pow_right (by decide) hdle
    have hac : a.card ≤ 2 ^ bs.length := card_le_sums a bs (hb.2.1 ▸ ha)
    exact (Nat.mul_le_mul hsc hac).trans_lt hb.2.2
  | branch v l r ihl ihr =>
    have ⟨hl, hr⟩ : check neighbors masks l (u.filter (fun a => a != v)) w = true ∧
        check neighbors masks r (u.filter (fun a => (neighbors v).testBit a.val))
          (w &&& masks v) = true := by
      simpa only [check, Bool.and_eq_true] using ht
    by_cases hv : v ∈ s
    · apply ihr _ _ hr
      · intro v' hv'
        exact List.mem_filter.mpr ⟨hs v' hv', hc v hv v' hv'⟩
      · intro m hm
        rw [Nat.testBit_land, ha m hm, hf v hv m hm]
        rfl
    · apply ihl _ _ hl
      · intro v' hv'
        exact List.mem_filter.mpr ⟨hs v' hv', by
          simpa only [bne_iff_ne] using (show v' ≠ v by rintro rfl; exact hv hv')⟩
      · exact ha



set_option maxRecDepth 10000 in
def certificate : ElementaryNormalizerCover.ElementaryBound.Tree := (.branch 16 (.branch 22 (.branch 54 (.branch 69 (.branch 76 (.branch 82 (.branch 128 (.branch 133 (.branch 145 (.branch 148 (.branch 149 (.branch 160 (.branch 187 (.branch 188 (.branch 191 .small (.bound 1 [28, 42, 70, 128, 270, 525, 1033])) (.bound 1 [27, 45, 70, 128, 270, 525, 1038])) (.bound 2 [23, 33, 70, 128, 270, 525, 1026])) (.bound 2 [16, 38, 70, 128, 270, 525, 1029])) (.bound 2 [5, 51, 67, 128, 267, 520, 1040])) (.bound 2 [9, 54, 70, 128, 263, 516, 1045])) (.branch 148 (.bound 2 [18, 36, 70, 128, 270, 525, 1031]) (.bound 3 [54, 70, 128, 270, 525, 1045]))) (.branch 145 (.branch 148 (.bound 2 [14, 54, 70, 128, 256, 515, 1045]) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045]))) (.branch 133 (.branch 145 (.branch 148 (.bound 2 [7, 49, 65, 128, 265, 522, 1042]) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045]))) (.branch 128 (.branch 133 (.branch 145 (.branch 148 (.bound 2 [2, 52, 68, 128, 268, 525, 1045]) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045]))) (.branch 82 (.branch 128 (.branch 133 (.branch 145 (.branch 148 (.bound 2 [11, 54, 70, 128, 261, 518, 1045]) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045]))) (.branch 76 (.branch 82 (.branch 128 (.branch 133 (.branch 145 (.branch 148 (.bound 2 [30, 40, 70, 128, 270, 525, 1035]) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045]))) (.branch 69 (.branch 76 (.branch 82 (.branch 128 (.branch 133 (.branch 145 (.branch 148 (.bound 2 [25, 47, 70, 128, 270, 525, 1036]) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045]))) (.branch 54 (.branch 69 (.branch 76 (.branch 82 (.branch 128 (.branch 133 (.branch 145 (.branch 148 (.bound 2 [21, 35, 70, 128, 270, 525, 1024]) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045]))) (.branch 22 (.branch 54 (.branch 69 (.branch 76 (.branch 82 (.branch 128 (.branch 133 (.branch 145 (.branch 148 (.bound 2 [12, 54, 70, 128, 258, 513, 1045]) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])) (.bound 3 [54, 70, 128, 270, 525, 1045])))

set_option maxRecDepth 10000 in
theorem certificate_checked : check neighbors masks certificate [0, 16, 22, 54, 69, 76, 82, 128, 133, 145, 148, 149, 160, 187, 188, 191] (2^2048-1) = true := by
  decide +kernel

end Janko4.LocalStructure.LinearFive.Geometry.SharpImages.Proper
