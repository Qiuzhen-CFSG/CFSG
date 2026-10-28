module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.UnipotentCocycle.SplitPositive.Filtration

/-!
# Coefficient-involution cocycles in the split positive D4 group

Let `n = 2*m`, with `m > 0`. The `3*m`-th binary Frobenius is the involution
of the actual cubic coefficient field GF(2^(3*n)). Every cocycle for its
coefficient action on the original positive subgroup is a coboundary there.

Use the twelve-step root filtration from `SplitPositive.Filtration`. The
cocycle equation and the trivial intersection of a leading root group with
the next tail show that its parameter is fixed by Frobenius. The scalar
trace equation supplies a root coboundary. Twisted conjugation by that root
element puts the cocycle in the next tail, and decreasing induction finishes
at the trivial tail. All subgroups and root exchanges use the integral Geck
split group; the proof includes `m = 1`.

This discharges the split-positive premise of the triality descent in
`UnipotentCocycle.Descent`; the parent owns the genuine triality and global
assembly. Sources: GLS3 §§2.1, 2.3–2.5, especially 2.5.13 and 2.5.17
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith 16.1.3–4, printed p.1171
(`refs/quasithin.pdf`). No general Lang theorem is used.
-/

public section

noncomputable section
namespace Triality.Standard.EvenField.NormalForm.UnipotentCocycle
open PositiveCoordinates OuterOdd SplitPositive
open Theory.AlgebraicGroup.StandardRootSystem
local instance : DecidableEq ((typeDRootPairing_base 2).support ⊕ TypeDRootIndex (2 + 2)) :=
  instDecidableEqSum

private lemma leading_product {G : Type*} [Group G] (x y w z : G)
    (h : x * w * (y * z) = 1) : x * y = (y⁻¹ * w * y * z)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  calc
    x * y * (y⁻¹ * w * y * z) = x * w * (y * z) := by group
    _ = 1 := h

private lemma twisted_cocycle {G : Type*} [Group G] (c : MulAut G)
    (hc : ∀ g, c (c g) = g) (u b : G) (hu : u * c u = 1) :
    (b * u * (c b)⁻¹) * c (b * u * (c b)⁻¹) = 1 := by
  simp only [map_mul, map_inv, hc]
  calc
    b * u * (c b)⁻¹ * (c b * c u * b⁻¹) = b * (u * c u) * b⁻¹ := by group
    _ = 1 := by rw [hu]; group

private lemma untwist_solution {G : Type*} [Group G] (c : MulAut G) (u b v : G)
    (hv : b * u * (c b)⁻¹ = v⁻¹ * c v) : u = (v*b)⁻¹ * c (v*b) := by
  have h := congrArg (fun x => b⁻¹ * x * c b) hv
  simpa only [map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel_right, inv_mul_cancel, mul_one] using h

private lemma remove_root {G : Type*} [Group G] (c : MulAut G) (x b w : G)
    (hx : x = b⁻¹ * c b) : b * (x*w) * (c b)⁻¹ = c b * w * (c b)⁻¹ := by
  rw [hx]
  group

private lemma leading_fixed (n : ℕ) (hn : 0 < n)
    (e : CoefficientAut (binaryParameters n hn)) (i : Fin 12)
    (t : ExtensionField (binaryParameters n hn))
    (w : SplitGroup (binaryParameters n hn)) (hw : w ∈ tail (binaryParameters n hn) (i.val+1))
    (hu : (curve (binaryParameters n hn) i t * w) *
      coefficientSplit (binaryParameters n hn) e (curve (binaryParameters n hn) i t * w) = 1) :
    e t = t := by
  let P := binaryParameters n hn
  let c := coefficientSplit P e
  have hprod : curve P i t * w * (curve P i (e t) * c w) = 1 := by
    simpa only [map_mul, coefficientSplit_curve] using hu
  have hw' : (curve P i (e t))⁻¹ * w * curve P i (e t) ∈ tail P (i.val+1) := by
    simpa only [curve_inv, neg_neg] using curve_conj_tail n hn (i.val+1) i (-(e t)) hw
  have hz : curve P i (t + e t) ∈ tail P (i.val+1) := by
    rw [curve_add, leading_product _ _ _ _ hprod]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hw' (coefficient_tail P e _ hw))
  have ht : t + e t = 0 := curve_mem_tail_succ n hn i (t + e t) hz
  calc
    e t = (t + e t) - t := by ring
    _ = t := by rw [ht, zero_sub]; exact CharTwo.neg_eq t

private lemma coefficient_involutive (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) :
    ∀ g : SplitGroup (binaryParameters n hn),
      coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn (3*m))
        (coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) g) = g := by
  have ho := coefficientFrobenius_order_two n hn m hm hnm
  have he : coefficientFrobenius n hn (3*m) * coefficientFrobenius n hn (3*m) = 1 := by
    rw [← pow_two, ← ho, pow_orderOf_eq_one]
  intro g
  rw [← coefficientSplit_mul, he, coefficientSplit_one]

private theorem push_fixed_root (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (i : Fin 12) (t : ExtensionField (binaryParameters n hn))
    (w : SplitGroup (binaryParameters n hn)) (hw : w ∈ tail (binaryParameters n hn) (i.val+1))
    (ht : coefficientFrobenius n hn (3*m) t = t) :
    ∃ b : SplitGroup (binaryParameters n hn), b ∈ tail (binaryParameters n hn) i.val ∧
      b * (curve (binaryParameters n hn) i t * w) *
        (coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) b)⁻¹ ∈
          tail (binaryParameters n hn) (i.val+1) := by
  let P := binaryParameters n hn
  let e := coefficientFrobenius n hn (3*m)
  let c := coefficientSplit P e
  obtain ⟨s, hs⟩ := canonical_curve_coboundary n hn m hm hnm i t ht
  let b := curve P i s
  refine ⟨b, curve_mem_tail P i s (le_refl _), ?_⟩
  have hcb : c b = curve P i (e s) := coefficientSplit_curve P e i s
  have hmem : c b * w * (c b)⁻¹ ∈ tail P (i.val+1) := by
    simpa only [hcb] using curve_conj_tail n hn (i.val+1) i (e s) hw
  exact (remove_root c (curve P i t) b w hs).symm ▸ hmem

private theorem push_cocycle (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (i : Fin 12) (u : SplitGroup (binaryParameters n hn))
    (hu : u ∈ tail (binaryParameters n hn) i.val)
    (hcoc : u * coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) u = 1) :
    ∃ b : SplitGroup (binaryParameters n hn), b ∈ tail (binaryParameters n hn) i.val ∧
      b * u * (coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) b)⁻¹ ∈
        tail (binaryParameters n hn) (i.val+1) := by
  obtain ⟨t, w, hw, rfl⟩ := tail_factor n hn i hu
  exact push_fixed_root n hn m hm hnm i t w hw
    (leading_fixed n hn _ i t w hw hcoc)

private theorem tail_cocycle_solutions (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (k : ℕ) (hk : k ≤ 12) :
    ∀ u : SplitGroup (binaryParameters n hn), u ∈ tail (binaryParameters n hn) k →
      u * coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) u = 1 →
      ∃ v : SplitGroup (binaryParameters n hn), v ∈ tail (binaryParameters n hn) k ∧
        u = v⁻¹ * coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) v := by
  induction hk using Nat.decreasingInduction with
  | self =>
    intro u hu _
    have hu' : u = 1 := by simpa only [tail_twelve, Subgroup.mem_bot] using hu
    subst u
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  | of_succ k hk ih =>
    intro u hu hcoc
    let P := binaryParameters n hn
    let e := coefficientFrobenius n hn (3*m)
    let c := coefficientSplit P e
    obtain ⟨b, hb, hnext⟩ := push_cocycle n hn m hm hnm ⟨k, hk⟩ u hu hcoc
    have hcoc' : (b*u*(c b)⁻¹) * c (b*u*(c b)⁻¹) = 1 :=
      twisted_cocycle c (coefficient_involutive n hn m hm hnm) u b hcoc
    obtain ⟨v, hv, hvsol⟩ := ih _ hnext hcoc'
    refine ⟨v*b, Subgroup.mul_mem _ (tail_antitone P (Nat.le_succ k) hv) hb, ?_⟩
    exact untwist_solution c u b v hvsol

/-- Every cocycle for the canonical coefficient involution is a coboundary
in the original split positive subgroup, including the case `m = 1`. -/
theorem splitPositive_cocycle_solutions (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (u : SplitGroup (binaryParameters n hn))
    (hu : u ∈ Parabolics.positiveSubgroup (binaryParameters n hn))
    (hcoc : u * coefficientSplit (binaryParameters n hn)
      (coefficientFrobenius n hn (3*m)) u = 1) :
    ∃ v : SplitGroup (binaryParameters n hn),
      v ∈ Parabolics.positiveSubgroup (binaryParameters n hn) ∧
      u = v⁻¹ * coefficientSplit (binaryParameters n hn)
        (coefficientFrobenius n hn (3*m)) v := by
  simpa only [tail_zero] using tail_cocycle_solutions n hn m hm hnm 0 (by omega) u
    (by simpa only [tail_zero] using hu) hcoc

end Triality.Standard.EvenField.NormalForm.UnipotentCocycle
