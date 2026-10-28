module

public import Theory.GroupTheory.NoncentralChiefRefinement.Accounting

/-!
# Four marked strata surrounding an unmarked chief interval

Refine four actual quotient filtrations, allowing central strata, and the central bottom
interval. Insert an arbitrary chief series in the gap and extend over a
quotient with no binary chief factors. Concatenation and equivariant
Jordan–Hölder compute the total count. No numerical bound on the surrounding
chief factors is assumed.

Source application: the multiplicities 1, 2, 1, 2 outside H_C/V_H in
Aschbacher–Smith 13.8.31, printed p.965.
-/

public section
open Subgroup Representation
namespace NoncentralChiefRefinement

/-- A marked filtration of a literal normal interval. Central strata may
occur between the homogeneous pieces; the multiplicity counts coordinates,
and does not assume a count of chief factors. -/
structure MarkedInterval {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]
    (A B : NormalNode K) (ρ : Representation (ZMod 2) K W) (multiplicity : ℕ) where
  length : ℕ
  flag : Filtration K length
  head : flag.term 0 = A
  last : flag.term (Fin.last length) = B
  copies : Fin length → ℕ
  strata : ∀ i, IsModuleStratum ρ (flag.term i.castSucc) (flag.term i.succ) (copies i)
  total : ∑ i, copies i = multiplicity

/-- Refining the marked quotient flag constructs its actual chief factors. -/
theorem MarkedInterval.exists_chief_refinement
    {K W : Type*} [Group K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W]
    {A B : NormalNode K} {ρ : Representation (ZMod 2) K W} [IsIrreducible ρ]
    {m : ℕ} (c : MarkedInterval A B ρ m) (hn : ∃ k w, ρ k w ≠ w) :
    ∃ s : ChiefSeries K, s.head = A ∧ s.last = B ∧ s.noncentralTwoCount = m := by
  obtain ⟨s, _, _, _, _, hs0, hs1, hc, _⟩ :=
    c.flag.exists_marked_refinement c.copies c.strata hn
  exact ⟨s, hs0.trans c.head, hs1.trans c.last, hc.trans c.total⟩

variable {K V₁ V₂ V₃ V₄ : Type*} [Group K] [Finite K]
  [AddCommGroup V₁] [Module (ZMod 2) V₁]
  [AddCommGroup V₂] [Module (ZMod 2) V₂]
  [AddCommGroup V₃] [Module (ZMod 2) V₃]
  [AddCommGroup V₄] [Module (ZMod 2) V₄]

/-- Refine the literal surrounding sections before counting their factors.
The four markings may involve different irreducible modules. -/
theorem complete_count_of_four_strata
    (Z U V C Q R : NormalNode K)
    (hZ : IsCentral ⊥ Z) (hterminal : HasNoTwoChiefFactors (K ⧸ R.val))
    (ρ₁ : Representation (ZMod 2) K V₁) [IsIrreducible ρ₁]
    (ρ₂ : Representation (ZMod 2) K V₂) [IsIrreducible ρ₂]
    (ρ₃ : Representation (ZMod 2) K V₃) [IsIrreducible ρ₃]
    (ρ₄ : Representation (ZMod 2) K V₄) [IsIrreducible ρ₄]
    (m₁ m₂ m₃ m₄ : ℕ)
    (c₁ : MarkedInterval Z U ρ₁ m₁) (c₂ : MarkedInterval U V ρ₂ m₂)
    (c₃ : MarkedInterval C Q ρ₃ m₃) (c₄ : MarkedInterval Q R ρ₄ m₄)
    (hn₁ : ∃ k v, ρ₁ k v ≠ v) (hn₂ : ∃ k v, ρ₂ k v ≠ v)
    (hn₃ : ∃ k v, ρ₃ k v ≠ v) (hn₄ : ∃ k v, ρ₄ k v ≠ v)
    (s : ChiefSeries K) (hs0 : s.head = V) (hs1 : s.last = C)
    (t : ChiefSeries K) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    t.noncentralTwoCount = s.noncentralTwoCount + m₁ + m₂ + m₃ + m₄ := by
  obtain ⟨z, hz0, hz1⟩ := exists_chiefSeries (⊥ : NormalNode K) Z bot_le
  have hzc : z.noncentralTwoCount = 0 :=
    z.noncentralTwoCount_eq_zero_of_central (by rwa [hz0, hz1])
  obtain ⟨a, ha0, ha1, hac⟩ := c₁.exists_chief_refinement hn₁
  obtain ⟨b, hb0, hb1, hbc⟩ := c₂.exists_chief_refinement hn₂
  obtain ⟨c, hc0, hc1, hcc⟩ := c₃.exists_chief_refinement hn₃
  obtain ⟨d, hd0, hd1, hdc⟩ := c₄.exists_chief_refinement hn₄
  obtain ⟨r, hr0, hr1⟩ := exists_chiefSeries R (⊤ : NormalNode K) le_top
  have hrc : r.noncentralTwoCount = 0 :=
    r.noncentralTwoCount_eq_zero_of_quotient R hr0.ge hterminal
  have hza : z.last = a.head := hz1.trans ha0.symm
  have hab : a.last = b.head := ha1.trans hb0.symm
  have hbs : b.last = s.head := hb1.trans hs0.symm
  have hsc : s.last = c.head := hs1.trans hc0.symm
  have hcd : c.last = d.head := hc1.trans hd0.symm
  have hdr : d.last = r.head := hd1.trans hr0.symm
  let za := z.smash a hza
  let zab := za.smash b ((RelSeries.last_smash hza).trans hab)
  let zabs := zab.smash s ((RelSeries.last_smash _).trans hbs)
  let zabsc := zabs.smash c ((RelSeries.last_smash _).trans hsc)
  let zabscd := zabsc.smash d ((RelSeries.last_smash _).trans hcd)
  let u := zabscd.smash r ((RelSeries.last_smash _).trans hdr)
  have hu0 : u.head = ⊥ := by
    simp only [u, zabscd, zabsc, zabs, zab, za, RelSeries.head_smash, hz0]
  have hu1 : u.last = ⊤ := (RelSeries.last_smash _).trans hr1
  have he := t.noncentralTwoCount_eq u (ht0.trans hu0.symm) (ht1.trans hu1.symm)
  rw [he]
  simp only [u, zabscd, zabsc, zabs, zab, za, ChiefSeries.noncentralTwoCount_smash,
    hzc, hrc, hac, hbc, hcc, hdc]
  omega

end NoncentralChiefRefinement
