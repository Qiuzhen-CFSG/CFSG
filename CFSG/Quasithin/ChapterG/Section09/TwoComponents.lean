module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.Geometry
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.TensorData
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.Models
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.Contracts

/-!
# The two-component branch of G.9.3

Source: Aschbacher--Smith, combined manuscript, printed p.356; the target
alternatives (14) and (15) are on printed p.354.

The imported reductions select the actual distinct component pair and retain
the original elementary actor. `TensorData` specifies the common Schur-field
construction; the degree and induction lemmas use its genuine equivariant
tensor identification. Existence of that construction, the rank and
splitting-field bounds, and recognition of the surviving natural actions
remain prerequisites of the source theorem. The final bookkeeping lemma
below combines their precise outputs; it is conditional and does not assert
the source classification.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A L L₂ H : Subgroup G} {m : ℕ}

/-- Numerical assembly after the tensor construction, dimension reduction
and natural-action recognition. All three mathematical obligations remain
explicit; in particular this is not a proof of G.9.3 from its hypotheses. -/
theorem conclusion_of_tensor_recognition (h : Setup ρ A m) (T : TensorData ρ L L₂)
    (hm : m ≤ 2 * primeRank 2 L) (hk : T.k = 2 ∨ T.k = 3)
    (htwo : T.k = 2 → 1 < T.n ∧
      Quasiequivalent (ρ.comp H.subtype) (fourOrthogonal T.n))
    (hthree : T.k = 3 → T.n = 1 ∧ primeRank 2 L = 2 ∧
      Quasiequivalent ρ threeTensor) : Conclusion ρ H m := by
  rcases hk with hk | hk
  · obtain ⟨hn, he⟩ := htwo hk
    obtain ⟨hd, hm⟩ := T.dimension_two_bounds hk h.degree_le
    exact Or.inr ⟨T.n, hn, he, hd, hm⟩
  · obtain ⟨hn, hr, he⟩ := hthree hk
    have hm4 : m ≤ 4 := by omega
    obtain ⟨hd, hm⟩ := T.dimension_three_bounds hk hn hm4 h.degree_le
    exact Or.inl ⟨he, hd, hm⟩

end CFSG.Quasithin.ChapterG.Section09.TwoComponents
