module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Induction
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree.Actions
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DimensionArithmetic

/-!
# Sharp splitting and the strictly smaller classified action

The two faithful actions constructed for the degree theorem also give the
equality induction its smaller classified action. Sharpness leaves either
no factor on the half-space and a moved plane, or one factor on the
half-space and a moved four-space. In the exceptional case we split at a
factor different from a chosen five-factor. The latter must lie in the
fixed-space product: otherwise its half-space degree bound is too large.

This module establishes the dimension and strict-induction portion of
Aschbacher--Smith G.9.2, printed pp.352--353. The retained small block and
the inclusion-preserving gluing remain separate constructions.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep

open DihedralDegree

universe v

variable {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι → ℕ}
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W} {i : ι}

/-- Induction data on the actual rotation-fixed space, together with the
two possible sizes of the retained rotation-moved block. -/
structure PreparedSplit (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W)
    (i : ι) (exceptional : Prop) where
  actions : SplitActions σ i
  fixed_classification : ClassifiedDecomposition
    (Representation.subrepresentation
      (σ.comp (subproductHom ((Finset.univ.erase i) \ actions.J)))
      (rotationFixed (factorRep σ i)) actions.fixed_stable) ⊤ exceptional
  small :
    (actions.J.card = 0 ∧ Module.finrank (ZMod 2) (rotationMoved (factorRep σ i)) = 2) ∨
    (actions.J.card = 1 ∧ Module.finrank (ZMod 2) (rotationMoved (factorRep σ i)) = 4)

/-- The two index sets and the distinguished index partition the factors. -/
theorem split_card (a : SplitActions σ i) :
    Fintype.card ι = (Finset.univ.erase i \ a.J).card + a.J.card + 1 := by
  have hJ : a.J ⊆ Finset.univ.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun h => a.excluded (h ▸ hj), Finset.mem_univ _⟩
  have h := Finset.card_sdiff_add_card_eq_card hJ
  have he := Finset.card_erase_of_mem (Finset.mem_univ i)
  simp only [Finset.card_univ] at he
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  omega

/-- Every nondistinguished factor belongs to one of the two smaller products. -/
theorem split_mem (a : SplitActions σ i) (j : ι) (hji : j ≠ i) :
    j ∈ Finset.univ.erase i \ a.J ∨ j ∈ a.J := by
  by_cases hj : j ∈ a.J
  · exact Or.inr hj
  · exact Or.inl (Finset.mem_sdiff.mpr
      ⟨Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, hj⟩)

variable [FiniteDimensional (ZMod 2) W]

theorem preparedSplit_cubic
    (split : DihedralSplittingTheorem.{v}) (bounds : DihedralDegreeTheorem.{v})
    (ih : ∀ s, s < Fintype.card ι → EqualityAt.{v} s)
    (hp : ∀ j, (p j).Prime) (ho : ∀ j, Odd (p j))
    (hf : Function.Injective σ) (hall : ∀ j, p j = 3)
    (hd : Module.finrank (ZMod 2) W ≤ 2 * Fintype.card ι) :
    Nonempty (PreparedSplit σ i False) := by
  obtain ⟨a⟩ := exists_splitActions split hp ho σ hf i
  let I := Finset.univ.erase i \ a.J
  let C := rotationFixed (factorRep σ i)
  let U := reflectionHalf (factorRep σ i)
  let τ := Representation.subrepresentation (σ.comp (subproductHom I)) C a.fixed_stable
  let υ := Representation.subrepresentation (σ.comp (subproductHom a.J)) U a.half_stable
  have hc := split_card a
  have hC := (dihedralDegree_fintype bounds (fun j : I => p j)
    (fun j => hp j) (fun j => ho j) τ a.fixed_faithful).1
  have hU := (dihedralDegree_fintype bounds (fun j : a.J => p j)
    (fun j => hp j) (fun j => ho j) υ a.half_faithful).1
  simp only [Fintype.card_coe] at hC hU
  obtain ⟨hDim, hM, hpos⟩ := split_dimensions (factorRep σ i) split (hp i) (ho i)
    (factorRep_injective σ hf i)
  have sharp := split_dimensions_rigid (e := 0) hc hDim (by simpa using hd)
    (by simpa using hC) hU hpos
  have hClt : I.card < Fintype.card ι := by dsimp [I]; omega
  have hCdim : Module.finrank (ZMod 2) C ≤ 2 * I.card := by
    simpa [C, I] using sharp.2.1.le
  obtain ⟨d⟩ := (ih I.card hClt I (by simp) (fun j : I => p j)
    (fun j => hp j) (fun j => ho j) C τ a.fixed_faithful).1
      (fun j => hall j) hCdim
  refine ⟨⟨a, d, ?_⟩⟩
  rcases sharp.2.2.2 with ⟨hn, hw⟩ | ⟨hn, hw⟩
  · exact Or.inl ⟨hn, by omega⟩
  · exact Or.inr ⟨hn, by omega⟩

theorem preparedSplit_five
    (split : DihedralSplittingTheorem.{v}) (bounds : DihedralDegreeTheorem.{v})
    (ih : ∀ s, s < Fintype.card ι → EqualityAt.{v} s)
    (hp : ∀ j, (p j).Prime) (ho : ∀ j, Odd (p j))
    (hf : Function.Injective σ) (j : ι) (hji : j ≠ i) (hj : p j = 5)
    (hd : Module.finrank (ZMod 2) W ≤ 2 * (Fintype.card ι + 1)) :
    Nonempty (PreparedSplit σ i True) := by
  obtain ⟨a⟩ := exists_splitActions split hp ho σ hf i
  let I := Finset.univ.erase i \ a.J
  let C := rotationFixed (factorRep σ i)
  let U := reflectionHalf (factorRep σ i)
  let τ := Representation.subrepresentation (σ.comp (subproductHom I)) C a.fixed_stable
  let υ := Representation.subrepresentation (σ.comp (subproductHom a.J)) U a.half_stable
  have hc := split_card a
  have hC := dihedralDegree_fintype bounds (fun j : I => p j)
    (fun j => hp j) (fun j => ho j) τ a.fixed_faithful
  have hU := dihedralDegree_fintype bounds (fun j : a.J => p j)
    (fun j => hp j) (fun j => ho j) υ a.half_faithful
  simp only [Fintype.card_coe] at hC hU
  obtain ⟨hDim, hM, hpos⟩ := split_dimensions (factorRep σ i) split (hp i) (ho i)
    (factorRep_injective σ hf i)
  have hjI : j ∈ I := by
    rcases split_mem a j hji with h | h
    · exact h
    · have hlarge := hU.2.1 ⟨⟨j, h⟩, by simp [hj]⟩
      exact (exceptional_half_space_impossible hc hDim hd hC.1 hlarge
        (Finset.card_pos.mpr ⟨j, h⟩)).elim
  have hlarge := hC.2.1 ⟨⟨j, hjI⟩, by simp [hj]⟩
  have sharp := split_dimensions_rigid hc hDim hd hlarge hU.1 hpos
  have hClt : I.card < Fintype.card ι := by dsimp [I]; omega
  have hCdim : Module.finrank (ZMod 2) C ≤ 2 * (I.card + 1) := sharp.2.1.le
  obtain ⟨d⟩ := (ih I.card hClt I (by simp) (fun j : I => p j)
    (fun j => hp j) (fun j => ho j) C τ a.fixed_faithful).2 ⟨⟨j, hjI⟩, hj⟩ hCdim
  refine ⟨⟨a, d, ?_⟩⟩
  rcases sharp.2.2.2 with ⟨hn, hw⟩ | ⟨hn, hw⟩
  · exact Or.inl ⟨hn, by omega⟩
  · exact Or.inr ⟨hn, by omega⟩

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep
