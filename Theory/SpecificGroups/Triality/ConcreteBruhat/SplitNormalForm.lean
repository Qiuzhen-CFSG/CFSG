module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.Basic
public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.Tits
public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.Equivariance

/-!
# Concrete split D4 Bruhat normal forms and parabolic cells

For every positive binary parameter, the literal split Geck matrix group has a
unique expression `u * t * n(w) * v`. Here `u` is positive, `t` belongs to the
original split torus, `w` is an actual root Weyl permutation, and `v` is the
ordered twelve-root product with zero coordinates outside the inversion set
of `w`. The Weyl/torus hypotheses are exactly the published `Inputs`; their
concrete discharge remains with the parent construction.

The matrix collection and separation results construct the split Tits system.
Abstract Bruhat coverage and index separation then give the complete normal
form. The standard-parabolic theorem identifies the original generator-defined
parabolics with precisely the cells indexed by their marked Weyl subgroups.
Graph-field equivariance restricts this bijection to fixed points, retaining
the exact Frobenius equations on the supported right coordinates.

Source: GLS3 2.3.4–8, §2.4, and 2.6.4–8,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

open Theory.AlgebraicGroup
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm
open Parabolics
noncomputable section

/-- A positive simple curve witnesses nontriviality of simple-reflection
conjugation on the actual split Borel. -/
theorem simple_reflection_nontrivial (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (i : Fin 4) :
    ∃ b ∈ splitBorel (binaryParameters n hn),
      D.lift (rootWeylGenerator i) * b * D.lift (rootWeylGenerator i) ∉ splitBorel _ := by
  refine ⟨positiveRoot _ i 1,
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, 1, rfl⟩), ?_⟩
  rw [D.lift_simple, weylWord_positive _ rfl]
  exact CellSeparation.negativeRoot_not_borel n hn D i

/-- Distinct root Weyl elements index disjoint concrete Borel double cosets. -/
theorem cell_index_unique (n : ℕ) (hn : 0 < n) (D : Inputs (binaryParameters n hn))
    {v w : rootWeylGroup} {g : SplitGroup (binaryParameters n hn)}
    (hv : g ∈ cell D v) (hw : g ∈ cell D w) : v = w := by
  let := normalizer_intersection_normal n hn D
  apply (quotientEquiv n hn D).injective
  exact (splitTitsSystem n hn D).doubleCoset_index_unique
    ((cell_eq_quotient_cell n hn D v).le hv)
    ((cell_eq_quotient_cell n hn D w).le hw)

/-- Every literal split matrix belongs to a root Weyl cell. -/
theorem exists_mem_cell (n : ℕ) (hn : 0 < n) (D : Inputs (binaryParameters n hn))
    (g : SplitGroup (binaryParameters n hn)) : ∃ w, g ∈ cell D w := by
  let := normalizer_intersection_normal n hn D
  let T := splitTitsSystem n hn D
  obtain ⟨q, hq⟩ := T.exists_mem_doubleCoset g
  obtain ⟨w, hw⟩ := (quotientEquiv n hn D).surjective q
  refine ⟨w, (cell_eq_quotient_cell n hn D w).ge ?_⟩
  exact (congrArg (fun q => g ∈ T.bruhatCell q) hw).mpr hq

/-- Full uniqueness of the four factors, including the Weyl index. -/
theorem evaluate_injective (n : ℕ) (hn : 0 < n) (D : Inputs (binaryParameters n hn)) :
    Function.Injective (evaluate D) := by
  intro a b hab
  apply CellSeparation.coordinates_injective n hn D _ hab
  exact cell_index_unique n hn D (evaluate_mem_cell n hn D a)
    (hab.symm ▸ evaluate_mem_cell n hn D b)

/-- The split D4 Bruhat normal form, in the published twelve-root order. -/
theorem existsUnique_coordinates (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (g : SplitGroup (binaryParameters n hn)) :
    ∃! a : Coordinates (binaryParameters n hn), evaluate D a = g := by
  obtain ⟨w, hw⟩ := exists_mem_cell n hn D g
  obtain ⟨a, _, ha⟩ := exists_coordinates_of_mem_cell n hn D w hw
  exact ⟨a, ha, fun b hb => evaluate_injective n hn D (hb.trans ha.symm)⟩

/-- The actual split group is parametrized bijectively by its four factors. -/
def normalFormEquiv (n : ℕ) (hn : 0 < n) (D : Inputs (binaryParameters n hn)) :
    Coordinates (binaryParameters n hn) ≃ SplitGroup (binaryParameters n hn) :=
  Equiv.ofBijective (evaluate D) ⟨evaluate_injective n hn D,
    fun g => (existsUnique_coordinates n hn D g).exists⟩

@[simp] theorem normalFormEquiv_apply (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (a : Coordinates (binaryParameters n hn)) :
    normalFormEquiv n hn D a = evaluate D a := rfl

@[simp] theorem evaluate_normalForm (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (g : SplitGroup (binaryParameters n hn)) :
    evaluate D ((normalFormEquiv n hn D).symm g) = g :=
  (normalFormEquiv n hn D).apply_symm_apply g

/-- Membership of a coordinate expression in a cell reads off precisely its index. -/
theorem evaluate_mem_cell_iff (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (a : Coordinates (binaryParameters n hn))
    (w : rootWeylGroup) : evaluate D a ∈ cell D w ↔ a.weyl = w := by
  constructor
  · exact cell_index_unique n hn D (evaluate_mem_cell n hn D a)
  · rintro rfl
    exact evaluate_mem_cell n hn D a

/-- The original generator-defined parabolic is exactly the standard parabolic
of the split Tits system with the marked simple-root support. -/
theorem splitParabolic_eq_standardParabolic (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (a : Node) :
    letI := normalizer_intersection_normal n hn D
    splitParabolic (binaryParameters n hn) a =
      (splitTitsSystem n hn D).standardParabolic
        ((quotientEquiv n hn D) '' {w | ∃ i ∈ a.support, w = rootWeylGenerator i}) := by
  let := normalizer_intersection_normal n hn D
  let T := splitTitsSystem n hn D
  let e := quotientEquiv n hn D
  let I := e '' {w | ∃ i ∈ a.support, w = rootWeylGenerator i}
  change splitParabolic (binaryParameters n hn) a = T.standardParabolic I
  apply le_antisymm
  · rw [splitParabolic_eq_borel_sup_weyl (binaryParameters n hn) rfl a]
    apply sup_le (T.B_le_standardParabolic I)
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, hi, rfl⟩
    have hs : e (rootWeylGenerator i) ∈ I :=
      ⟨rootWeylGenerator i, ⟨i, hi, rfl⟩, rfl⟩
    have hc : D.lift (rootWeylGenerator i) ∈ cell D (rootWeylGenerator i) :=
      ⟨1, (splitBorel _).one_mem, 1, (splitBorel _).one_mem,
        by simp only [one_mul, mul_one]⟩
    have h := T.bruhatCell_subset_standardParabolic_of_mem hs
      ((cell_eq_bruhatCell n hn D _).le hc)
    simpa only [D.lift_simple] using h
  · apply T.standardParabolic_le _ le_sup_left
    rintro q ⟨w, ⟨i, hi, rfl⟩, rfl⟩ g hg
    exact cell_subset_splitParabolic (binaryParameters n hn) rfl D a
      (Subgroup.subset_closure ⟨i, hi, rfl⟩) ((cell_eq_bruhatCell n hn D _).ge hg)

/-- Exact cell coverage of the original split parabolic. -/
theorem mem_splitParabolic_iff_exists_cell (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (a : Node)
    (g : SplitGroup (binaryParameters n hn)) :
    g ∈ splitParabolic (binaryParameters n hn) a ↔
      ∃ w ∈ parabolicWeyl a, g ∈ cell D w := by
  let := normalizer_intersection_normal n hn D
  let T := splitTitsSystem n hn D
  let e := quotientEquiv n hn D
  let J := {w | ∃ i ∈ a.support, w = rootWeylGenerator i}
  let I := e '' J
  have hI : I ⊆ T.S := by
    rintro q ⟨w, ⟨i, _, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  constructor
  · intro hg
    have hp : g ∈ T.standardParabolic I :=
      (splitParabolic_eq_standardParabolic n hn D a).le hg
    obtain ⟨q, hq, hgq⟩ := (T.mem_standardParabolic_iff hI g).mp hp
    have hmap : (parabolicWeyl a).map e.toMonoidHom = Subgroup.closure I :=
      MonoidHom.map_closure e.toMonoidHom J
    obtain ⟨w, hw, hwq⟩ := hmap.ge hq
    refine ⟨w, hw, (cell_eq_bruhatCell n hn D w).ge ?_⟩
    exact (congrArg (fun q => g ∈ T.bruhatCell q) hwq).mpr hgq
  · rintro ⟨w, hw, hgw⟩
    exact cell_subset_splitParabolic (binaryParameters n hn) rfl D a hw hgw

/-- Parabolic membership of any point of a cell is equivalent to membership
of its root Weyl index in the subgroup on the original marked support. -/
theorem mem_splitParabolic_iff_of_mem_cell (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (a : Node)
    {g : SplitGroup (binaryParameters n hn)} {w : rootWeylGroup} (hg : g ∈ cell D w) :
    g ∈ splitParabolic (binaryParameters n hn) a ↔ w ∈ parabolicWeyl a := by
  constructor
  · intro hp
    obtain ⟨v, hv, hgv⟩ := (mem_splitParabolic_iff_exists_cell n hn D a g).mp hp
    exact (cell_index_unique n hn D hgv hg) ▸ hv
  · exact fun hw => cell_subset_splitParabolic (binaryParameters n hn) rfl D a hw hg

/-- The normal form decides membership in each original split parabolic. -/
theorem evaluate_mem_splitParabolic_iff (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (a : Node)
    (c : Coordinates (binaryParameters n hn)) :
    evaluate D c ∈ splitParabolic (binaryParameters n hn) a ↔ c.weyl ∈ parabolicWeyl a :=
  mem_splitParabolic_iff_of_mem_cell n hn D a (evaluate_mem_cell n hn D c)

/-- The unique normal form intertwines the genuine graph-field automorphism. -/
theorem normalForm_graphField (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (g : SplitGroup (binaryParameters n hn)) :
    (normalFormEquiv n hn D).symm (graphFieldAutomorphism _ g) =
      twist D ((normalFormEquiv n hn D).symm g) := by
  apply evaluate_injective n hn D
  exact ((normalFormEquiv n hn D).apply_symm_apply (graphFieldAutomorphism _ g)).trans
    ((congrArg (graphFieldAutomorphism _) ((normalFormEquiv n hn D).apply_symm_apply g)).symm.trans
      (evaluate_twist_binary n hn D _).symm)

/-- Fixedness holds factor by factor, with the exact inversion-coordinate
Frobenius equations; no assertion about fixed-point generation is used. -/
theorem evaluate_mem_fixed_iff (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (a : Coordinates (binaryParameters n hn)) :
    evaluate D a ∈ fixedSubgroup (binaryParameters n hn) ↔
      a.left.val ∈ fixedSubgroup (binaryParameters n hn) ∧
      a.torus.val ∈ fixedSubgroup (binaryParameters n hn) ∧
      D.weylTwist a.weyl = a.weyl ∧
      ∀ i, a.right (PositiveCoordinates.diagram i) =
        fieldFrobenius (binaryParameters n hn) (a.right i) :=
  evaluate_mem_fixed_iff_of_injective n hn D (evaluate_injective n hn D) a

/-- Restricting the actual normal form to fixed points is a bijection. -/
def fixedNormalFormEquiv (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) :
    {a : Coordinates (binaryParameters n hn) // twist D a = a} ≃
      fixedSubgroup (binaryParameters n hn) where
  toFun a := ⟨evaluate D a.val,
    (evaluate_mem_fixed_iff n hn D a.val).mpr ((twist_eq_self_iff D a.val).mp a.property)⟩
  invFun g := ⟨(normalFormEquiv n hn D).symm g.val, by
    have he := (normalFormEquiv n hn D).apply_symm_apply g.val
    apply (twist_eq_self_iff D _).mpr
    have hf : evaluate D ((normalFormEquiv n hn D).symm g.val) ∈
        fixedSubgroup (binaryParameters n hn) :=
      (congrArg (fun x : SplitGroup (binaryParameters n hn) =>
        x ∈ fixedSubgroup (binaryParameters n hn)) he).mpr g.property
    exact (evaluate_mem_fixed_iff n hn D _).mp hf⟩
  left_inv a := Subtype.ext ((normalFormEquiv n hn D).symm_apply_apply a.val)
  right_inv g := Subtype.ext ((normalFormEquiv n hn D).apply_symm_apply g.val)

end
end Triality.Standard.ConcreteBruhat.SplitNormalForm
