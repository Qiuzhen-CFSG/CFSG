module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Candidates

/-!
# Common words and fixed subgroups for the concrete triality Weyl group

The root-side words use the literal D4 reflections, while the matrix-side words
are the published Geck representatives. Multiplication in the three commuting
pinned SL₂ images identifies the arm word with the product of simple Weyl words
at vertices 0, 2 and 3. Thus every published representative lies in the split
Weyl subgroup and is fixed by the graph-field action. Frobenius is trivial on
this entire split Weyl subgroup, so graph-field fixedness there is exactly
fixedness under the diagram action.

These are boundary facts for the Weyl realization. No multiplicativity or
faithfulness of the dihedral-indexed words, and no exhaustive description of
either fixed subgroup, is assumed or asserted here.

Source: GLS3 §§2.3.1–8 and 2.4, in particular the product of orthogonal-arm
reflections in 2.4.4 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.ConcreteBruhat
open Parabolics ElementaryCentralKernel
noncomputable section

theorem splitWeylGenerator_mem (P : Parameters) (i : Fin 4) :
    weylWord P i 1 ∈ splitWeylSubgroup P :=
  Subgroup.subset_closure ⟨i, rfl⟩

/-- A numbered simple matrix word as an element of the generated subgroup. -/
def splitWeylGenerator (P : Parameters) (i : Fin 4) : splitWeylSubgroup P :=
  ⟨weylWord P i 1, splitWeylGenerator_mem P i⟩

/-- A numbered reflection as an element of the literal root Weyl group. -/
def rootWeylGenerator (i : Fin 4) : rootWeylGroup :=
  ⟨rootReflection i, Subgroup.subset_closure (Set.mem_range_self i)⟩

/-- The product of the three arm reflections, or the central reflection. -/
def foldedRootReflection : Node → rootWeylGroup
  | .arms => rootWeylGenerator 0 * rootWeylGenerator 2 * rootWeylGenerator 3
  | .central => rootWeylGenerator 1

/-- Dihedral-indexed root words, without a presumed multiplication law. -/
def rootRepresentative : DihedralGroup 6 → rootWeylGroup
  | .r i => (foldedRootReflection .arms * foldedRootReflection .central) ^ i.val
  | .sr i => foldedRootReflection .arms *
      (foldedRootReflection .arms * foldedRootReflection .central) ^ i.val

/-- The actual centralizer of the diagram permutation inside the root Weyl group. -/
def fixedRootWeylSubgroup : Subgroup rootWeylGroup :=
  (Subgroup.centralizer {typeD4DiagramEquiv.indexEquiv}).comap rootWeylGroup.subtype

/-- The graph-field fixed subgroup of the actual split matrix Weyl subgroup. -/
def fixedSplitWeylSubgroup (P : Parameters) : Subgroup (splitWeylSubgroup P) :=
  (fixedSubgroup P).comap (splitWeylSubgroup P).subtype

private theorem invariant_of_cube {G : Type*} [Group G] (f : G ≃* G)
    (hf : ∀ x, f (f (f x)) = x) (H : Subgroup G)
    (h : ∀ x ∈ H, f x ∈ H) : H.map f.toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · intro x hx
    exact ⟨f (f x), h _ (h _ hx), hf x⟩

theorem splitWeylSubgroup_invariant (P : Parameters) :
    (splitWeylSubgroup P).map (graphFieldAutomorphism P).toMonoidHom =
      splitWeylSubgroup P := by
  apply invariant_of_cube _ (graphFieldAutomorphism_three P)
  change splitWeylSubgroup P ≤
    (splitWeylSubgroup P).comap (graphFieldAutomorphism P).toMonoidHom
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i, rfl⟩
  change graphFieldAutomorphism P (weylWord P i 1) ∈ splitWeylSubgroup P
  simpa using splitWeylGenerator_mem P (typeD4DiagramPermutation i)

/-- Restriction of the actual graph-field automorphism to its invariant Weyl subgroup. -/
def splitWeylGraphField (P : Parameters) : splitWeylSubgroup P ≃* splitWeylSubgroup P :=
  ((graphFieldAutomorphism P).subgroupMap (splitWeylSubgroup P)).trans
    (MulEquiv.subgroupCongr (splitWeylSubgroup_invariant P))

@[simp] theorem splitWeylGraphField_val (P : Parameters) (w : splitWeylSubgroup P) :
    (splitWeylGraphField P w).val = graphFieldAutomorphism P w.val := rfl

theorem splitTorus_invariant (P : Parameters) :
    (splitTorus P).map (graphFieldAutomorphism P).toMonoidHom = splitTorus P := by
  apply invariant_of_cube _ (graphFieldAutomorphism_three P)
  change splitTorus P ≤ (splitTorus P).comap (graphFieldAutomorphism P).toMonoidHom
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i, t, rfl⟩
  change graphFieldAutomorphism P (torusWord P i t) ∈ splitTorus P
  rw [graphField_torusWord]
  exact Subgroup.subset_closure ⟨_, _, rfl⟩

theorem fieldAutomorphism_weylWord_one (P : Parameters) (i : Fin 4) :
    fieldAutomorphism P (weylWord P i 1) = weylWord P i 1 := by
  have hneg : (-1 : ExtensionField P) ^ P.q = -1 := by
    change fieldFrobenius P (-1) = -1
    rw [map_neg, map_one]
  simp [weylWord, positiveRoot, negativeRoot, hneg]

theorem fieldAutomorphism_eq_self_of_mem_splitWeylSubgroup (P : Parameters)
    {g : SplitGroup P} (hg : g ∈ splitWeylSubgroup P) : fieldAutomorphism P g = g := by
  have h : splitWeylSubgroup P ≤
      MonoidHom.eqLocus (fieldAutomorphism P).toMonoidHom (MonoidHom.id _) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨i, rfl⟩
    exact fieldAutomorphism_weylWord_one P i
  exact h hg

theorem graphField_eq_diagram_of_mem_splitWeylSubgroup (P : Parameters)
    {g : SplitGroup P} (hg : g ∈ splitWeylSubgroup P) :
    graphFieldAutomorphism P g = diagramAutomorphism P g := by
  change fieldAutomorphism P (diagramAutomorphism P g) = _
  rw [← diagram_field_commute, fieldAutomorphism_eq_self_of_mem_splitWeylSubgroup P hg]

private abbrev upper (P : Parameters) : SL(2, ExtensionField P) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) 1
private abbrev lower (P : Parameters) : SL(2, ExtensionField P) :=
  SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) 1

private theorem pinned_weyl (P : Parameters) (hp : P.prime = 2)
    (D : PinnedRankOneMaps P) (i : Fin 4) :
    D.hom i (upper P * lower P * upper P) = weylWord P i 1 := by
  let := rankOneExtensionCharTwo P hp
  simp only [map_mul, upper, lower, D.positive, D.negative, weylWord,
    inv_one, CharTwo.neg_eq]

private theorem elementaryInclusion_simple_arms_with (P : Parameters) (hp : P.prime = 2)
    (D : PinnedRankOneMaps P) (C : ArmRootCommutation P) :
    elementaryInclusion P (simpleElementary P hp .arms) =
      weylWord P 0 1 * weylWord P 2 1 * weylWord P 3 1 := by
  have hu : D.armsProduct C ((upper P, upper P), upper P) = foldedRoot P true 1 := by
    simp [PinnedRankOneMaps.armsProduct_apply, upper, D.positive, foldedRoot, simpleRoot]
  have hl : D.armsProduct C ((lower P, lower P), lower P) = foldedRoot P false 1 := by
    simp [PinnedRankOneMaps.armsProduct_apply, lower, D.negative, foldedRoot, simpleRoot]
  change foldedRoot P true 1 * foldedRoot P false 1 * foldedRoot P true 1 = _
  calc
    _ = D.armsProduct C
        (((upper P, upper P), upper P) * ((lower P, lower P), lower P) *
          ((upper P, upper P), upper P)) := by
      rw [map_mul, map_mul, hu, hl]
    _ = _ := by
      change D.hom 0 (upper P * lower P * upper P) *
        D.hom 2 (upper P * lower P * upper P) *
        D.hom 3 (upper P * lower P * upper P) = _
      simp only [pinned_weyl P hp]

/-- The folded arm word is exactly the product of the three simple matrix words. -/
theorem elementaryInclusion_simple_arms (P : Parameters) (hp : P.prime = 2) :
    elementaryInclusion P (simpleElementary P hp .arms) =
      weylWord P 0 1 * weylWord P 2 1 * weylWord P 3 1 :=
  elementaryInclusion_simple_arms_with P hp (pinnedRankOneMaps P hp) (armRootCommutation P hp)

/-- The central folded word is the numbered central simple matrix word. -/
theorem elementaryInclusion_simple_central (P : Parameters) (hp : P.prime = 2) :
    elementaryInclusion P (simpleElementary P hp .central) = weylWord P 1 1 := by
  let := rankOneExtensionCharTwo P hp
  change positiveRoot P 1 1 * negativeRoot P 1 1 * positiveRoot P 1 1 = _
  simp only [weylWord, inv_one, CharTwo.neg_eq]

theorem elementaryInclusion_simple_mem (P : Parameters) (hp : P.prime = 2) (a : Node) :
    elementaryInclusion P (simpleElementary P hp a) ∈ splitWeylSubgroup P := by
  cases a with
  | arms =>
    rw [elementaryInclusion_simple_arms]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (splitWeylGenerator_mem P 0)
      (splitWeylGenerator_mem P 2)) (splitWeylGenerator_mem P 3)
  | central =>
    rw [elementaryInclusion_simple_central]
    exact splitWeylGenerator_mem P 1

theorem splitRepresentative_mem (P : Parameters) (hp : P.prime = 2) (w : DihedralGroup 6) :
    splitRepresentative P hp w ∈ splitWeylSubgroup P := by
  have hab := (splitWeylSubgroup P).mul_mem
    (elementaryInclusion_simple_mem P hp .arms) (elementaryInclusion_simple_mem P hp .central)
  cases w <;> simp only [splitRepresentative, weylElementary, map_mul, map_pow]
  · exact (splitWeylSubgroup P).pow_mem hab _
  · exact (splitWeylSubgroup P).mul_mem (elementaryInclusion_simple_mem P hp .arms)
      ((splitWeylSubgroup P).pow_mem hab _)

theorem graphField_splitRepresentative (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) :
    graphFieldAutomorphism P (splitRepresentative P hp w) = splitRepresentative P hp w :=
  (weylElementary P hp w).val.property

/-- The published representative bundled in the actual fixed split Weyl subgroup. -/
def fixedSplitRepresentative (P : Parameters) (hp : P.prime = 2)
    (w : DihedralGroup 6) : fixedSplitWeylSubgroup P :=
  ⟨⟨splitRepresentative P hp w, splitRepresentative_mem P hp w⟩,
    graphField_splitRepresentative P hp w⟩

@[simp] theorem splitRepresentative_one (P : Parameters) (hp : P.prime = 2) :
    splitRepresentative P hp 1 = 1 := by
  simp [splitRepresentative]

@[simp] theorem splitRepresentative_simple (P : Parameters) (hp : P.prime = 2) (a : Node) :
    splitRepresentative P hp (relativeReflection a) =
      elementaryInclusion P (simpleElementary P hp a) :=
  congrArg (elementaryInclusion P) (weylElementary_simple P hp a)

@[simp] theorem mem_fixedRootWeylSubgroup (w : rootWeylGroup) :
    w ∈ fixedRootWeylSubgroup ↔
      typeD4DiagramEquiv.indexEquiv * w.val = w.val * typeD4DiagramEquiv.indexEquiv := by
  change w.val ∈ Subgroup.centralizer {typeD4DiagramEquiv.indexEquiv} ↔ _
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]

@[simp] theorem mem_fixedSplitWeylSubgroup (P : Parameters) (w : splitWeylSubgroup P) :
    w ∈ fixedSplitWeylSubgroup P ↔ diagramAutomorphism P w.val = w.val := by
  change graphFieldAutomorphism P w.val = w.val ↔ _
  rw [graphField_eq_diagram_of_mem_splitWeylSubgroup P w.property]

end
end Triality.Standard.ConcreteBruhat
