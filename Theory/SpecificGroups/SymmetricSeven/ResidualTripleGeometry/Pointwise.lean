module

public import Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition.Cubic
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Pointwise stabilizers for the residual triple in S₇

The source letters `1,...,7` correspond to coordinates `2,3,4,5,0,1,6`.
The block embeddings identify the pointwise fixers with S₃ and S₄. Taking
actual two-residuals identifies them with the cubic and duad residuals of
the index-three overgroups. In particular the cubic residual is supported
on `{0,1,6}`. Sixteen Sylow words certify the 4+2+1 block convention.

Source: Aschbacher–Smith, Lemma 14.4.11 and its first proof paragraph,
printed p.1011 (combined manuscript of 1 March 2004); B.3 for the letters.
-/

@[expose] public section
open Equiv Subgroup
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
open Theory.SpecificGroups.SymmetricSix
namespace Theory.SpecificGroups.SymmetricSeven.ResidualTripleGeometry
abbrev S3 := Equiv.Perm (Fin 3)
abbrev S4 := Equiv.Perm (Fin 4)
def sourceRelabelling : Fin 7 ≃ Fin 7 where
  toFun := ![2,3,4,5,0,1,6]
  invFun := ![4,5,0,1,2,3,6]
  left_inv := by decide
  right_inv := by decide

def blockEquiv : Fin 4 ⊕ Fin 3 ≃ Fin 7 := finSumFinEquiv.trans sourceRelabelling

def blockHom : S4 × S3 →* S7 :=
  (Equiv.permCongrHom blockEquiv).toMonoidHom.comp (Equiv.Perm.sumCongrHom _ _)

theorem blockHom_injective : Function.Injective blockHom :=
  (Equiv.permCongrHom _).injective.comp Equiv.Perm.sumCongrHom_injective

def fourHom : S4 →* S7 := blockHom.comp ((MonoidHom.id _).prod (1 : S4 →* S3))
def threeHom : S3 →* S7 := blockHom.comp ((1 : S3 →* S4).prod (MonoidHom.id _))

def fourFixer : Subgroup S7 := fixingSubgroup S7 ({2,3,4,5} : Set (Fin 7))
def threeFixer : Subgroup S7 := fixingSubgroup S7 ({0,1,6} : Set (Fin 7))

private def fourPoints : Fin 4 ≃ {i : Fin 7 // i ∈ ({2,3,4,5} : Finset (Fin 7))} where
  toFun i := ⟨blockEquiv (Sum.inl i), by revert i; decide⟩
  invFun i := ⟨i.val.val - 2, by have := i.property; simp only [Finset.mem_insert, Finset.mem_singleton] at this; rcases this with h|h|h|h <;> rw [h] <;> decide⟩
  left_inv := by decide
  right_inv := by decide
private def threePoints : Fin 3 ≃ {i : Fin 7 // i ∈ ({0,1,6} : Finset (Fin 7))} where
  toFun i := ⟨blockEquiv (Sum.inr i), by revert i; decide⟩
  invFun i := if i.val = 0 then 0 else if i.val = 1 then 1 else 2
  left_inv := by decide
  right_inv := by decide

private theorem fourHom_subtype : fourHom = Equiv.Perm.ofSubtype.comp
    (Equiv.permCongrHom fourPoints).toMonoidHom := by
  ext g i
  revert g i
  decide +kernel
private theorem threeHom_subtype : threeHom = Equiv.Perm.ofSubtype.comp
    (Equiv.permCongrHom threePoints).toMonoidHom := by
  ext g i
  revert g i
  decide +kernel

theorem fourHom_range : fourHom.range = threeFixer := by
  rw [fourHom_subtype, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (Equiv.permCongrHom fourPoints).surjective, ← MonoidHom.range_eq_map]
  ext g
  rw [Equiv.Perm.mem_range_ofSubtype_iff, threeFixer, mem_fixingSubgroup_iff]
  change (∀ i, i ∈ g.support → i ∈ ({2,3,4,5} : Finset (Fin 7))) ↔
    ∀ i ∈ ({0,1,6} : Set (Fin 7)), g i = i
  have hc : ∀ i : Fin 7, i ∈ ({2,3,4,5} : Finset (Fin 7)) ↔ i ∉ ({0,1,6} : Set (Fin 7)) := by decide
  simp only [hc, Equiv.Perm.mem_support]
  constructor
  · intro h i hi; by_contra hn; exact h i hn hi
  · intro h i hi hh; exact hi (h i hh)

theorem threeHom_range : threeHom.range = fourFixer := by
  rw [threeHom_subtype, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (Equiv.permCongrHom threePoints).surjective, ← MonoidHom.range_eq_map]
  ext g
  rw [Equiv.Perm.mem_range_ofSubtype_iff, fourFixer, mem_fixingSubgroup_iff]
  change (∀ i, i ∈ g.support → i ∈ ({0,1,6} : Finset (Fin 7))) ↔
    ∀ i ∈ ({2,3,4,5} : Set (Fin 7)), g i = i
  have hc : ∀ i : Fin 7, i ∈ ({0,1,6} : Finset (Fin 7)) ↔ i ∉ ({2,3,4,5} : Set (Fin 7)) := by decide
  simp only [hc, Equiv.Perm.mem_support]
  constructor
  · intro h i hi; by_contra hn; exact h i hn hi
  · intro h i hi hh; exact hi (h i hh)

private theorem residual_range {G : Type*} [Group G] [Finite G] (f : G →* S7) :
    (pResidual 2 f.range).map f.range.subtype = (pResidual 2 G).map f := by
  have h := map_embedded_pResidual 2 (⊤ : Subgroup G) f
  rw [← MonoidHom.range_eq_map] at h
  have ht := map_pResidual_of_surjective 2 (⊤ : Subgroup G).subtype
    (fun g => ⟨⟨g, mem_top g⟩, rfl⟩)
  rw [ht] at h
  exact h.symm

theorem residual_threeFixer : (pResidual 2 threeFixer).map threeFixer.subtype =
    (pResidual 2 duadOvergroup).map duadOvergroup.subtype := by
  rw [← fourHom_range, residual_range, Equiv.Perm.twoResidual_eq_alternating,
    residual_duadOvergroup, duadResidual7, ← MonoidHom.range_comp]
  rw [← range_subtype (alternatingGroup (Fin 4)), ← MonoidHom.range_comp]
  congr 1
  apply MonoidHom.ext
  intro a
  apply Equiv.ext
  intro i
  exact (show ∀ (a : ResidualPairRecognition.A) (i : Fin 7),
    fourHom a.val i = liftSix (ResidualPairRecognition.duadHom a) i by decide +kernel) a i

theorem residual_fourFixer : (pResidual 2 fourFixer).map fourFixer.subtype =
    (pResidual 2 cubicOvergroup).map cubicOvergroup.subtype := by
  rw [← threeHom_range, residual_range, Equiv.Perm.twoResidual_eq_alternating,
    residual_cubicOvergroup, cubicResidual7, MonoidHom.map_zpowers]
  let c : S3 := swap 0 1 * swap 1 2
  have ha : alternatingGroup (Fin 3) = zpowers c := by
    apply le_antisymm
    · intro g hg
      have ht : ∀ g : S3, g.sign = 1 → ∃ n : Fin 3, c ^ n.val = g := by decide
      obtain ⟨n, rfl⟩ := ht g hg
      exact pow_mem (mem_zpowers c) _
    · exact zpowers_le.mpr (show c ∈ alternatingGroup (Fin 3) from by change c.sign = 1; decide)
  rw [ha, MonoidHom.map_zpowers]
  congr 1
  decide


/-- The cubic residual on `{0,1,6}`, embedded in the seven-letter group. -/
def C : Subgroup S7 := (pResidual 2 cubicOvergroup).map cubicOvergroup.subtype
/-- The alternating residual on `{2,3,4,5}`, embedded in the seven-letter group. -/
def D : Subgroup S7 := (pResidual 2 duadOvergroup).map duadOvergroup.subtype
theorem C_eq : C = (alternatingGroup (Fin 3)).map threeHom := by
  rw [C, ← residual_fourFixer, ← threeHom_range, residual_range,
    Equiv.Perm.twoResidual_eq_alternating]

theorem D_eq : D = (alternatingGroup (Fin 4)).map fourHom := by
  rw [D, ← residual_threeFixer, ← fourHom_range, residual_range,
    Equiv.Perm.twoResidual_eq_alternating]

/-- The source letters `1,...,7` are zero-indexed before this relabelling. -/
theorem sourceRelabelling_apply : ∀ i : Fin 7,
    sourceRelabelling i = ![2,3,4,5,0,1,6] i := by decide

/-- The source 4+2+1 blocks become the actual blocks of the standard Sylow. -/
theorem source_partition_coordinates :
    ({{0,1,2,3},{4,5},{6}} : Finset (Finset (Fin 7))).image
      (fun s => s.image sourceRelabelling) = {{2,3,4,5},{0,1},{6}} := by decide

/-- The standard Sylow preserves each of the source blocks individually. -/
theorem standardTwo_preserves_blocks (g : S7) (hg : g ∈ standardTwo) :
    ({2,3,4,5} : Finset (Fin 7)).image g = {2,3,4,5} ∧
    ({0,1} : Finset (Fin 7)).image g = {0,1} ∧ g 6 = 6 := by
  obtain ⟨i, hi⟩ := sylowEquiv.surjective ⟨g,hg⟩
  have he : sylowWord i = g := congrArg Subtype.val hi
  rw [← he]
  exact (show ∀ i : Fin 16,
    ({2,3,4,5} : Finset (Fin 7)).image (sylowWord i) = {2,3,4,5} ∧
    ({0,1} : Finset (Fin 7)).image (sylowWord i) = {0,1} ∧
    sylowWord i 6 = 6 by decide +kernel) i


end Theory.SpecificGroups.SymmetricSeven.ResidualTripleGeometry
