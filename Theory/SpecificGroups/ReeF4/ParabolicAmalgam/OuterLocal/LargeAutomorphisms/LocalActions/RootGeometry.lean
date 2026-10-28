module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.FieldSubgroups
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.FixedGeometryTransport
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.Disjoint

/-!
# Signed root blocks in the canonical Ree carrier

The opposite positive subgroup and the four signed simple blocks are the
intersections of the existing split root closures with `Model m`. The comparison
with a supplied exceptional map preserves these intersections, since it preserves
the underlying split matrices. Positive and negative blocks lie in the respective
unipotent subgroups, whose intersection is trivial. Frobenius preserves all four
blocks and the opposite subgroup.

These are geometric definitions and comparison results for the local calculation
in GLS3, Sections 2.3--2.5, especially Table 2.4 (types V and VI) and 2.5.1
(`refs/KGroup/GLS3/chapter2.tex`). Generation and recognition of these subgroups
by arbitrary automorphisms remain separate obligations. No simplicity or
perfectness assumption is made.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions

open Subgroup LargeLocalSeeds

/-- The actual negative-root fixed intersection in the canonical matrix group. -/
def oppositeUnipotent (m : ℕ) : Subgroup (Model m) :=
  (LocalBlockInput.splitNegativeUnipotent m).comap (toSplitGroup m)

/-- A signed simple relative root group, including the full B₂ block on the
Suzuki side. The Boolean `true` specifies the positive sign. -/
def simpleBlock (m : ℕ) (s : Side) (positive : Bool) : Subgroup (Model m) :=
  (LocalBlockInput.PairRigidity.splitSimpleBlock m s positive).comap (toSplitGroup m)

/-- Preservation of both actual positive and negative fixed subgroups. -/
def PreservesUnipotentPair (m : ℕ) (a : MulAut (Model m)) : Prop :=
  (unipotent m).map a.toMonoidHom = unipotent m ∧
    (oppositeUnipotent m).map a.toMonoidHom = oppositeUnipotent m

/-- Individual preservation of the four specified signed root blocks. -/
def PreservesSimpleBlocks (m : ℕ) (a : MulAut (Model m)) : Prop :=
  ∀ s positive, (simpleBlock m s positive).map a.toMonoidHom = simpleBlock m s positive

private theorem modelEquiv_map_intersection {m : ℕ} (d : LocalBlockInput m)
    (H : Subgroup (SplitGroup m)) :
    (H.subgroupOf d.fixedGroup).map d.modelEquiv.toMonoidHom =
      H.comap (toSplitGroup m) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change toSplitGroup m (d.modelEquiv y) ∈ H
    rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]
    exact hy
  · intro hx
    refine ⟨d.modelEquiv.symm x, ?_, d.modelEquiv.apply_symm_apply x⟩
    change (d.modelEquiv.symm x).val ∈ H
    rw [modelEquiv_symm_coe]
    simpa only [mem_comap, toSplitGroup_apply] using hx

/-- The comparison preserves the opposite subgroup as an actual matrix set. -/
theorem modelEquiv_map_oppositeUnipotent {m : ℕ} (d : LocalBlockInput m) :
    (LocalBlockInput.oppositeUnipotent d).map d.modelEquiv.toMonoidHom =
      oppositeUnipotent m :=
  modelEquiv_map_intersection d _

/-- The comparison preserves all four actual signed blocks. -/
theorem modelEquiv_map_simpleBlock {m : ℕ} (d : LocalBlockInput m)
    (s : Side) (positive : Bool) :
    (LocalBlockInput.PairRigidity.simpleBlock d s positive).map
      d.modelEquiv.toMonoidHom = simpleBlock m s positive :=
  modelEquiv_map_intersection d _

/-- The two concrete constructions of Frobenius agree under the comparison. -/
theorem modelEquiv_fieldAutomorphism {m : ℕ} (d : LocalBlockInput m)
    (x : d.fixedGroup) :
    d.modelEquiv (d.fieldAutomorphism x) = fieldAutomorphism m (d.modelEquiv x) := by
  apply toSplitGroup_injective m
  rw [fieldAutomorphism_coe]
  simp only [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe,
    LocalBlockInput.fieldAutomorphism_coe]

/-- The actual positive and negative fixed subgroups intersect trivially. -/
theorem unipotent_disjoint_opposite (m : ℕ) :
    Disjoint (unipotent m) (oppositeUnipotent m) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hy
  apply toSplitGroup_injective m
  rw [map_one]
  exact (Subgroup.disjoint_def.mp
    (LocalBlockInput.PairNormalization.splitUnipotent_disjoint_negative m)) hx hy

theorem simpleBlock_positive_le (m : ℕ) (s : Side) :
    simpleBlock m s true ≤ unipotent m := by
  rw [← modelEquiv_map_simpleBlock (canonicalLocalBlockInput m),
    ← modelEquiv_map_standardUnipotent (canonicalLocalBlockInput m)]
  exact Subgroup.map_mono
    (LocalBlockInput.PairRigidity.simpleBlock_positive_le (canonicalLocalBlockInput m) s)

theorem simpleBlock_negative_le (m : ℕ) (s : Side) :
    simpleBlock m s false ≤ oppositeUnipotent m := by
  rw [← modelEquiv_map_simpleBlock (canonicalLocalBlockInput m),
    ← modelEquiv_map_oppositeUnipotent (canonicalLocalBlockInput m)]
  exact Subgroup.map_mono
    (LocalBlockInput.PairRigidity.simpleBlock_negative_le (canonicalLocalBlockInput m) s)

private theorem field_map_intersection {m : ℕ} (d : LocalBlockInput m)
    (H : Subgroup d.fixedGroup)
    (hH : H.map d.fieldAutomorphism.toMonoidHom = H) :
    (H.map d.modelEquiv.toMonoidHom).map (fieldAutomorphism m).toMonoidHom =
      H.map d.modelEquiv.toMonoidHom := by
  have he : (fieldAutomorphism m).toMonoidHom.comp d.modelEquiv.toMonoidHom =
      d.modelEquiv.toMonoidHom.comp d.fieldAutomorphism.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact (modelEquiv_fieldAutomorphism d x).symm
  rw [Subgroup.map_map, he, ← Subgroup.map_map, hH]

/-- Frobenius preserves the negative root subgroup as well. -/
theorem fieldAutomorphism_oppositeUnipotent (m : ℕ) :
    (oppositeUnipotent m).map (fieldAutomorphism m).toMonoidHom =
      oppositeUnipotent m := by
  rw [← modelEquiv_map_oppositeUnipotent (canonicalLocalBlockInput m)]
  exact field_map_intersection (canonicalLocalBlockInput m) _
    (LocalBlockInput.fieldAutomorphism_preservesUnipotentPair (canonicalLocalBlockInput m)).2

/-- Frobenius preserves each signed simple block. -/
theorem fieldAutomorphism_simpleBlock (m : ℕ) (s : Side) (positive : Bool) :
    (simpleBlock m s positive).map (fieldAutomorphism m).toMonoidHom =
      simpleBlock m s positive := by
  rw [← modelEquiv_map_simpleBlock (canonicalLocalBlockInput m)]
  exact field_map_intersection (canonicalLocalBlockInput m) _
    (LocalBlockInput.PairRigidity.fieldAutomorphism_preservesSimpleBlocks
      (canonicalLocalBlockInput m) s positive)

/-- Generation by the supplied fixed blocks transfers to the canonical model. -/
theorem simpleBlocks_generate_of_standard {m : ℕ} (d : LocalBlockInput m)
    (hgen : (⨆ s, ⨆ positive, LocalBlockInput.PairRigidity.simpleBlock d s positive) = ⊤) :
    (⨆ s, ⨆ positive, simpleBlock m s positive) = ⊤ := by
  have h := congrArg (fun H : Subgroup d.fixedGroup => H.map d.modelEquiv.toMonoidHom) hgen
  simpa only [Subgroup.map_iSup, modelEquiv_map_simpleBlock,
    Subgroup.map_top_of_surjective d.modelEquiv.toMonoidHom d.modelEquiv.surjective] using h

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions
