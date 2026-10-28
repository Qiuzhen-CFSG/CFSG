/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Mathieu/Mathieu22PairStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu22PointStabilizer
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PairStabilizer

/-!
The setwise stabilizer of a marked pair in the concrete Mathieu coordinate action.
The proof identifies the pointwise Mathieu kernel and counts the pair action.

Source: Gerald Höhn, `Atlas/Mathieu/Mathieu22PairStabilizer.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

abbrev Mathieu22PairModel (a : Omega) (b : Mathieu23Points a) :=
  Atlas.GroupTheory.PairStabilizer (G := Mathieu24CodeModel) a b.val

theorem mathieu22_range_fixing (a : Omega) (b : Mathieu23Points a) :
    (mathieu22_embedding a b).range = fixingSubgroup Mathieu24CodeModel ({a,b.val} : Set Omega) := by
  ext g
  rw [mathieu22_image]
  simp [mem_fixingSubgroup_iff]

def mathieu22FixingEquiv (a : Omega) (b : Mathieu23Points a) :
    Mathieu22PointModel a b ≃* fixingSubgroup Mathieu24CodeModel ({a,b.val} : Set Omega) :=
  (MonoidHom.ofInjective (mathieu22_embedding_injective a b)).trans
    (MulEquiv.subgroupCongr (mathieu22_range_fixing a b))

def mathieu22PairRestriction (a : Omega) (b : Mathieu23Points a) :
    Mathieu22PairModel a b →* Equiv.Perm ({a,b.val} : Set Omega) :=
  Atlas.GroupTheory.pairRestrictionHom a b.val

def mathieu22PairKernelEquiv (a : Omega) (b : Mathieu23Points a) :
    (mathieu22PairRestriction a b).ker ≃* Mathieu22PointModel a b :=
  (Atlas.GroupTheory.pairRestrictionKernelEquiv a b.val (Ne.symm b.prop)).trans
    (mathieu22FixingEquiv a b).symm

theorem mathieu22PairKernelEquiv_embedding (a : Omega) (b : Mathieu23Points a)
    (g : (mathieu22PairRestriction a b).ker) :
    mathieu22_embedding a b (mathieu22PairKernelEquiv a b g) = g.val.val := by
  have he := (mathieu22FixingEquiv a b).apply_symm_apply
    (Atlas.GroupTheory.pairRestrictionKernelEquiv a b.val (Ne.symm b.prop) g)
  exact congrArg (fun h : fixingSubgroup Mathieu24CodeModel ({a,b.val} : Set Omega) => h.val) he

def mathieu22_to_pair (a : Omega) (b : Mathieu23Points a) :
    Mathieu22PointModel a b →* Mathieu22PairModel a b where
  toFun h := ⟨mathieu22_embedding a b h,
    (Atlas.GroupTheory.pairStabilizer_mem a b.val (Ne.symm b.prop) _).mpr
      (Or.inl ⟨h.val.prop,congrArg Subtype.val h.prop⟩)⟩
  map_one' := by apply Subtype.ext; exact map_one (mathieu22_embedding a b)
  map_mul' g h := by apply Subtype.ext; exact map_mul (mathieu22_embedding a b) g h

theorem mathieu22_to_pair_injective (a : Omega) (b : Mathieu23Points a) :
    Function.Injective (mathieu22_to_pair a b) := by
  intro g h he
  exact mathieu22_embedding_injective a b
    (congrArg (fun x : Mathieu22PairModel a b => x.val) he)

theorem mathieu22_to_pair_embedding (a : Omega) (b : Mathieu23Points a)
    (h : Mathieu22PointModel a b) :
    (mathieu22_to_pair a b h).val = mathieu22_embedding a b h := rfl

theorem mathieu22_to_pair_range (a : Omega) (b : Mathieu23Points a) :
    (mathieu22_to_pair a b).range = (mathieu22PairRestriction a b).ker := by
  ext g
  constructor
  · rintro ⟨h,rfl⟩
    unfold mathieu22PairRestriction
    rw [Atlas.GroupTheory.pairRestriction_ker a b.val (Ne.symm b.prop)]
    exact Subtype.ext h.val.prop
  · intro hg
    exact ⟨mathieu22PairKernelEquiv a b ⟨g,hg⟩,
      Subtype.ext (mathieu22PairKernelEquiv_embedding a b ⟨g,hg⟩)⟩

theorem mathieu24_double_pretransitive :
    MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 2 := by
  have := mathieu24_four_transitive
  exact MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 4) (by simp [Omega])

theorem mathieu22PairRestriction_surjective (a : Omega) (b : Mathieu23Points a) :
    Function.Surjective (mathieu22PairRestriction a b) := by
  have := mathieu24_double_pretransitive
  exact Atlas.GroupTheory.pairRestriction_surjective a b.val (Ne.symm b.prop)

theorem mathieu22Pair_order (a : Omega) (b : Mathieu23Points a) :
    Nat.card (Mathieu22PairModel a b) = 887040 := by
  have := mathieu24_double_pretransitive
  have h := Atlas.GroupTheory.pairStabilizer_order (G := Mathieu24CodeModel) a b.val (Ne.symm b.prop)
  rw [← Nat.card_congr (mathieu22FixingEquiv a b).toEquiv,mathieu22_order] at h
  exact h

theorem mathieu22Pair_kernel_index (a : Omega) (b : Mathieu23Points a) :
    (mathieu22PairRestriction a b).ker.index = 2 := by
  have h := (mathieu22PairRestriction a b).ker.card_mul_index
  rw [Nat.card_congr (mathieu22PairKernelEquiv a b).toEquiv,
    mathieu22_order,mathieu22Pair_order] at h
  omega

end Atlas.Codes
