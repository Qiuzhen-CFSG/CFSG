module
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Cosets

/-!
# Transitivity on nested pairs of binary subspaces

An automorphism of a subspace extends to its ambient finite-dimensional
space. Applying this to the two restricted smaller subspaces proves that a
parabolic is transitive on its subspaces of any fixed dimension. First move
the larger subspace, then apply this parabolic action to the smaller one.
This proves flag transitivity with both prescribed images retained.

The consumer is the marked point-residue flag in Aschbacher, *Sporadic Groups*
(1994), 41.1, printed pp.219–220.
-/

public noncomputable section
namespace BinaryLinear.FourParabolicAction
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Subspaces of equal dimension inside W are conjugate under its parabolic. -/
theorem exists_parabolic_map_eq (W A B : Submodule (ZMod 2) V)
    (hA : A ≤ W) (hB : B ≤ W)
    (hd : Module.finrank (ZMod 2) A = Module.finrank (ZMod 2) B) :
    ∃ g : GL V, g ∈ parabolic W ∧ A.map g.toLinearMap = B := by
  have hdim : Module.finrank (ZMod 2) (A.comap W.subtype) =
      Module.finrank (ZMod 2) (B.comap W.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hA).finrank_eq.trans
      (hd.trans (Submodule.comapSubtypeEquivOfLe hB).finrank_eq.symm)
  obtain ⟨f, hf⟩ := exists_linearEquiv_map_eq (A.comap W.subtype) (B.comap W.subtype) hdim
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hW : W.map g.toLinearMap = W := by
    apply le_antisymm
    · rintro v ⟨w, hw, rfl⟩
      change g w ∈ W
      rw [← hg ⟨w, hw⟩]
      exact (f ⟨w, hw⟩).property
    · intro v hv
      refine ⟨f.symm ⟨v, hv⟩, (f.symm ⟨v, hv⟩).property, ?_⟩
      exact (hg (f.symm ⟨v, hv⟩)).symm.trans
        (congrArg Subtype.val (f.apply_symm_apply ⟨v, hv⟩))
  have hpar : g ∈ parabolic W := by
    have hh := (map_eq_map_iff W 1 g).mp (by simpa using hW.symm)
    simpa using hh
  refine ⟨g, hpar, ?_⟩
  apply le_antisymm
  · rintro v ⟨a, ha, rfl⟩
    have hfa : f ⟨a, hA ha⟩ ∈ B.comap W.subtype := by
      rw [← hf]
      exact ⟨⟨a, hA ha⟩, ha, rfl⟩
    change (f ⟨a, hA ha⟩ : V) ∈ B at hfa
    rwa [hg] at hfa
  · intro b hb
    have hbm : (⟨b, hB hb⟩ : W) ∈ (A.comap W.subtype).map f.toLinearMap := by
      rw [hf]
      exact hb
    obtain ⟨a, ha, he⟩ := hbm
    refine ⟨a, ha, ?_⟩
    exact (hg a).symm.trans (congrArg Subtype.val he)

/-- The full binary linear group is transitive on incident pairs of fixed dimensions. -/
theorem exists_linearEquiv_map_flag (A B A' B' : Submodule (ZMod 2) V)
    (hAB : A ≤ B) (hAB' : A' ≤ B')
    (hA : Module.finrank (ZMod 2) A = Module.finrank (ZMod 2) A')
    (hB : Module.finrank (ZMod 2) B = Module.finrank (ZMod 2) B') :
    ∃ g : GL V, A.map g.toLinearMap = A' ∧ B.map g.toLinearMap = B' := by
  obtain ⟨f, hf⟩ := exists_linearEquiv_map_eq B B' hB
  have hAf : A.map f.toLinearMap ≤ B' := hf ▸ Submodule.map_mono hAB
  obtain ⟨g, hg, hga⟩ := exists_parabolic_map_eq B' (A.map f.toLinearMap) A' hAf hAB'
    ((f.finrank_map_eq A).trans hA)
  refine ⟨g * f, ?_, ?_⟩
  · rw [← Submodule.map_comp] at hga
    exact hga
  · have hgb : B'.map g.toLinearMap = B' := by
      have hh := (map_eq_map_iff B' 1 g).mpr (by simpa using hg)
      simpa using hh.symm
    calc
      B.map (g * f).toLinearMap = (B.map f.toLinearMap).map g.toLinearMap := by
        rw [← Submodule.map_comp]; rfl
      _ = B' := by rw [hf, hgb]

end BinaryLinear.FourParabolicAction
