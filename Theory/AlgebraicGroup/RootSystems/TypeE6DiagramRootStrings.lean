module
public import Theory.AlgebraicGroup.RootSystems.TypeE6DiagramInvolution
public import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# Root-string invariance under the E6 diagram involution

The specified E6 diagram equivalence preserves root sums, differences, negation,
and the upper and lower root-string lengths.  The proof transports membership
in the root set through its bijective weight map and uses the characterization
of each chain coefficient as the supremum of the corresponding string.
These are the entrywise identities needed to lift the diagram action to Geck's
integral simple-root matrices.

Source: GLS3, §§2.1–2.3 (`refs/KGroup/GLS3/chapter2.tex`).
-/

namespace Theory.AlgebraicGroup.StandardRootSystem
@[expose] public section

@[simp] theorem typeE6Diagram_weight_root (r : typeE6Roots) :
    typeE6DiagramEquiv.weightMap (typeE6RootPairing.root r) =
      typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv r) :=
  congrFun typeE6DiagramEquiv.root_weightMap r

theorem typeE6Diagram_root_add_iff (r s t : typeE6Roots) :
    typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv r) =
      typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv s) +
        typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv t) ↔
    typeE6RootPairing.root r = typeE6RootPairing.root s + typeE6RootPairing.root t := by
  rw [← typeE6Diagram_weight_root, ← typeE6Diagram_weight_root,
    ← typeE6Diagram_weight_root, ← map_add]
  exact typeE6DiagramEquiv.bijective_weightMap.injective.eq_iff

theorem typeE6Diagram_root_sub_iff (r s t : typeE6Roots) :
    typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv r) =
      typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv s) -
        typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv t) ↔
    typeE6RootPairing.root r = typeE6RootPairing.root s - typeE6RootPairing.root t := by
  rw [← typeE6Diagram_weight_root, ← typeE6Diagram_weight_root,
    ← typeE6Diagram_weight_root, ← map_sub]
  exact typeE6DiagramEquiv.bijective_weightMap.injective.eq_iff

@[simp] theorem typeE6Diagram_neg (r : typeE6Roots) :
    let _ := typeE6RootPairing.indexNeg
    typeE6DiagramEquiv.indexEquiv (-r) = -typeE6DiagramEquiv.indexEquiv r := by
  let _ := typeE6RootPairing.indexNeg
  apply typeE6RootPairing.root.injective
  rw [← typeE6Diagram_weight_root]
  change typeE6DiagramEquiv.weightMap
      (typeE6RootPairing.root (typeE6RootPairing.reflectionPerm r r)) =
    typeE6RootPairing.root (typeE6RootPairing.reflectionPerm
      (typeE6DiagramEquiv.indexEquiv r) (typeE6DiagramEquiv.indexEquiv r))
  rw [typeE6RootPairing.root_reflectionPerm, typeE6RootPairing.reflection_apply_self,
    map_neg, typeE6Diagram_weight_root, typeE6RootPairing.root_reflectionPerm,
    typeE6RootPairing.reflection_apply_self]

private theorem diagram_linearIndependent (r s : typeE6Roots) :
    LinearIndependent ℝ ![typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv r),
      typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv s)] ↔
    LinearIndependent ℝ ![typeE6RootPairing.root r, typeE6RootPairing.root s] := by
  have h := typeE6DiagramEquiv.weightMap.linearIndependent_iff
    (LinearMap.ker_eq_bot.mpr typeE6DiagramEquiv.bijective_weightMap.injective)
      (v := ![typeE6RootPairing.root r, typeE6RootPairing.root s])
  have heq : typeE6DiagramEquiv.weightMap ∘
      ![typeE6RootPairing.root r, typeE6RootPairing.root s] =
      ![typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv r),
        typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv s)] := by
    funext i
    fin_cases i <;> exact typeE6Diagram_weight_root _
  rwa [heq] at h

private theorem diagram_mem_range (x : typeE6RootSpan) :
    typeE6DiagramEquiv.weightMap x ∈ Set.range typeE6RootPairing.root ↔
      x ∈ Set.range typeE6RootPairing.root := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨typeE6DiagramEquiv.indexEquiv.symm r, ?_⟩
    apply typeE6DiagramEquiv.bijective_weightMap.injective
    rw [typeE6Diagram_weight_root, Equiv.apply_symm_apply]
    exact hr
  · rintro ⟨r, rfl⟩
    exact ⟨typeE6DiagramEquiv.indexEquiv r, (typeE6Diagram_weight_root r).symm⟩

@[simp] theorem typeE6Diagram_chainBotCoeff (r s : typeE6Roots) :
    typeE6RootPairing.chainBotCoeff (typeE6DiagramEquiv.indexEquiv r)
      (typeE6DiagramEquiv.indexEquiv s) = typeE6RootPairing.chainBotCoeff r s := by
  by_cases h : LinearIndependent ℝ ![typeE6RootPairing.root r, typeE6RootPairing.root s]
  · rw [typeE6RootPairing.chainBotCoeff_eq_sSup h,
      typeE6RootPairing.chainBotCoeff_eq_sSup ((diagram_linearIndependent r s).mpr h)]
    congr 1
    ext n
    simpa only [Set.mem_ofPred_eq, map_sub, map_nsmul, typeE6Diagram_weight_root]
      using diagram_mem_range (typeE6RootPairing.root s - n • typeE6RootPairing.root r)
  · rw [typeE6RootPairing.chainBotCoeff_of_not_linearIndependent h,
      typeE6RootPairing.chainBotCoeff_of_not_linearIndependent
        (fun h' => h ((diagram_linearIndependent r s).mp h'))]

@[simp] theorem typeE6Diagram_chainTopCoeff (r s : typeE6Roots) :
    typeE6RootPairing.chainTopCoeff (typeE6DiagramEquiv.indexEquiv r)
      (typeE6DiagramEquiv.indexEquiv s) = typeE6RootPairing.chainTopCoeff r s := by
  by_cases h : LinearIndependent ℝ ![typeE6RootPairing.root r, typeE6RootPairing.root s]
  · rw [typeE6RootPairing.chainTopCoeff_eq_sSup h,
      typeE6RootPairing.chainTopCoeff_eq_sSup ((diagram_linearIndependent r s).mpr h)]
    congr 1
    ext n
    simpa only [Set.mem_ofPred_eq, map_add, map_nsmul, typeE6Diagram_weight_root]
      using diagram_mem_range (typeE6RootPairing.root s + n • typeE6RootPairing.root r)
  · rw [typeE6RootPairing.chainTopCoeff_of_not_linearIndependent h,
      typeE6RootPairing.chainTopCoeff_of_not_linearIndependent
        (fun h' => h ((diagram_linearIndependent r s).mp h'))]

end
end Theory.AlgebraicGroup.StandardRootSystem
