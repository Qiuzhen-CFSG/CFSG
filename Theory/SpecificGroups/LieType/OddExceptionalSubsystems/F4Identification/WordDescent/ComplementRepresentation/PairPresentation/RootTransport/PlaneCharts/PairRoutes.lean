module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport

/-!
# Routes inside the full span of a standard F4 pair

The subsystem consisting of all roots in a standard parabolic span has the
selected simple roots as its base. Its Weyl group moves each root to a simple
root, and its action extends to the corresponding ambient parabolic Weyl
subgroup. Expressing the inverse action as a word gives a root route using
only the selected nodes.

For two nodes, relabel that word by Booleans to match the literal pair-word
convention. This includes every B2 root and allows equal nodes. It is the
subsystem-generation part of GLS3 §2.9.3, `refs/KGroup/GLS3/chapter2.tex`,
lines 1455–1462. No assertion about placement of an arbitrary plane is needed.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.PlaneCharts
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction
open scoped Classical
attribute [local instance] Classical.decEq
local instance planeChartsPairRoutesRootFintype : Fintype typeF4Roots := Fintype.ofFinite _
local notation "𝓟" => typeF4RootPairing

/-- Every root in a standard parabolic span has a route using only its nodes. -/
theorem parabolic_root_route (J : Set typeF4RootPairing_base.support) (r : typeF4Roots)
    (hr : r ∈ typeF4RootPairing_base.parabolicRootIndices J) :
    ∃ (w : List typeF4RootPairing_base.support) (i : typeF4RootPairing_base.support),
      (∀ k ∈ w, k ∈ J) ∧ i ∈ J ∧ reflectionWord (P := 𝓟) w i = r := by
  let Q := typeF4RootPairing_base.parabolicRootSubsystem J
  let C := typeF4RootPairing_base.parabolicSubsystemBase J
  let r' : typeF4RootPairing_base.parabolicRootIndices J := ⟨r, hr⟩
  let : Fintype (typeF4RootPairing_base.parabolicRootIndices J) := Fintype.ofFinite _
  obtain ⟨g, s, hs, hg⟩ := Theory.AlgebraicGroup.weylGroup_orbit_meets_base Q C r'
  obtain ⟨j, hj⟩ := typeF4RootPairing_base.exists_parabolicSimpleIndex_eq_of_mem_support J ⟨s, hs⟩
  obtain ⟨g₀, hg₀, hact⟩ :=
    typeF4RootPairing_base.exists_parabolicSubgroup_action_eq_subsystemWeylGroup J g⁻¹
  obtain ⟨w, hw, hprod⟩ := (typeF4RootPairing_base.mem_parabolicSubgroup_iff_exists_word J g₀).mp hg₀
  refine ⟨w, j.val, hw, j.property, ?_⟩
  apply typeF4RootPairing.root.injective
  rw [root_reflectionWord, hprod]
  have he := hact (Q.root s)
  have hg' : g⁻¹ • Q.root s = Q.root r' := by rw [← hg, inv_smul_smul]
  rw [hg'] at he
  change g₀ • typeF4RootPairing.root s.val = typeF4RootPairing.root r at he
  change s = typeF4RootPairing_base.parabolicSimpleIndex J j at hj
  rw [hj] at he
  exact he

/-- Every root in the full span of a standard pair is reached using that pair,
including all intermediate B2 roots and pairs with equal nodes. -/
theorem standardPair_root_route (i j : Fin 4) (r : typeF4Roots)
    (hr : r ∈ rootPlane (signedRoot true i) (signedRoot true j)) :
    ∃ (v : List Bool) (k : Bool),
      reflectionWord (P := 𝓟) (pairTransportNodes i j v)
        (signedRoot true (pairNode i j k)) = r := by
  let J : Set typeF4RootPairing_base.support := {sourceIndex i, sourceIndex j}
  have hrJ : r ∈ typeF4RootPairing_base.parabolicRootIndices J := by
    simpa only [RootPairing.Base.parabolicRootIndices, RootPairing.Base.parabolicRootSpan,
      Set.mem_ofPred_eq, J, Set.image_pair, rootPlane, signedRoot, if_true] using hr
  obtain ⟨w, l, hw, hl, hroot⟩ := parabolic_root_route J r hrJ
  let select : typeF4RootPairing_base.support → Bool := fun k => decide (k = sourceIndex i)
  have hselect (k : typeF4RootPairing_base.support) (hk : k ∈ J) :
      sourceIndex (pairNode i j (select k)) = k := by
    rcases hk with hk | hk
    · subst k
      simp [select, pairNode]
    · subst k
      by_cases hij : sourceIndex j = sourceIndex i
      · simp [select, pairNode, hij]
      · simp [select, pairNode, hij]
  have hw' : pairTransportNodes i j (w.map select) = w := by
    simp only [pairTransportNodes, List.map_map]
    calc
      _ = List.map id w := List.map_congr_left fun k hk => hselect k (hw k hk)
      _ = w := List.map_id w
  refine ⟨w.map select, select l, ?_⟩
  rw [hw']
  change reflectionWord (P := 𝓟) w (sourceIndex (pairNode i j (select l))) = r
  rw [hselect l hl]
  exact hroot

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.PlaneCharts
