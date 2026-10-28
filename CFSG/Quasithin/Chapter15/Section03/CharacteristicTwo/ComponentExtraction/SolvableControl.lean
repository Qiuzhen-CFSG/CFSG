module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Inheritance
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Candidates
public import Theory.GroupTheory.SolvableNormalSup

/-!
# Solvable invariant subgroups in the characteristic-two argument

An actual C-component makes its local overgroup nonsolvable. If components
are constructed uniformly for smaller outside overgroups, then a solvable
`Y₊S`-invariant subgroup cannot escape `M`: adjoining `Y₊S` would produce a
solvable outside overgroup. The inherited two-core verifies membership in the
source family, and the inherited generalized-Fitting equality permits use of
the same component construction there.

These are conditional assembly steps. The component-extraction owner must
construct the witnesses before establishing the source containment theorem.
The version for star candidates shows that solvable control does not need
to wait for the separate two-core quotient upgrade.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.15(3) and 15.3.26(3), printed pp.1125 and 1130.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Subgroup
variable {G : Type*} [Group G] [Finite G]

namespace ComponentWitness
variable {d : LocalData G} {I : Subgroup G}

omit [Finite G] in
/-- An actual C-component of the Thompson subgroup certifies that its
local overgroup is nonsolvable. -/
theorem not_isSolvable (w : ComponentWitness d I) : ¬ Group.IsSolvable I := by
  intro hI
  let _ := hI
  have hJI : Stellmacher.elementaryAbelianMaxJ I ≤ I := sSup_le fun A hA => hA.1
  have hJ : Group.IsSolvable (Stellmacher.elementaryAbelianMaxJ I) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hJI)
  let _ := hJ
  exact w.component.not_isSolvable inferInstance

end ComponentWitness

namespace LocalData
variable (d : LocalData G)

/-- The local subgroup `Y₊S` is solvable as soon as `Y₊` is solvable and
normal in that join, as in the two alternatives of 15.3.11(5). -/
theorem join_isSolvable (hY : Group.IsSolvable d.Yplus)
    (hn : d.S ≤ normalizer (d.Yplus : Set G)) :
    Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) := by
  let H := d.Yplus ⊔ d.S
  let A := d.Yplus.subgroupOf H
  let B := d.S.subgroupOf H
  let _ := hY
  have hS : IsPGroup 2 d.S := d.T.isPGroup'.to_le inf_le_left
  let _ : Group.IsNilpotent d.S := hS.isNilpotent
  let _ : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le d.Yplus.le_normalizer hn)
  let _ : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show d.Yplus ≤ H from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show d.Yplus ≤ H from le_sup_left)).injective
  let _ : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show d.S ≤ H from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show d.S ≤ H from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top A B
  apply (map_injective H.subtype_injective)
  simp only [A, B, H, Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]

/-- The actual quotient clause of 15.3.11(5), together with theta generation,
supplies solvability of `Y₊S`; no solvability premise is added to the setup. -/
theorem join_isSolvable_of_three_quotient {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hθ : theta (d.MI I) = d.Yplus)
    (hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus)) :
    Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) := by
  let _ : Group.IsNilpotent (pCore 2 d.Yplus) := pCore_isNilpotent
  let _ : Group.IsNilpotent (d.Yplus ⧸ pCore 2 d.Yplus) := hY.isNilpotent
  have hsol : Group.IsSolvable d.Yplus :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 d.Yplus)).mpr
      ⟨inferInstance, inferInstance⟩
  apply d.join_isSolvable hsol
  rw [← hθ]
  have hSMI : d.S ≤ d.MI I :=
    le_inf (inf_le_left.trans d.sylow_le) (le_sup_right.trans hI.1.2)
  exact hSMI.trans ((d.MI I).le_normalizer.trans (normalizer_le_normalizer_theta _))

/-- The common extension argument: a solvable invariant subgroup outside
`M` would generate a solvable outside overgroup with `Y₊S`. -/
theorem solvable_invariant_le_of_nonsolvable_overgroups {I X : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hf : HasCharacteristicTwo I)
    (hYS : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G))
    (hnonsolvable : ∀ K : Subgroup G, K ≤ I → K ∈ d.Hplus →
      HasCharacteristicTwo K → ¬ Group.IsSolvable K)
    (hXI : X ≤ I) (hX : Group.IsSolvable X)
    (hn : d.Yplus ⊔ d.S ≤ normalizer (X : Set G)) : X ≤ d.MI I := by
  apply le_inf _ hXI
  by_contra hXM
  let K := X ⊔ (d.Yplus ⊔ d.S)
  have hKI : K ≤ I := sup_le hXI (d.join_le_of_mem_Hplus hI)
  have hK : K ∈ d.Hplus := d.mem_Hplus_of_intermediate hI hS hKI le_sup_right
    (fun hKM => hXM (le_sup_left.trans hKM))
  apply hnonsolvable K hKI hK (d.characteristicTwo_of_mem_Hplus_le hS hKI hK hf)
  let A := X.subgroupOf K
  let B := (d.Yplus ⊔ d.S).subgroupOf K
  let _ := hX
  let _ := hYS
  let _ : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hn)
  let _ : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show X ≤ K from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show X ≤ K from le_sup_left)).injective
  let _ : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show d.Yplus ⊔ d.S ≤ K from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show d.Yplus ⊔ d.S ≤ K from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top A B
  apply (map_injective K.subtype_injective)
  simp only [A, B, K, Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]

/-- The component construction must apply to every smaller outside
subgroup; a component in the original overgroup alone does not suffice. -/
theorem solvable_invariant_le_of_components {I X : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hf : HasCharacteristicTwo I)
    (hYS : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G))
    (hcomponents : ∀ K : Subgroup G, K ≤ I → K ∈ d.Hplus →
      HasCharacteristicTwo K → Nonempty (ComponentWitness d K))
    (hXI : X ≤ I) (hX : Group.IsSolvable X)
    (hn : d.Yplus ⊔ d.S ≤ normalizer (X : Set G)) : X ≤ d.MI I :=
  d.solvable_invariant_le_of_nonsolvable_overgroups hI hS hf hYS
    (fun K hKI hK hfK => (hcomponents K hKI hK hfK).elim ComponentWitness.not_isSolvable)
    hXI hX hn

/-- Solvable control already follows from the classified star candidates,
independently of the subsequent two-core quotient argument. -/
theorem solvable_invariant_le_of_star_candidates {I X : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hf : HasCharacteristicTwo I)
    (hYS : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G))
    (hcandidates : ∀ K : Subgroup G, K ≤ I → K ∈ d.Hplus →
      HasCharacteristicTwo K → Nonempty (StarComponentCandidate d K))
    (hXI : X ≤ I) (hX : Group.IsSolvable X)
    (hn : d.Yplus ⊔ d.S ≤ normalizer (X : Set G)) : X ≤ d.MI I :=
  d.solvable_invariant_le_of_nonsolvable_overgroups hI hS hf hYS
    (fun K hKI hK hfK =>
      (hcandidates K hKI hK hfK).elim StarComponentCandidate.not_isSolvable)
    hXI hX hn

/-- Uniform candidate selection is the only additional extraction premise
in this version of the solvable-control deduction. -/
theorem solvable_invariant_le_of_classified_candidates {I X : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hf : HasCharacteristicTwo I)
    (hθ : theta (d.MI I) = d.Yplus)
    (hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus))
    (hcandidates : ∀ K : Subgroup G, K ≤ I → K ∈ d.Hplus →
      HasCharacteristicTwo K → Nonempty (StarComponentCandidate d K))
    (hXI : X ≤ I) (hX : Group.IsSolvable X)
    (hn : d.Yplus ⊔ d.S ≤ normalizer (X : Set G)) : X ≤ d.MI I :=
  d.solvable_invariant_le_of_star_candidates hI hS hf
    (d.join_isSolvable_of_three_quotient hI hθ hY) hcandidates hXI hX hn

end LocalData

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
end
