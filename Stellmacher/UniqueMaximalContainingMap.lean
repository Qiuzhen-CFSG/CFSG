module
public import Stellmacher.SectionsOneToFourDefs
public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.Order.Atoms.Finite

/-!
# Unique maximal containment under a surjective homomorphism

If a subgroup lies in a unique maximal subgroup of a finite ambient group,
its proper image under a surjective homomorphism also lies in a unique maximal
subgroup. No normality or Sylow hypothesis on the original subgroup is needed.

Transport through `Subgroup.topEquiv` first expresses the native containment
property directly in the ambient subgroup lattice. A proper image has a maximal
overgroup because that lattice is finite. The preimage of each maximal
overgroup is maximal by surjectivity and contains the original subgroup.
Uniqueness upstairs, followed by injectivity of preimage on subgroup lattices,
gives uniqueness downstairs.

This elementary subgroup-correspondence step supplies quotient unique-maximal
inputs in Stellmacher (9.3)'s application of (1.7); see
`refs/latex/stellmacher-n-group.tex`. The native `IsUniqueMaximalContaining`
property and its top-subgroup convention are preserved. The equivalence with
the ambient unique-coatom formulation is public for quotient Sylow consumers.
-/

namespace Stellmacher

/-- Native unique maximal containment is the ambient unique-coatom property. -/
public theorem uniqueMaximalContaining_top_iff {G : Type*} [Group G] (S : Subgroup G) :
    IsUniqueMaximalContaining S ⊤ ↔
      ∃ M : Subgroup G, IsCoatom M ∧ S ≤ M ∧
        ∀ M' : Subgroup G, IsCoatom M' → S ≤ M' → M' = M := by
  let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  constructor
  · rintro ⟨M, hM, hSM, huniq⟩
    refine ⟨M.map e.toMonoidHom, (OrderIso.isCoatom_iff e.mapSubgroup M).2 hM, hSM, ?_⟩
    intro N hN hSN
    have hNmap : (N.map e.symm.toMonoidHom).map e.toMonoidHom = N := by
      rw [Subgroup.map_map]; simp
    have hh := huniq (N.map e.symm.toMonoidHom)
      ((OrderIso.isCoatom_iff e.symm.mapSubgroup N).2 hN) (by
        change S ≤ (N.map e.symm.toMonoidHom).map e.toMonoidHom
        rwa [hNmap])
    rw [← hNmap, hh]
  · rintro ⟨M, hM, hSM, huniq⟩
    let N := M.map e.symm.toMonoidHom
    have hNmap : N.map e.toMonoidHom = M := by
      dsimp only [N]
      rw [Subgroup.map_map]; simp
    refine ⟨N, (OrderIso.isCoatom_iff e.symm.mapSubgroup M).2 hM, ?_, ?_⟩
    · change S ≤ N.map e.toMonoidHom
      rwa [hNmap]
    · intro N' hN' hSN'
      apply e.mapSubgroup.injective
      change N'.map e.toMonoidHom = N.map e.toMonoidHom
      rw [hNmap]
      exact huniq _ ((OrderIso.isCoatom_iff e.mapSubgroup N').2 hN') hSN'

/-- A proper surjective image inherits unique maximal containment. -/
public theorem uniqueMaximalContaining_map_of_ne_top
    {G X : Type*} [Group G] [Group X] [Finite G] [Finite X]
    (q : G →* X) (hq : Function.Surjective q) (S : Subgroup G)
    (hS : IsUniqueMaximalContaining S ⊤) (hproper : S.map q ≠ ⊤) :
    IsUniqueMaximalContaining (S.map q) ⊤ := by
  obtain ⟨M, hM, hSM, huniq⟩ := (uniqueMaximalContaining_top_iff S).mp hS
  obtain ⟨N, hN, hSN⟩ := (eq_top_or_exists_le_coatom (S.map q)).resolve_left hproper
  apply (uniqueMaximalContaining_top_iff (S.map q)).mpr
  refine ⟨N, hN, hSN, ?_⟩
  intro N' hN' hSN'
  apply Subgroup.comap_injective hq
  have hNM : N.comap q = M := huniq _ (Subgroup.isCoatom_comap_of_surjective hq hN)
    (Subgroup.map_le_iff_le_comap.mp hSN)
  have hN'M : N'.comap q = M := huniq _ (Subgroup.isCoatom_comap_of_surjective hq hN')
    (Subgroup.map_le_iff_le_comap.mp hSN')
  exact hN'M.trans hNM.symm

end Stellmacher
