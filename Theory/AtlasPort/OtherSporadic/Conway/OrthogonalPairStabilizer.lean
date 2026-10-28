/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalPairStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalPairGeometry
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalPairStabilizer.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def orthogonalPairStabilizer (e : Fin 2 ↪ Omega) : Subgroup LeechIsometryGroup :=
  (fixingSubgroup (leech ≃ₗ[ℤ] leech)
    ({minimumPairPlus (e 0) (e 1),minimumPairMinus (e 0) (e 1)} : Set leech)).comap
      leechIsometries.subtype

theorem orthogonalPairStabilizer_mem (e : Fin 2 ↪ Omega) (g : LeechIsometryGroup) :
    g ∈ orthogonalPairStabilizer e ↔
      g.val (minimumPairPlus (e 0) (e 1)) = minimumPairPlus (e 0) (e 1) ∧
      g.val (minimumPairMinus (e 0) (e 1)) = minimumPairMinus (e 0) (e 1) := by
  change g.val ∈ fixingSubgroup (leech ≃ₗ[ℤ] leech)
    ({minimumPairPlus (e 0) (e 1),minimumPairMinus (e 0) (e 1)} : Set leech) ↔ _
  rw [mem_fixingSubgroup_iff]
  simp

theorem orthogonalPairStabilizer_le_monomial (e : Fin 2 ↪ Omega) :
    orthogonalPairStabilizer e ≤ monomialSubgroup := by
  intro g hg
  obtain ⟨hp,hm⟩ := (orthogonalPairStabilizer_mem e g).mp hg
  exact minimumPair_fixer_mem_monomial g _ _ hp hm

def pairLatticeEmbedding (e : Fin 2 ↪ Omega) : GolayPairMonomialGroup e →* LeechIsometryGroup :=
  monomialEmbedding.comp (pairMonomialInclusion e)

theorem pairLatticeEmbedding_injective (e : Fin 2 ↪ Omega) :
    Function.Injective (pairLatticeEmbedding e) :=
  monomialEmbedding_injective.comp (pairMonomialInclusion_injective e)

theorem pairLatticeEmbedding_range (e : Fin 2 ↪ Omega) :
    (pairLatticeEmbedding e).range = orthogonalPairStabilizer e := by
  ext g
  constructor
  · rintro ⟨m,rfl⟩
    rw [orthogonalPairStabilizer_mem,minimumPair_fixed_iff_axes]
    change (monomialEmbedding (pairMonomialInclusion e m)).val (coordinateEight (e 0)) = _ ∧
      (monomialEmbedding (pairMonomialInclusion e m)).val (coordinateEight (e 1)) = _
    rw [monomial_axis_fixed_iff,monomial_axis_fixed_iff]
    have h0 := congrArg Prod.fst m.left.toAdd.prop
    have h1 := congrArg Prod.snd m.left.toAdd.prop
    exact ⟨⟨orderedPair_fixes e m.right 0,h0⟩,⟨orderedPair_fixes e m.right 1,h1⟩⟩
  · intro hg
    obtain ⟨m,hm⟩ := orthogonalPairStabilizer_le_monomial e hg
    subst g
    rw [orthogonalPairStabilizer_mem,minimumPair_fixed_iff_axes,
      monomial_axis_fixed_iff,monomial_axis_fixed_iff] at hg
    let c : GolayPairKernel e := ⟨m.left.toAdd,Prod.ext hg.1.2 hg.2.2⟩
    let p : orderedPointStabilizer e := ⟨m.right,by
      apply (mem_fixingSubgroup_iff Mathieu24CodeModel).mpr
      rintro i ⟨k,rfl⟩
      fin_cases k
      · exact hg.1.1
      · exact hg.2.1⟩
    refine ⟨⟨Multiplicative.ofAdd c,p⟩,?_⟩
    apply congrArg monomialEmbedding
    apply SemidirectProduct.ext <;> rfl

def orthogonalPairStabilizerEquiv (e : Fin 2 ↪ Omega) :
    GolayPairMonomialGroup e ≃* orthogonalPairStabilizer e :=
  (MonoidHom.ofInjective (pairLatticeEmbedding_injective e)).trans
    (MulEquiv.subgroupCongr (pairLatticeEmbedding_range e))

theorem orthogonalPairStabilizerEquiv_compatible (e : Fin 2 ↪ Omega)
    (m : GolayPairMonomialGroup e) :
    (orthogonalPairStabilizerEquiv e m).val = pairLatticeEmbedding e m := rfl

theorem orthogonalPairStabilizer_order (e : Fin 2 ↪ Omega) :
    Nat.card (orthogonalPairStabilizer e) = 1024 * 443520 := by
  rw [← Nat.card_congr (orthogonalPairStabilizerEquiv e).toEquiv]
  exact golayPairMonomialGroup_order e

theorem orthogonalPairStabilizer_le_overgroup (e : Fin 2 ↪ Omega)
    (H : Subgroup LeechIsometryGroup) (hH : monomialSubgroup ≤ H) :
    orthogonalPairStabilizer e ≤ H := (orthogonalPairStabilizer_le_monomial e).trans hH

theorem orthogonalPairStabilizer_overgroup_order (e : Fin 2 ↪ Omega)
    (H : Subgroup LeechIsometryGroup) (hH : monomialSubgroup ≤ H) :
    Nat.card ((orthogonalPairStabilizer e).subgroupOf H) = 1024 * 443520 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (orthogonalPairStabilizer_le_overgroup e H hH)).toEquiv]
  exact orthogonalPairStabilizer_order e

end Atlas.Conway

