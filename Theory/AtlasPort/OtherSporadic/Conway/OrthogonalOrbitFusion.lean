/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalOrbitFusion.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalClassTransitivity
public import Theory.AtlasPort.OtherSporadic.Conway.OvergroupOrthogonalDivisibility
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalOrbitFusion.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def orthogonalClassShell (i j : Omega) (hij : i ≠ j) (t : Fin 5)
    (x : OrthogonalClassType i j t) : LeechShell 4 :=
  ⟨orthogonalClassValue i j t x,(orthogonalClass_good i j hij t x).1⟩

theorem orthogonal_class_orbit_saturated (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup ≤ H) (i j : Omega) (hij : i ≠ j) (base : LeechShell 4)
    (t : Fin 5) (x y : OrthogonalClassType i j t)
    (hx : orthogonalClassShell i j hij t x ∈
      MulAction.orbit (leechVectorStabilizer H (minimumPairPlus i j)) base) :
    orthogonalClassShell i j hij t y ∈
      MulAction.orbit (leechVectorStabilizer H (minimumPairPlus i j)) base := by
  obtain ⟨r,hr⟩ := orthogonalClass_transitive i j hij t x y
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hx
  let s := vectorStabilizerInclusion monomialSubgroup H hH (minimumPairPlus i j) r
  refine MulAction.mem_orbit_iff.mpr ⟨s*g,?_⟩
  rw [mul_smul,hg]
  exact Subtype.ext hr

theorem orthogonal_point_orbit_orthogonal (H : Subgroup LeechIsometryGroup)
    (i j : Omega) (base : LeechShell 4)
    (hb : integerDot (minimumPairPlus i j).val base.val.val = 0)
    (x : LeechShell 4)
    (hx : x ∈ MulAction.orbit (leechVectorStabilizer H (minimumPairPlus i j)) base) :
    integerDot (minimumPairPlus i j).val x.val.val = 0 := by
  obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hx
  have he := g.val.val.prop (minimumPairPlus i j) base.val
  rw [leechVectorStabilizer_fixes] at he
  exact he.trans hb

theorem orthogonal_orbit_fusion (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup ≤ H) (i j : Omega) (hij : i ≠ j) (base : LeechShell 4)
    (hb : integerDot (minimumPairPlus i j).val base.val.val = 0)
    (hd : 23 ∣ Nat.card (MulAction.orbit (leechVectorStabilizer H (minimumPairPlus i j)) base)) :
    ∀ x : LeechShell 4, integerDot (minimumPairPlus i j).val x.val.val = 0 →
      x ∈ MulAction.orbit (leechVectorStabilizer H (minimumPairPlus i j)) base := by
  let K := leechVectorStabilizer H (minimumPairPlus i j)
  let S : Finset (Fin 5) := Finset.univ.filter fun t =>
    ∃ y : OrthogonalClassType i j t, orthogonalClassShell i j hij t y ∈ MulAction.orbit K base
  have hS (t : Fin 5) : t ∈ S ↔ ∃ y : OrthogonalClassType i j t,
      orthogonalClassShell i j hij t y ∈ MulAction.orbit K base := by simp [S]
  have hall (t : S) (y : OrthogonalClassType i j t.val) :
      orthogonalClassShell i j hij t.val y ∈ MulAction.orbit K base := by
    obtain ⟨z,hz⟩ := (hS t.val).mp t.prop
    exact orthogonal_class_orbit_saturated H hH i j hij base t.val z y hz
  let f : ((t : S) × OrthogonalClassType i j t.val) → MulAction.orbit K base :=
    fun p => ⟨orthogonalClassShell i j hij p.1.val p.2,hall p.1 p.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t,u⟩ ⟨s,v⟩ he
      have hv := congrArg (fun z : MulAction.orbit K base => z.val.val) he
      change orthogonalClassValue i j t.val u = orthogonalClassValue i j s.val v at hv
      have ht := congrArg (orthogonalClassIndex i) hv
      simp only [orthogonalClassIndex_value i j hij] at ht
      have hts : t = s := Subtype.ext ht
      subst s
      have huv := orthogonalClassValue_injective i j t.val hv
      subst v
      rfl
    · intro x
      have ho := orthogonal_point_orbit_orthogonal H i j base hb x.val x.prop
      obtain ⟨t,y,hy⟩ := orthogonalClass_exhaustive i j hij x.val.val x.val.prop ho
      have he : orthogonalClassShell i j hij t y = x.val := Subtype.ext hy
      have ht : t ∈ S := (hS t).mpr ⟨y,he ▸ x.prop⟩
      exact ⟨⟨⟨t,ht⟩,y⟩,Subtype.ext he⟩
  have hfinit (t : Fin 5) : Finite (OrthogonalClassType i j t) :=
    Nat.finite_of_card_ne_zero (by rw [orthogonalClass_card i j hij]; fin_cases t <;> decide)
  have hc : Nat.card (MulAction.orbit K base) = ∑ t ∈ S, ![2,924,42240,4928,45056] t := by
    rw [← Nat.card_congr (Equiv.ofBijective f hf),Nat.card_sigma]
    simp_rw [orthogonalClass_card i j hij]
    exact Finset.sum_attach S _
  have hn : S.Nonempty := by
    obtain ⟨t,y,hy⟩ := orthogonalClass_exhaustive i j hij base.val base.prop hb
    refine ⟨t,(hS t).mpr ⟨y,?_⟩⟩
    have he : orthogonalClassShell i j hij t y = base := Subtype.ext hy
    rw [he]
    exact MulAction.mem_orbit_self _
  have hfull : S = Finset.univ := by
    have hd' : 23 ∣ ∑ t ∈ S, ![2,924,42240,4928,45056] t := hc ▸ hd
    rcases orthogonal_five_sizes_fusion S hd' with he | he
    · exact False.elim (hn.ne_empty he)
    · exact he
  intro x hx
  obtain ⟨t,y,hy⟩ := orthogonalClass_exhaustive i j hij x.val x.prop hx
  have ht : t ∈ S := by rw [hfull]; exact Finset.mem_univ _
  have he : orthogonalClassShell i j hij t y = x := Subtype.ext hy
  exact he ▸ hall ⟨t,ht⟩ y

end Atlas.Conway
