/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalMinimumClasses.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.ContainingOctadCount
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalOddCount
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalFourCount
public import Theory.AtlasPort.OtherSporadic.Conway.MinimumShapeSeparation
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalFusionArithmetic
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalMinimumClasses.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def OrthogonalClassType (i j : Omega) : Fin 5 → Type
  | 0 => PairSignClass i j
  | 1 => DisjointFourClass {i,j}
  | 2 => DisjointOctadClass {i,j}
  | 3 => ContainingOctadClass i j
  | 4 => OrthogonalOddClass i j

def orthogonalClassValue (i j : Omega) : (t : Fin 5) → OrthogonalClassType i j t → leech
  | 0, x => x.val
  | 1, x => x.val
  | 2, x => x.val
  | 3, x => x.val
  | 4, x => x.val

theorem orthogonalClassValue_injective (i j : Omega) (t : Fin 5) :
    Function.Injective (orthogonalClassValue i j t) := by
  fin_cases t <;> exact Subtype.val_injective

theorem orthogonalClass_card (i j : Omega) (hij : i ≠ j) (t : Fin 5) :
    Nat.card (OrthogonalClassType i j t) = ![2,924,42240,4928,45056] t := by
  fin_cases t
  · exact pairSignClass_card i j hij
  · exact disjointFourPair_card i j hij
  · exact disjointOctadPair_card i j hij
  · exact containingOctadClass_card i j hij
  · exact orthogonalOddClass_card i j hij

theorem orthogonalClass_good (i j : Omega) (hij : i ≠ j) (t : Fin 5)
    (x : OrthogonalClassType i j t) :
    integerDot (orthogonalClassValue i j t x).val (orthogonalClassValue i j t x).val = 32 ∧
    integerDot (minimumPairPlus i j).val (orthogonalClassValue i j t x).val = 0 := by
  fin_cases t
  · have h := pairSign_four_orthogonal i j hij x
    exact ⟨(twoFourFamily_properties 0 2 _ h.1).2.2,h.2⟩
  · refine ⟨(twoFourFamily_properties 0 2 _ x.prop.1).2.2,?_⟩
    change integerDot (minimumPairPlus i j).val x.val.val = 0
    rw [minimumPairPlus_dot,x.prop.2 i (by simp),x.prop.2 j (by simp)]
    norm_num
  · refine ⟨(twoFourFamily_properties 8 0 _ x.prop.1).2.2,?_⟩
    change integerDot (minimumPairPlus i j).val x.val.val = 0
    rw [minimumPairPlus_dot,x.prop.2 i (by simp),x.prop.2 j (by simp)]
    norm_num
  · exact ⟨(twoFourFamily_properties 8 0 _ x.prop.1).2.2,x.prop.2.1⟩
  · exact ⟨((odd_minimal_shell_iff x.val.val).mpr x.prop.1).2.2,x.prop.2⟩

def orthogonalClassIndex (i : Omega) (x : leech) : Fin 5 :=
  if x.val ∈ twoFourFamily 0 2 then (if x.val i = 0 then 1 else 0)
  else if x.val ∈ twoFourFamily 8 0 then (if x.val i = 0 then 2 else 3) else 4

theorem orthogonalClassIndex_value (i j : Omega) (hij : i ≠ j) (t : Fin 5)
    (x : OrthogonalClassType i j t) : orthogonalClassIndex i (orthogonalClassValue i j t x) = t := by
  fin_cases t
  · have hf := (pairSign_four_orthogonal i j hij x).1
    have hn := pairSign_coordinate_ne_zero i j hij x
    simp [orthogonalClassValue,orthogonalClassIndex,hf,hn]
  · have hz := x.prop.2 i (by simp)
    simp [orthogonalClassValue,orthogonalClassIndex,x.prop.1,hz]
  · have hn : x.val.val ∉ twoFourFamily 0 2 := fun h =>
      Finset.disjoint_left.mp (twoFourFamily_disjoint 0 2 8 0 (Or.inl (by decide))) h x.prop.1
    have hz := x.prop.2 i (by simp)
    simp [orthogonalClassValue,orthogonalClassIndex,hn,x.prop.1,hz]
  · have hn : x.val.val ∉ twoFourFamily 0 2 := fun h =>
      Finset.disjoint_left.mp (twoFourFamily_disjoint 0 2 8 0 (Or.inl (by decide))) h x.prop.1
    simp [orthogonalClassValue,orthogonalClassIndex,hn,x.prop.1,x.prop.2.2]
  · have h0 : x.val.val ∉ twoFourFamily 0 2 := fun h =>
      Finset.disjoint_left.mp (even_odd_minimum_disjoint 0 2) h x.prop.1
    have h1 : x.val.val ∉ twoFourFamily 8 0 := fun h =>
      Finset.disjoint_left.mp (even_odd_minimum_disjoint 8 0) h x.prop.1
    simp [orthogonalClassValue,orthogonalClassIndex,h0,h1]

theorem orthogonalClass_exhaustive (i j : Omega) (hij : i ≠ j) (x : leech)
    (hn : integerDot x.val x.val = 32) (ho : integerDot (minimumPairPlus i j).val x.val = 0) :
    ∃ t : Fin 5, ∃ y : OrthogonalClassType i j t, orthogonalClassValue i j t y = x := by
  obtain ⟨t,ht⟩ := minimumShape_exhaustive (⟨x,hn⟩ : LeechShell 4)
  fin_cases t
  · rcases four_orthogonal_partition i j hij x ht ho with hp | hz
    · exact ⟨0,⟨x,hp⟩,rfl⟩
    · refine ⟨1,⟨x,ht,?_⟩,rfl⟩
      intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hz.1
      · exact hz.2
  · by_cases hi : x.val i = 0
    · have hj : x.val j = 0 := by rw [minimumPairPlus_dot,hi] at ho; omega
      refine ⟨2,⟨x,ht,?_⟩,rfl⟩
      intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hi
      · exact hj
    · exact ⟨3,⟨x,ht,ho,hi⟩,rfl⟩
  · exact ⟨4,⟨x,ht,ho⟩,rfl⟩

def OrthogonalMinimumShell (i j : Omega) :=
  {x : LeechShell 4 // integerDot (minimumPairPlus i j).val x.val.val = 0}

def orthogonalClassMap (i j : Omega) (hij : i ≠ j)
    (p : (t : Fin 5) × OrthogonalClassType i j t) : OrthogonalMinimumShell i j :=
  ⟨⟨orthogonalClassValue i j p.1 p.2,(orthogonalClass_good i j hij p.1 p.2).1⟩,
    (orthogonalClass_good i j hij p.1 p.2).2⟩

def orthogonalMinimumEquiv (i j : Omega) (hij : i ≠ j) :
    ((t : Fin 5) × OrthogonalClassType i j t) ≃ OrthogonalMinimumShell i j :=
  Equiv.ofBijective (orthogonalClassMap i j hij) ⟨by
    rintro ⟨t,x⟩ ⟨s,y⟩ h
    have hv := congrArg (fun z : OrthogonalMinimumShell i j => z.val.val) h
    change orthogonalClassValue i j t x = orthogonalClassValue i j s y at hv
    have ht := congrArg (orthogonalClassIndex i) hv
    simp only [orthogonalClassIndex_value i j hij] at ht
    subst s
    have he := orthogonalClassValue_injective i j t hv
    subst y
    rfl,by
    intro x
    obtain ⟨t,y,hy⟩ := orthogonalClass_exhaustive i j hij x.val.val x.val.prop x.prop
    exact ⟨⟨t,y⟩,Subtype.ext (Subtype.ext hy)⟩⟩

theorem orthogonalMinimumShell_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (OrthogonalMinimumShell i j) = 93150 := by
  have hf (t : Fin 5) : Finite (OrthogonalClassType i j t) := Nat.finite_of_card_ne_zero (by
    rw [orthogonalClass_card i j hij]
    fin_cases t <;> decide)
  rw [← Nat.card_congr (orthogonalMinimumEquiv i j hij),Nat.card_sigma]
  simp_rw [orthogonalClass_card i j hij]
  exact orthogonal_five_sizes_total

end Atlas.Conway
