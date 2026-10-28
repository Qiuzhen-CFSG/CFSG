/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadAction
public import Theory.AtlasPort.OtherSporadic.Combinatorics.SteinerCounting

/-!
# Mathieu12Witt

The six-point traces of octads on a dodecad form the Steiner system with parameters 5,
6, 12 and 132 blocks. Unique octad completion proves the design property; intersections
and code addition establish uniqueness, invariance, and closure under complement.

Source: `Atlas/Mathieu/Mathieu12Witt.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open Finset

def mathieu12OctadTrace (D : Dodecad) (O : Finset Omega) : Finset (Mathieu12Points D) := by
  classical
  exact univ.filter (fun x => x.val ∈ O)

def mathieu12BlockLift (D : Dodecad) (B : Finset (Mathieu12Points D)) : Finset Omega :=
  B.map (Function.Embedding.subtype _)

theorem mathieu12OctadTrace_lift (D : Dodecad) (O : Finset Omega) :
    mathieu12BlockLift D (mathieu12OctadTrace D O) = D.val ∩ O := by
  classical
  ext x
  simp only [mathieu12BlockLift,mem_map,mathieu12OctadTrace,mem_filter,mem_univ,true_and,mem_inter]
  constructor
  · rintro ⟨y,hy,rfl⟩; exact ⟨y.prop,hy⟩
  · rintro ⟨hx,ho⟩; exact ⟨⟨x,hx⟩,ho,rfl⟩

theorem mathieu12OctadTrace_card (D : Dodecad) (O : Finset Omega) :
    (mathieu12OctadTrace D O).card = (D.val ∩ O).card := by
  rw [← mathieu12OctadTrace_lift]
  exact (card_map _).symm

def mathieu12Blocks (D : Dodecad) : Finset (Finset (Mathieu12Points D)) := by
  classical
  exact (octads.filter (fun O => (D.val ∩ O).card = 6)).image (mathieu12OctadTrace D)

theorem mathieu12Blocks_mem (D : Dodecad) (B : Finset (Mathieu12Points D)) :
    B ∈ mathieu12Blocks D ↔ ∃ O ∈ octads, (D.val ∩ O).card = 6 ∧ mathieu12OctadTrace D O = B := by
  classical
  simp only [mathieu12Blocks,mem_image,mem_filter]
  constructor
  · rintro ⟨O,⟨hO,hc⟩,he⟩; exact ⟨O,hO,hc,he⟩
  · rintro ⟨O,hO,hc,he⟩; exact ⟨O,⟨hO,hc⟩,he⟩

theorem mathieu12Blocks_size (D : Dodecad) (B : Finset (Mathieu12Points D))
    (hB : B ∈ mathieu12Blocks D) : B.card = 6 := by
  obtain ⟨O,hO,hc,rfl⟩ := (mathieu12Blocks_mem D B).mp hB
  exact (mathieu12OctadTrace_card D O).trans hc

theorem mathieu12_lift_subset_trace (D : Dodecad) (T : Finset (Mathieu12Points D)) (O : Finset Omega) :
    mathieu12BlockLift D T ⊆ O ↔ T ⊆ mathieu12OctadTrace D O := by
  classical
  constructor
  · intro ht x hx
    exact mem_filter.mpr ⟨mem_univ _,ht (mem_map.mpr ⟨x,hx,rfl⟩)⟩
  · intro ht x hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    exact (mem_filter.mp (ht hy)).2

theorem mathieu12_steiner (D : Dodecad) (T : Finset (Mathieu12Points D)) (hT : T.card = 5) :
    ∃! B : Finset (Mathieu12Points D), B ∈ mathieu12Blocks D ∧ T ⊆ B := by
  classical
  have ht : (mathieu12BlockLift D T).card = 5 := by rw [mathieu12BlockLift,card_map,hT]
  obtain ⟨O,⟨hO,hTO⟩,huniq⟩ := octad_steiner (mathieu12BlockLift D T) ht
  have hsub : mathieu12BlockLift D T ⊆ D.val ∩ O := by
    intro x hx
    obtain ⟨y,hy,he⟩ := mem_map.mp hx
    exact mem_inter.mpr ⟨he ▸ y.prop,hTO hx⟩
  have hc : (D.val ∩ O).card = 6 := by
    have hl := card_le_card hsub
    have hs := dodecad_octad_intersection D.val O D.prop hO
    omega
  refine ⟨mathieu12OctadTrace D O,⟨(mathieu12Blocks_mem D _).mpr ⟨O,hO,hc,rfl⟩,
    (mathieu12_lift_subset_trace D T O).mp hTO⟩,?_⟩
  intro B hB
  obtain ⟨P,hP,hPc,hPB⟩ := (mathieu12Blocks_mem D B).mp hB.1
  have hTP := (mathieu12_lift_subset_trace D T P).mpr (hPB.symm ▸ hB.2)
  rw [huniq P ⟨hP,hTP⟩] at hPB
  exact hPB.symm

theorem mathieu12Blocks_card (D : Dodecad) : (mathieu12Blocks D).card = 132 := by
  have h := Atlas.Combinatorics.steiner_block_count (mathieu12Blocks D) 5 6
    (mathieu12Blocks_size D) (mathieu12_steiner D)
  rw [← Nat.card_eq_fintype_card,mathieu12_degree] at h
  norm_num [Nat.choose] at h
  omega

theorem mathieu12_hexad_determines_octad (D : Dodecad) (O P : Finset Omega)
    (hO : O ∈ octads) (hP : P ∈ octads) (hc : (mathieu12OctadTrace D O).card = 6)
    (he : mathieu12OctadTrace D O = mathieu12OctadTrace D P) : O = P := by
  classical
  obtain ⟨T,hT,hcT⟩ := exists_subset_card_eq
    (s := mathieu12OctadTrace D O) (n := 5) (by omega)
  apply octad_unique_on_five (mathieu12BlockLift D T) O P
    (by rw [mathieu12BlockLift,card_map,hcT]) hO hP
    ((mathieu12_lift_subset_trace D T O).mpr hT)
  exact (mathieu12_lift_subset_trace D T P).mpr (he ▸ hT)

def mathieu12PermuteBlock (D : Dodecad) (g : Mathieu12DodecadModel D)
    (B : Finset (Mathieu12Points D)) : Finset (Mathieu12Points D) := by
  classical
  exact B.image (fun x => g • x)

theorem mathieu12_trace_permute (D : Dodecad) (g : Mathieu12DodecadModel D) (O : Finset Omega) :
    mathieu12PermuteBlock D g (mathieu12OctadTrace D O) =
      mathieu12OctadTrace D (permuteBlock g.val.val O) := by
  classical
  ext x
  simp only [mathieu12PermuteBlock,mathieu12OctadTrace,mem_image,mem_filter,mem_univ,true_and,
    permuteBlock]
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.val,hy,rfl⟩
  · rintro ⟨y,hy,he⟩
    refine ⟨g⁻¹ • x,?_,smul_inv_smul g x⟩
    have hh : (g⁻¹ • x).val = y := by
      change g.val.val⁻¹ x.val = y
      rw [← he,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
    exact hh.symm ▸ hy

theorem mathieu12Blocks_preserved (D : Dodecad) (g : Mathieu12DodecadModel D)
    (B : Finset (Mathieu12Points D)) (hB : B ∈ mathieu12Blocks D) :
    mathieu12PermuteBlock D g B ∈ mathieu12Blocks D := by
  classical
  obtain ⟨O,hO,hc,rfl⟩ := (mathieu12Blocks_mem D B).mp hB
  refine (mathieu12Blocks_mem D _).mpr ⟨permuteBlock g.val.val O,
    codePreserving_octad_forward _ g.val.prop O hO,?_,(mathieu12_trace_permute D g O).symm⟩
  rw [← mathieu12OctadTrace_card,← mathieu12_trace_permute,mathieu12PermuteBlock,
    card_image_of_injective _ (MulAction.injective g),mathieu12OctadTrace_card,hc]

theorem mathieu12Blocks_complement (D : Dodecad) (B : Finset (Mathieu12Points D))
    (hB : B ∈ mathieu12Blocks D) : Bᶜ ∈ mathieu12Blocks D := by
  classical
  obtain ⟨O,hO,hc,rfl⟩ := (mathieu12Blocks_mem D B).mp hB
  obtain ⟨u,hu,hsu⟩ := (dodecads_mem D.val).mp D.prop
  obtain ⟨v,hv,hsv⟩ := (octads_mem O).mp hO
  have hw : hammingNorm (u.val + v.val) = 8 := by
    have he := binary_weight_add u.val v.val
    rw [hu,hv,overlap_inter,hsu,hsv,hc] at he
    omega
  have hp : support (u.val+v.val) ∈ octads :=
    (octads_mem _).mpr ⟨⟨u.val+v.val,golay.add_mem u.prop v.prop⟩,hw,rfl⟩
  have ht : mathieu12OctadTrace D (support (u.val+v.val)) = (mathieu12OctadTrace D O)ᶜ := by
    ext x
    simp [mathieu12OctadTrace,support_add_sdiff,hsu,hsv]
  refine (mathieu12Blocks_mem D _).mpr ⟨support (u.val+v.val),hp,?_,ht⟩
  rw [← mathieu12OctadTrace_card,ht,card_compl,mathieu12OctadTrace_card,hc,
    ← Nat.card_eq_fintype_card,mathieu12_degree]

end Atlas.Codes
