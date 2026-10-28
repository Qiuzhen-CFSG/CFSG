module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Lattice
public import Theory.GroupTheory.ConjugateSpanSylow


/-!
# The two root-module generation calculations in original 4.3.6

In the standard symplectic carrier, the full plane radical lies in the
point local group and normally generates it. Its plane-fixed subgroup is
exactly short root four. That short root normally generates the point radical:
the nonbinary natural extension has no proper noncentral normal subgroup.
The plane radical also has nontrivial image in the simple point quotient,
which supplies the remaining local generation.

These calculations retain the original matrix embeddings, centralizers and
conjugation spans. `OrdinaryRootCore` transports them to the actual source
configuration. Source: Aschbacher--Smith 4.3.6, printed pp.614--615, including (*).
-/

public section

open Subgroup Matrix
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCoreMatrix
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)

omit [Finite F] [CharP F 2] in
theorem plane_radical_le_point :
    (Plane.radical (F := F)).map planeLocal.subtype ≤ pointLocal := by
  rintro _ ⟨g, hg, rfl⟩
  apply (mem_pointLocal_iff _).mpr
  have hm := Plane.radical_matrix (⟨g, hg⟩ : Plane.radical)
  refine ⟨?_, ?_⟩
  · rw [mem_pointParabolic_iff]
    constructor
    · change g.val.val (.inl 1) (.inl 0) = 0
      rw [hm]; rfl
    · intro i
      change g.val.val (.inr i) (.inl 0) = 0
      rw [hm]; rfl
  · change g.val.val (.inl 0) (.inl 0) = 1
    rw [hm]; rfl

omit [Finite F] [CharP F 2] in
theorem root_four_le_plane_radical :
    RootSubgroup.group (F := F) 4 ≤ (Plane.radical (F := F)).map planeLocal.subtype := by
  intro g hg
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 4 g).mp hg
  have hl : rootElement (K := F) 4 t ∈ planeLocal := by
    rw [mem_planeLocal_iff]
    constructor
    · rw [mem_planeParabolic_iff]
      intro i j
      rfl
    · simp [rootElement, rootMatrix]
  refine ⟨⟨rootElement 4 t, hl⟩, ?_, rfl⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [Finite F] in
theorem plane_fixed_eq_root_four :
    (Plane.radical (F := F)).map planeLocal.subtype ⊓
      centralizer (planeLocal (F := F) : Set (Sp F)) = RootSubgroup.group 4 := by
  apply le_antisymm
  · rintro g ⟨⟨q, hq, he⟩, hc⟩
    subst g
    have hcenter : q ∈ center (planeLocal (F := F)) :=
      mem_center_iff.mpr (fun l => Subtype.ext (hc l l.property))
    obtain ⟨z, hz⟩ := (Plane.mem_center_subgroupOf_iff_alternating
      (⟨q, hq⟩ : Plane.radical)).mp hcenter
    apply (RootSubgroup.mem_group_iff 4 _).mpr
    refine ⟨z, ?_⟩
    apply Subtype.ext
    have hm := Plane.radical_matrix (⟨q, hq⟩ : Plane.radical)
    change q.val.val.toBlocks₁₂ = _ at hz
    change (rootElement 4 z).val = q.val.val
    change q.val.val = _ at hm
    rw [hm, hz]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rootElement, rootMatrix, Matrix.single]
  · apply le_inf root_four_le_plane_radical
    apply le_centralizer_iff.mpr
    rw [RootNormalizerResidual.centralizer_four_eq]

omit [Finite F] in
theorem root_four_le_point_radical :
    RootSubgroup.group (F := F) 4 ≤ (pointRadical (F := F)).map pointLocal.subtype := by
  intro g hg
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 4 g).mp hg
  refine ⟨pointRadicalElement t 0 0, pointRadicalElement_mem _ _ _, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointRadicalElement, pointRadicalMatrix, rootElement, rootMatrix, Matrix.single]

include hcard hn in
theorem root_four_span :
    conjugateSpanBy (RootSubgroup.group (F := F) 4) pointLocal =
      (pointRadical (F := F)).map pointLocal.subtype := by
  let A := conjugateSpanBy (RootSubgroup.group (F := F) 4) pointLocal
  have hnorm : pointLocal ≤ normalizer
      ((pointRadical (F := F)).map pointLocal.subtype : Set (Sp F)) := by
    have hh := (pointRadical (F := F)).le_normalizer_map pointLocal.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hAR : A ≤ (pointRadical (F := F)).map pointLocal.subtype :=
    conjugateSpanBy_le root_four_le_point_radical hnorm
  have hAP : A ≤ pointLocal := hAR.trans (map_subtype_le _)
  let N := A.subgroupOf (pointLocal (F := F))
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  have hNR : N ≤ pointRadical := by
    intro x hx
    obtain ⟨q, hq, he⟩ := hAR hx
    exact (Subtype.ext he : q = x) ▸ hq
  rcases PointRadicalAction.normal_radical_dichotomy hcard hn N hNR with hc | he
  · have hx : rootElement (K := F) 4 1 ∈ A :=
      le_conjugateSpanBy _ _ ((RootSubgroup.mem_group_iff 4 _).mpr ⟨1, rfl⟩)
    have hc' : A ≤ RootSubgroup.group (F := F) 0 := by
      rw [← PointRadicalAction.center_eq_root hcard hn,
        ← map_subgroupOf_eq_of_le hAP]
      exact map_mono hc
    obtain ⟨z, hz⟩ := (RootSubgroup.mem_group_iff 0 _).mp (hc' hx)
    have hh := congrArg (fun g : Sp F => g.val (.inl 1) (.inr 0)) hz
    simp [rootElement, rootMatrix, Matrix.single] at hh
  · change A = _
    rw [← map_subgroupOf_eq_of_le hAP, show A.subgroupOf pointLocal = pointRadical from he]

include hcard hn in
theorem plane_radical_span :
    conjugateSpanBy ((Plane.radical (F := F)).map planeLocal.subtype) pointLocal =
      pointLocal := by
  let A := conjugateSpanBy ((Plane.radical (F := F)).map planeLocal.subtype) pointLocal
  have hAP : A ≤ pointLocal := conjugateSpanBy_le_self plane_radical_le_point
  let N := A.subgroupOf (pointLocal (F := F))
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  have hRN : pointRadical ≤ N := by
    intro q hq
    exact (conjugateSpanBy_mono root_four_le_plane_radical le_rfl)
      ((root_four_span hcard hn).symm ▸ mem_map_of_mem pointLocal.subtype hq)
  have hlarge : 2 < Nat.card F := by
    rw [hcard]
    exact (show 2 = 2 ^ 1 by decide).trans_lt (Nat.pow_lt_pow_right (by decide) hn)
  let : IsSimpleGroup (SpecialLinearGroup (Fin 2) F) := NaturalExtension.model_simple hlarge
  let : (N.map pointQuotient).Normal :=
    (inferInstance : N.Normal).map _ pointQuotient_surjective
  have hquot : N.map pointQuotient = ⊤ := by
    rcases (inferInstance : (N.map pointQuotient).Normal).eq_bot_or_eq_top with hb | ht
    · have hroot : rootElement (K := F) 2 1 ∈ (Plane.radical (F := F)).map planeLocal.subtype := by
        have hp : rootElement (K := F) 2 1 ∈ planeLocal := by
          rw [mem_planeLocal_iff]
          refine ⟨?_, ?_⟩
          · rw [mem_planeParabolic_iff]; intro i j; rfl
          · simp [rootElement, rootMatrix]
        refine ⟨⟨rootElement 2 1, hp⟩, ?_, rfl⟩
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      have ha := le_conjugateSpanBy ((Plane.radical (F := F)).map planeLocal.subtype) pointLocal hroot
      let x : pointLocal (F := F) := ⟨rootElement 2 1, plane_radical_le_point hroot⟩
      have hx : x ∈ N := ha
      have h1 := (map_eq_bot_iff N).mp hb hx
      have hentry := congrArg (fun a : SpecialLinearGroup (Fin 2) F => a.val 0 1) h1
      change (1 : F) = 0 at hentry
      exact (one_ne_zero hentry).elim
    · exact ht
  have htop : N = ⊤ := by
    have hh := congrArg (fun B : Subgroup (SpecialLinearGroup (Fin 2) F) =>
      B.comap pointQuotient) hquot
    simpa only [comap_map_eq, pointQuotient_ker, sup_eq_left.mpr hRN, comap_top] using hh
  change A = pointLocal
  rw [← map_subgroupOf_eq_of_le hAP, show A.subgroupOf pointLocal = ⊤ from htop,
    ← MonoidHom.range_eq_map, range_subtype]
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootCoreMatrix
