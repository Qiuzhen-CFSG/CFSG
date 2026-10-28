module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MathieuSolvableSpan.Restriction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.HexadPullback
public import Theory.SpecificGroups.SymmetricSix.SolvableGeneration

/-!
# Solvable-overgroup generation of an invariant Mathieu hexad

Let A contain the inner automorphism group of the actual M₂₂, and let S
be the ambient image of a Sylow two-subgroup of A. The action on 77 hexads
selects an S-invariant hexad B. Write E for the image under inner conjugation
of its M₂₂ stabilizer. The actual six-point action on its stabilizer in A
has solvable kernel and image A₆ or S₆. The two six-point parabolics therefore
lift to solvable overgroups of S which generate E S.

Thus E lies in the span of the solvable overgroups of S in A. Primitivity
of the hexad action proves ordinary maximality of E S in A. Every proper
subgroup containing S and that span is consequently E S, for this same B.
All actions, subgroup inclusions and conjugations use the native design.

This proves the intrinsic Mathieu solvable-overgroup geometry used in
Aschbacher--Smith 13.8.21(2), printed p.956 (PDF p.973), under Y = L₁.
Lifting through the source central kernel and comparing C-components in
H ∩ M are separate applications, not hypotheses of this result.
-/

public section

open Subgroup
open scoped Pointwise
open Sporadic.Mathieu
open Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MathieuSolvableSpan

private theorem solvable_comp_kernel {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : X →* Y) [Group.IsSolvable f.ker] (j : Z →* X) (hj : Function.Injective j) :
    Group.IsSolvable (f.comp j).ker := by
  let k : (f.comp j).ker →* f.ker :=
    (j.comp (f.comp j).ker.subtype).codRestrict f.ker (fun x => x.property)
  apply Group.isSolvable_of_isSolvable_injective (f := k)
  intro x y h
  apply Subtype.ext
  apply hj
  exact congrArg (fun z : f.ker => (z : X)) h

/-- The two actual six-point parabolics lift to solvable Sylow overgroups
whose images generate the invariant hexad stabilizer, including its outer supplement. -/
theorem join_le_solvableOvergroupSpan (A : Subgroup (MulAut M22)) (hA : m22InnerAut ≤ A)
    (P : Sylow 2 A) (B : Hexad)
    (hfix : (P : Subgroup A).map A.subtype ≤ fullHexad B) :
    innerHexad B ⊔ (P : Subgroup A).map A.subtype ≤
      solvableOvergroupSpan A ⊥ ((P : Subgroup A).map A.subtype) := by
  let F := (fullHexad B).subgroupOf A
  have hPF : (P : Subgroup A) ≤ F := by
    intro p hp
    exact hfix (mem_map.mpr ⟨p, hp, rfl⟩)
  let j : F →* fullHexad B := A.subtype.subgroupComap (fullHexad B)
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : fullHexad B => z.val) h))
  let f := (sixAction B).comp j
  let := sixAction_ker_solvable B
  let : Group.IsSolvable f.ker := solvable_comp_kernel (sixAction B) j hj
  have ha : alternatingGroup (Fin 6) ≤ f.range := by
    intro a ha
    rw [← m22HexadAction_range B.property] at ha
    obtain ⟨g, rfl⟩ := ha
    let z : F := ⟨⟨MulAut.conj g.val, hA ⟨g.val, rfl⟩⟩, (innerToHexad B g).property⟩
    exact ⟨z, sixAction_inner B g⟩
  obtain ⟨U, V, hU, hV, hUs, hVs, hgen⟩ := solvable_pair_of_six_action f ha (P.subtype hPF)
  let i : F →* MulAut M22 := A.subtype.comp F.subtype
  have hmapP : ((P.subtype hPF : Sylow 2 F) : Subgroup F).map i =
      (P : Subgroup A).map A.subtype := by
    change ((P : Subgroup A).subgroupOf F).map (A.subtype.comp F.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hPF]
  have hmapTop : (⊤ : Subgroup F).map i =
      innerHexad B ⊔ (P : Subgroup A).map A.subtype := by
    change (⊤ : Subgroup F).map (A.subtype.comp F.subtype) = _
    rw [← map_map, ← MonoidHom.range_eq_map, range_subtype]
    exact (subgroupOf_map_subtype _ _).trans (stabilizer_eq_join A hA P B hfix)
  have hspan (W : Subgroup F) (hPW : ((P.subtype hPF : Sylow 2 F) : Subgroup F) ≤ W)
      (hs : Group.IsSolvable W) :
      W.map i ≤ solvableOvergroupSpan A ⊥ ((P : Subgroup A).map A.subtype) := by
    let := hs
    apply le_sSup
    refine ⟨?_, ?_, Group.isSolvable_of_surjective (i.subgroupMap_surjective W)⟩
    · simpa only [bot_sup_eq, hmapP] using (map_mono (f := i) hPW)
    · rintro x ⟨w, _hw, rfl⟩
      exact w.val.property
  have hUV := sup_le (hspan U hU hUs) (hspan V hV hVs)
  rwa [← Subgroup.map_sup, hgen, hmapTop] at hUV

/-- Choose an actual invariant hexad, prove solvable-overgroup generation,
and prove ordinary maximality in the prescribed intermediate automorphism group. -/
theorem exists_hexad_solvable_span (A : Subgroup (MulAut M22)) (hA : m22InnerAut ≤ A)
    (P : Sylow 2 A) :
    ∃ B : Hexad,
      (P : Subgroup A).map A.subtype ≤ normalizer (innerHexad B : Set (MulAut M22)) ∧
      innerHexad B ≤ solvableOvergroupSpan A ⊥ ((P : Subgroup A).map A.subtype) ∧
      IsCoatom ((innerHexad B ⊔ (P : Subgroup A).map A.subtype).subgroupOf A) := by
  obtain ⟨B, hB⟩ := exists_invariant_hexad ((P : Subgroup A).map A.subtype)
    (P.isPGroup'.map A.subtype)
  exact ⟨B, hB.trans (innerHexad_normalized B),
    le_sup_left.trans (join_le_solvableOvergroupSpan A hA P B hB), join_isCoatom A hA P B hB⟩

private theorem eq_of_coatom_subgroupOf {X : Type*} [Group X]
    (A F J : Subgroup X) (hFA : F ≤ A) (hJA : J ≤ A) (hFJ : F ≤ J)
    (hJ : J ≠ A) (hmax : IsCoatom (F.subgroupOf A)) : J = F := by
  have hjtop : J.subgroupOf A ≠ ⊤ := by
    intro he
    exact hJ (hJA.antisymm (subgroupOf_eq_top.mp he))
  have he : F.subgroupOf A = J.subgroupOf A := by
    rcases eq_or_lt_of_le (comap_mono (f := A.subtype) hFJ) with he | hl
    · exact he
    · exact (hjtop (hmax.2 _ hl)).elim
  have hm := congrArg (map A.subtype) he
  rw [map_subgroupOf_eq_of_le hFA, map_subgroupOf_eq_of_le hJA] at hm
  exact hm.symm

/-- The selected hexad identifies every proper overgroup containing the
Sylow subgroup and all its solvable overgroups. The same hexad works for every J. -/
theorem exists_hexad_identifying_proper_overgroups
    (A : Subgroup (MulAut M22)) (hA : m22InnerAut ≤ A) (P : Sylow 2 A) :
    ∃ B : Hexad,
      (P : Subgroup A).map A.subtype ≤ normalizer (innerHexad B : Set (MulAut M22)) ∧
      innerHexad B ≤ solvableOvergroupSpan A ⊥ ((P : Subgroup A).map A.subtype) ∧
      IsCoatom ((innerHexad B ⊔ (P : Subgroup A).map A.subtype).subgroupOf A) ∧
      ∀ J : Subgroup (MulAut M22), J ≤ A → J ≠ A →
        (P : Subgroup A).map A.subtype ≤ J →
        solvableOvergroupSpan A ⊥ ((P : Subgroup A).map A.subtype) ≤ J →
        J = innerHexad B ⊔ (P : Subgroup A).map A.subtype := by
  obtain ⟨B, hn, hs, hm⟩ := exists_hexad_solvable_span A hA P
  refine ⟨B, hn, hs, hm, ?_⟩
  intro J hJA hne hPJ hspan
  exact eq_of_coatom_subgroupOf A _ J
    (sup_le ((innerHexad_le_inner B).trans hA) (map_subtype_le _)) hJA
    (sup_le (hs.trans hspan) hPJ) hne hm

/-- The intrinsic Mathieu statement, displaying the original hexad, inner
embedding and Sylow image without auxiliary model labels. -/
theorem mathieu_hexad_solvable_overgroups (A : Subgroup (MulAut M22))
    (hA : (MulAut.conj : M22 →* MulAut M22).range ≤ A) (P : Sylow 2 A) :
    let S := (P : Subgroup A).map A.subtype
    ∃ B : Finset (Fin 22), B ∈ m22Blocks ∧
      let E := (MulAction.stabilizer M22 B).map (MulAut.conj : M22 →* MulAut M22)
      S ≤ normalizer (E : Set (MulAut M22)) ∧
      E ≤ solvableOvergroupSpan A ⊥ S ∧
      IsCoatom ((E ⊔ S).subgroupOf A) ∧
      ∀ J : Subgroup (MulAut M22), J ≤ A → J ≠ A → S ≤ J →
        solvableOvergroupSpan A ⊥ S ≤ J → J = E ⊔ S := by
  obtain ⟨B, hn, hs, hm, hJ⟩ := exists_hexad_identifying_proper_overgroups A hA P
  exact ⟨B.val, B.property, hn, hs, hm, hJ⟩


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MathieuSolvableSpan
