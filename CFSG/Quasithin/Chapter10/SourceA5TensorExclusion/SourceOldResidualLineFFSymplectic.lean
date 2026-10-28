module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableSupplement
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.TwoSylowSource
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvariantLocalPair
public import CFSG.Quasithin.ChapterB.InternalThompsonAction

/-!
# The original tensor-line symplectic Cartan row

A solvable overgroup of a full Sylow two-subgroup in Sp₄(4) normalizes
that Sylow. Apply this to the intersection of the original Cartan--Sylow
join with the normal acting component. The marked component Sylow is its
two-core, so the whole join preserves it. The cubic Cartan induces inner
automorphisms because the symplectic outer group has order four.

A proper local C-component is a point or plane determinant kernel. After
aligning its marked Sylow by conjugation inside its normalizer, an inner
automorphism preserving that Sylow preserves both local factors. Thus the
original Cartan image normalizes the old residual image. The final theorem
uses the literal conjugation quotient and the original Sylow in the normal
component; it does not require normalization of the original ambient Sylow
or full movement of the Omega module.

Source: Aschbacher--Smith, original Proposition 9.3.1, printed pp.732--733,
combined manuscript of 1 March 2004. The Cartan--Sylow join's solvability is
an earlier-source input supplied by the original orbit Borel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.Section03
open Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms

namespace CFSG.Quasithin.Chapter10.SourceOldResidualLineFFSymplectic

private theorem adjust_sylow {G : Type*} [Group G] [Finite G]
    (S U : Sylow 2 G) (B : Subgroup G)
    (hS : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hU : (U : Subgroup G) ≤ normalizer (B : Set G)) :
    ∃ g ∈ normalizer (B : Set G),
      (S : Subgroup G).map (MulAut.conj g).toMonoidHom = U := by
  let N := normalizer (B : Set G)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq N (S.subtype hS) (U.subtype hU)
  refine ⟨g,g.property,?_⟩
  have hm := congrArg (fun P : Sylow 2 N => (P : Subgroup N).map N.subtype) hg
  change (((S : Subgroup G).subgroupOf N).map (MulAut.conj g).toMonoidHom).map N.subtype =
    ((U : Subgroup G).subgroupOf N).map N.subtype at hm
  rw [map_subgroupOf_eq_of_le hU] at hm
  calc
    _ = (((S : Subgroup G).subgroupOf N).map N.subtype).map
        (MulAut.conj (g : G)).toMonoidHom := by rw [map_subgroupOf_eq_of_le hS]
    _ = (((S : Subgroup G).subgroupOf N).map (MulAut.conj g).toMonoidHom).map N.subtype := by
      rw [map_map,map_map]
      rfl
    _ = U := hm

private theorem aligned_local {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (S : Sylow 2 (Sp F)) (B : Subgroup (Sp F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hSB : (S : Subgroup (Sp F)) ≤ normalizer (B : Set (Sp F))) :
    ∃ a : MulAut (Sp F), (S : Subgroup (Sp F)).map a.toMonoidHom = unipotent ∧
      (B.map a.toMonoidHom = pointLocal ∨ B.map a.toMonoidHom = planeLocal) := by
  obtain ⟨g,hg⟩ := SourceEmbeddings.FiveLocalFF.symplectic_local_placement
    (n := 2) hF (by decide) S B hB hproper
  let a := MulAut.conj g
  let B' := B.map a.toMonoidHom
  let S' := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let U := unipotentSylow (n := 2) hF (by decide)
  have hS' : (S' : Subgroup (Sp F)) ≤ normalizer (B' : Set (Sp F)) := by
    change (S : Subgroup (Sp F)).map a.toMonoidHom ≤ _
    rw [← map_equiv_normalizer_eq]
    exact map_mono hSB
  have hU : (U : Subgroup (Sp F)) ≤ normalizer (B' : Set (Sp F)) := by
    change unipotent ≤ _
    rcases hg with hg | hg
    · change B' = pointLocal at hg
      rw [hg]
      exact inf_le_left.trans (pointLocal (F := F)).le_normalizer
    · change B' = planeLocal at hg
      rw [hg]
      exact inf_le_right.trans (planeLocal (F := F)).le_normalizer
  obtain ⟨x,hx,hSU⟩ := adjust_sylow S' U B' hS' hU
  refine ⟨a.trans (MulAut.conj x),?_,?_⟩
  · change (S : Subgroup (Sp F)).map ((MulAut.conj x).toMonoidHom.comp a.toMonoidHom) = _
    rw [←map_map]
    exact hSU
  · have hB' : B'.map (MulAut.conj x).toMonoidHom = B' :=
      mem_normalizer_iff_map_conj_eq.mp hx
    change B.map ((MulAut.conj x).toMonoidHom.comp a.toMonoidHom) = pointLocal ∨
      B.map ((MulAut.conj x).toMonoidHom.comp a.toMonoidHom) = planeLocal
    rw [←map_map,hB']
    exact hg

private theorem three_power_inner {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (a : MulAut (Sp F)) {n : ℕ} (ha : a ^ (3 ^ n) = 1) :
    ∃ g : Sp F, MulAut.conj g = a := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))
  have hp : (q a) ^ (3 ^ n) = 1 := by rw [←map_pow,ha,map_one]
  have hq : q a = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 3 4).pow_left n)
      (orderOf_dvd_of_pow_eq_one hp) (by
        simpa only [card_outer_eq_two_mul (m := 2) hF (by decide)] using orderOf_dvd_natCard (q a)))
  exact (QuotientGroup.eq_one_iff a).mp hq

private theorem three_power_fixes_local {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (S : Sylow 2 (Sp F)) (B : Subgroup (Sp F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hSB : (S : Subgroup (Sp F)) ≤ normalizer (B : Set (Sp F)))
    (a : MulAut (Sp F)) {n : ℕ} (ha : a ^ (3 ^ n) = 1)
    (hS : (S : Subgroup (Sp F)).map a.toMonoidHom = S) :
    B.map a.toMonoidHom = B := by
  obtain ⟨c,hcS,hcB⟩ := aligned_local hF S B hB hproper hSB
  let b := MulAut.congr c a
  have hb : b ^ (3 ^ n) = 1 := by
    change (MulAut.congr c a) ^ (3 ^ n) = 1
    rw [←map_pow,ha,map_one]
  obtain ⟨g,hg⟩ := three_power_inner hF b hb
  have hU : unipotent.map b.toMonoidHom = unipotent := by
    calc
      _ = ((S : Subgroup (Sp F)).map c.toMonoidHom).map b.toMonoidHom := by rw [hcS]
      _ = ((S : Subgroup (Sp F)).map a.toMonoidHom).map c.toMonoidHom := by
        rw [map_map,map_map]
        congr 1
        ext x : 1
        change c (a (c.symm (c x))) = c (a x)
        rw [c.symm_apply_apply]
      _ = unipotent := by rw [hS,hcS]
  have hpair := local_pair_map_of_unipotent_map (n := 2) hF (by decide) b
    (hg ▸ inner_preservesDiagram g) hU
  have hB : (B.map c.toMonoidHom).map b.toMonoidHom = B.map c.toMonoidHom := by
    rcases hcB with hcB | hcB
    · rw [hcB]
      exact hpair.1
    · rw [hcB]
      exact hpair.2
  apply map_injective (f := c.toMonoidHom) c.injective
  calc
    _ = (B.map c.toMonoidHom).map b.toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      ext x : 1
      change c (a x) = c (a (c.symm (c x)))
      rw [c.symm_apply_apply]
    _ = _ := hB

/-- A cubic Cartan in a solvable Sylow overgroup preserves the original
proper local factor of a normal Sp₄(4) component. -/
theorem threeGroup_normalizes_local {Q F : Type*} [Group Q] [Finite Q] [Field F] [Finite F] [CharP F 2]
    (C : Subgroup Q) [C.Normal] (eC : C ≃* Sp F) (hF : Nat.card F = 4)
    (P : Sylow 2 Q) (R : Sylow 2 C)
    (hRP : (R : Subgroup C).map C.subtype ≤ P)
    (A B : Subgroup Q) (hBC : B ≤ C) (hA : IsPGroup 3 A)
    (hsol : Group.IsSolvable (A ⊔ (P : Subgroup Q) : Subgroup Q))
    (hPB : (P : Subgroup Q) ≤ normalizer (B : Set Q))
    (hB : B.subgroupOf C ∈ localCComponents R) (hproper : B.subgroupOf C ≠ ⊤) :
    A ≤ normalizer (B : Set Q) := by
  let Y := A ⊔ (P : Subgroup Q)
  let S := (R : Subgroup C).map C.subtype
  have hcontrol : SolvableSylowControl 2 C := SolvableSylowControl.of_equiv eC (by
    exact solvable_overgroups_of_orthogonal_root_orbits (n := 2) hF (by decide)
      (fun D hs hu => solvable_unipotent_point_orbit_orthogonal (by rw [hF]; decide) D hs hu))
  let := hsol
  have hYS : Y ≤ normalizer (S : Set Q) :=
    SolvableSylowControl.normalizes_sylow C Y hcontrol R le_normalizer_of_normal
      (hRP.trans le_sup_right)
  let RM := R.mapSurjective (f := eC.toMonoidHom) eC.surjective
  let BM := (B.subgroupOf C).map eC.toMonoidHom
  let : Group.IsSolvable eC.toMonoidHom.ker := by
    rw [eC.toMonoidHom.ker_eq_bot_iff.mpr eC.injective]
    infer_instance
  have hBM : BM ∈ localCComponents RM :=
    CFSG.Quasithin.Chapter1.Section02.localCComponents_map_of_solvable_ker hB eC.toMonoidHom
  have hBMproper : BM ≠ ⊤ := by
    intro ht
    apply hproper
    apply top_unique
    intro x _
    apply (mem_map_iff_mem (f := eC.toMonoidHom) eC.injective).mp
    change eC x ∈ BM
    rw [ht]
    trivial
  have hRB : (R : Subgroup C) ≤ normalizer (B.subgroupOf C : Set C) := by
    rw [←subgroupOf_normalizer_eq hBC]
    intro r hr
    exact hPB (hRP (mem_map_of_mem C.subtype hr))
  have hRMB : (RM : Subgroup (Sp F)) ≤ normalizer (BM : Set (Sp F)) := by
    change (R : Subgroup C).map eC.toMonoidHom ≤ _
    rw [←map_equiv_normalizer_eq]
    exact map_mono hRB
  intro a ha
  let aC : MulAut C := MulAut.conjNormal a
  let am := MulAut.congr eC aC
  obtain ⟨n,hn⟩ := hA.exists_pow_pow_eq_one (⟨a,ha⟩ : A)
  have haQ : a ^ (3 ^ n) = 1 := congrArg Subtype.val hn
  have haC : aC ^ (3 ^ n) = 1 := by
    change (MulAut.conjNormal a) ^ (3 ^ n) = 1
    rw [←map_pow,haQ,map_one]
  have ham : am ^ (3 ^ n) = 1 := by
    change (MulAut.congr eC aC) ^ (3 ^ n) = 1
    rw [←map_pow,haC,map_one]
  have hRa : (R : Subgroup C).map aC.toMonoidHom = R := by
    apply map_injective (f := C.subtype) C.subtype_injective
    calc
      _ = S.map (MulAut.conj a).toMonoidHom := by rw [map_map,map_map]; rfl
      _ = S := mem_normalizer_iff_map_conj_eq.mp (hYS ((show A ≤ Y from le_sup_left) ha))
  have hRMa : (RM : Subgroup (Sp F)).map am.toMonoidHom = RM := by
    change ((R : Subgroup C).map eC.toMonoidHom).map am.toMonoidHom = _
    calc
      _ = ((R : Subgroup C).map aC.toMonoidHom).map eC.toMonoidHom := by
        rw [map_map,map_map]
        congr 1
        ext x : 1
        change eC (aC (eC.symm (eC x))) = eC (aC x)
        rw [eC.symm_apply_apply]
      _ = _ := by rw [hRa]; rfl
  have hfix := three_power_fixes_local hF RM BM hBM hBMproper hRMB am ham hRMa
  have hfixC : (B.subgroupOf C).map aC.toMonoidHom = B.subgroupOf C := by
    apply map_injective (f := eC.toMonoidHom) eC.injective
    calc
      _ = BM.map am.toMonoidHom := by
        rw [map_map,map_map]
        congr 1
        ext x : 1
        change eC (aC x) = eC (aC (eC.symm (eC x)))
        rw [eC.symm_apply_apply]
      _ = BM := hfix
  apply mem_normalizer_iff_map_conj_eq.mpr
  calc
    B.map (MulAut.conj a).toMonoidHom =
        ((B.subgroupOf C).map C.subtype).map (MulAut.conj a).toMonoidHom := by
      rw [map_subgroupOf_eq_of_le hBC]
    _ = ((B.subgroupOf C).map aC.toMonoidHom).map C.subtype := by
      rw [map_map,map_map]
      rfl
    _ = B := by rw [hfixC,map_subgroupOf_eq_of_le hBC]

open CFSG.Quasithin.ChapterB.InternalThompsonAction

/-- The symplectic 9.3.1 row for the literal action quotient. The original
component Sylow and both subgroup images use the same quotient map. -/
theorem action_image_normalizes_local
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
    (W J K A : Subgroup X) [W.Normal] [J.Normal]
    (P : Sylow 2 X) (R : Sylow 2 J)
    (hRP : (R : Subgroup J).map J.subtype ≤ P)
    (hKJ : K ≤ J) (hA : IsPGroup 3 A)
    (hsol : Group.IsSolvable (A ⊔ (P : Subgroup X) : Subgroup X))
    (hPK : (P : Subgroup X) ≤ normalizer (K : Set X))
    (eJ : (J.map (actionMk W)) ≃* Sp F) (hF : Nat.card F = 4)
    (hK : (K.map (actionMk W)).subgroupOf (J.map (actionMk W)) ∈
      localCComponents (R.mapSurjective ((actionMk W).subgroupMap_surjective J)))
    (hproper : (K.map (actionMk W)).subgroupOf (J.map (actionMk W)) ≠ ⊤) :
    A.map (actionMk W) ≤ normalizer (K.map (actionMk W) : Set (ActionQuotient W)) := by
  let q := actionMk W
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let C := J.map q
  let : C.Normal := Normal.map inferInstance q hq
  let P' := P.mapSurjective hq
  let R' := R.mapSurjective (q.subgroupMap_surjective J)
  have hRP' : (R' : Subgroup C).map C.subtype ≤ P' := by
    change ((R : Subgroup J).map (q.subgroupMap J)).map C.subtype ≤
      (P : Subgroup X).map q
    rw [map_map]
    change (R : Subgroup J).map (q.comp J.subtype) ≤ _
    rw [←map_map]
    exact map_mono hRP
  let := hsol
  have hsol' : Group.IsSolvable (A.map q ⊔ (P' : Subgroup (ActionQuotient W)) :
      Subgroup (ActionQuotient W)) := by
    change Group.IsSolvable (A.map q ⊔ (P : Subgroup X).map q : Subgroup (ActionQuotient W))
    rw [←Subgroup.map_sup]
    exact Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  have hPK' : (P' : Subgroup (ActionQuotient W)) ≤ normalizer (K.map q : Set (ActionQuotient W)) :=
    (map_mono hPK).trans (le_normalizer_map q)
  exact threeGroup_normalizes_local C eJ hF P' R' hRP' (A.map q) (K.map q)
    (map_mono hKJ) (hA.map q) hsol' hPK' hK hproper

end CFSG.Quasithin.Chapter10.SourceOldResidualLineFFSymplectic
