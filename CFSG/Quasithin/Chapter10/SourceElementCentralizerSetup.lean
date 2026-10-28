module
public import CFSG.Quasithin.Chapter10.SourceThompsonControl
public import Theory.GroupTheory.RelativeSylowNormalizer
public import Theory.GroupTheory.SaturatedCentralizer

/-!
# Element-centralizer preparation in the original Fundamental Setup

A nonidentity vector fixed by L₀T has its ambient centralizer in M by
source uniqueness. Every full-module vector can be conjugated inside M
so that C_T(v) is Sylow in C_M(v). If J(T) centralizes the full module,
Thompson control puts N_G(C_T(v)) in M, and relative Sylow promotion
makes C_T(v) Sylow in C_G(v). The bad-vector application retains the
literal conjugated component, commutator membership and failure of
centralizer containment.

The other normalizer branch uses exactly the earlier 10.2.1 conclusion
and Baum(T) fixing v; heredity identifies Baum(C_T(v)) with Baum(T).
For an escaping overgroup of L, source uniqueness also excludes any
nonzero characteristic subgroup of the original Baumann group normalized
by that overgroup, discharging the non-block alternative of C.1.24.
These results prove the initial Sylow reductions of 10.2.9(1). They do
not assert the subsequent enlarged-component classification or its A₇
block exclusion, and hence do not assert full element-centralizer control.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition 10.2.9, printed pp.750–753.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- A nonzero fixed vector is already controlled by original 1.2.7 uniqueness. -/
theorem source_fixed_element_centralizer_le
    {v : G} (hv : v ∈ D.fullModule) (hv1 : v ≠ 1)
    (hfix : v ∈ centralizer (localJoin T L : Set G)) :
    centralizer ({v} : Set G) ≤ D.maximalLocal := by
  have hp : IsPGroup 2 (zpowers v) :=
    (D.fullModule_elementary (uniqueness D)).isPGroup.to_le (zpowers_le.mpr hv)
  have hn : zpowers v ≠ ⊥ := by
    intro he
    exact hv1 (mem_bot.mp (he ▸ mem_zpowers v))
  have hJ : localJoin T L ≤ centralizer (zpowers v : Set G) := by
    apply le_centralizer_iff.mpr
    exact zpowers_le.mpr hfix
  have hc : centralizer ({v} : Set G) = centralizer (zpowers v : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hc]
  exact (Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness (uniqueness D)).2.2
      hp hn (hJ.trans (Subgroup.centralizer_le_normalizer _)))

/-- The first Sylow-normalizer branch of original 10.2.9(1). -/
theorem source_element_sylow_normalizer_of_thompson_centralizes
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    {v : G} (hv : v ∈ D.fullModule) :
    normalizer ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G) ≤ D.maximalLocal := by
  apply (source_two_overgroup_normalizer_le_of_centralizes D hJ _
    (T.isPGroup'.to_le inf_le_left) ?_).2
  exact le_inf (sSup_le fun _ hA => hA.1)
    (hJ.trans (centralizer_le (Set.singleton_subset_iff.mpr hv)))

/-- Promote the actual locally chosen centralizer Sylow to the ambient centralizer. -/
theorem source_element_sylow_of_thompson_centralizes
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    {v : G} (hv : v ∈ D.fullModule)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)) := by
  exact exists_sylow_eq_of_relative_normalizer_le hs inf_le_right
    (le_inf (inf_le_right.trans
      (source_element_sylow_normalizer_of_thompson_centralizes D hJ hv)) inf_le_left)

/-- Conjugation inside M makes the original Sylow centralizer Sylow in
C_M(v), preserving the full source module. -/
theorem source_exists_locally_sylow_element
    {v : G} (hv : v ∈ D.fullModule) :
    ∃ m : D.maximalLocal,
      (MulAut.conj (m : G)) v ∈ D.fullModule ∧
      Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({(MulAut.conj (m : G)) v} : Set G))
        (D.maximalLocal ⊓ centralizer ({(MulAut.conj (m : G)) v} : Set G)) := by
  let M := D.maximalLocal
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  let S := T.subtype hTM
  have hvT : v ∈ (T : Subgroup G) := D.fullModule_le_sylow (uniqueness D) hv
  let x : S := ⟨⟨v,hTM hvT⟩,hvT⟩
  obtain ⟨w, hw, hmax⟩ := S.exists_conjugate_with_saturated_centralizer x
  obtain ⟨m, hm⟩ := isConj_iff.mp hw
  let u : G := (w : M)
  have hu : (MulAut.conj (m : G)) v = u := congrArg M.subtype hm
  have huf : u ∈ D.fullModule := by
    rw [←hu]
    exact (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp hv
  let E : Subgroup M := (centralizer ({w} : Set S)).map (S : Subgroup M).subtype
  have hE : Chapter1.IsSylowIn 2 E (centralizer ({(w : M)} : Set M)) := by
    refine Chapter1.isSylowIn_iff.mpr ⟨(S.isPGroup'.to_subgroup _).map _, ?_, hmax⟩
    dsimp only [E]
    rw [map_subtype_centralizer_singleton]
    exact inf_le_right
  have heE : E.map M.subtype = (T : Subgroup G) ⊓ centralizer ({u} : Set G) := by
    change ((centralizer ({w} : Set S)).map (S : Subgroup M).subtype).map M.subtype = _
    rw [map_subtype_centralizer_singleton, Subgroup.map_inf _ _ _ M.subtype_injective,
      map_subtype_centralizer_singleton]
    change ((T : Subgroup G).subgroupOf M).map M.subtype ⊓ _ = _
    rw [map_subgroupOf_eq_of_le hTM, ←inf_assoc, inf_eq_left.mpr hTM]
  have hh := (Chapter1.IsSylowIn.map_iff M.subtype M.subtype_injective).mpr hE
  rw [heE, map_subtype_centralizer_singleton] at hh
  exact ⟨m,hu.symm ▸ huf,hu.symm ▸ hh⟩

/-- The WLOG conjugation and Sylow promotion in the centralizing Thompson
branch of 10.2.9(1), on the literal original full module. -/
theorem source_exists_sylow_element_of_thompson_centralizes
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    {v : G} (hv : v ∈ D.fullModule) :
    ∃ m : D.maximalLocal,
      (MulAut.conj (m : G)) v ∈ D.fullModule ∧
      normalizer ((T : Subgroup G) ⊓ centralizer ({(MulAut.conj (m : G)) v} : Set G) : Set G)
        ≤ D.maximalLocal ∧
      Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({(MulAut.conj (m : G)) v} : Set G))
        (centralizer ({(MulAut.conj (m : G)) v} : Set G)) := by
  obtain ⟨m,hm,hs⟩ := source_exists_locally_sylow_element D hv
  exact ⟨m,hm,source_element_sylow_normalizer_of_thompson_centralizes D hJ hm,
    source_element_sylow_of_thompson_centralizes D hJ hm hs⟩

/-- The original bad vector retains its failure of centralizer control
under conjugation inside M. -/
theorem source_element_centralizer_not_le_conj
    {v : G} (hout : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal)
    (m : D.maximalLocal) :
    ¬ centralizer ({(MulAut.conj (m : G)) v} : Set G) ≤ D.maximalLocal := by
  intro hc
  apply hout
  intro g hg
  apply (mem_normalizer_iff.mp (D.maximalLocal.le_normalizer m.property) g).mpr
  apply hc
  apply mem_centralizer_singleton_iff.mpr
  simpa only [map_mul, MulAut.conj_apply] using
    congrArg (MulAut.conj (m : G)) (mem_centralizer_singleton_iff.mp hg)

/-- Preparation of the actual commutator-vector contradiction in 10.2.9(1).
The conjugated component and vector are retained literally. The remaining
source cases begin with an element outside the fixed layer and a centralizer
whose specified Sylow has controlled normalizer. -/
theorem source_bad_commutator_element_preparation
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    {v : G} (hv : v ∈ ⁅D.fullModule,L⁆) (hv1 : v ≠ 1)
    (hout : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal) :
    ∃ m : D.maximalLocal,
      let u := (MulAut.conj (m : G)) v
      u ∈ ⁅D.fullModule,L.map (MulAut.conj (m : G)).toMonoidHom⁆ ∧
      u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ D.maximalLocal ∧
      u ∉ centralizer (localJoin T L : Set G) ∧
      normalizer ((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Set G) ≤ D.maximalLocal ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (centralizer ({u} : Set G)) := by
  have hvf : v ∈ D.fullModule :=
    (le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)) hv
  obtain ⟨m,hm,hn,hs⟩ := source_exists_sylow_element_of_thompson_centralizes D hJ hvf
  have hmem : (MulAut.conj (m : G)) v ∈
      ⁅D.fullModule,L.map (MulAut.conj (m : G)).toMonoidHom⁆ := by
    have hh := mem_map_of_mem (MulAut.conj (m : G)).toMonoidHom hv
    have he : D.fullModule.map (MulAut.conj (m : G)).toMonoidHom = D.fullModule := by
      convert mem_normalizer_iff_map_conj_eq.mp
        (D.maximalLocal_normalizes_fullModule m.property) using 1
      congr 1
    rw [map_commutator, he] at hh
    exact hh
  have hne : (MulAut.conj (m : G)) v ≠ 1 := by
    intro he
    exact hv1 ((MulAut.conj (m : G)).injective (he.trans (map_one _).symm))
  have ho := source_element_centralizer_not_le_conj D hout m
  exact ⟨m,hmem,hne,ho,(fun hf => ho (source_fixed_element_centralizer_le D hm hne hf)),hn,hs⟩

/-- The other Sylow-normalizer step of 10.2.9 uses exactly the earlier
10.2.1 bound and centralization of the vector by the original Baumann group. -/
theorem source_element_sylow_normalizer_of_baumann_centralizes
    (h1021 : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {v : G} (hB : ChapterB.baumann (T : Subgroup G) ≤ centralizer ({v} : Set G)) :
    normalizer ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G) ≤ D.maximalLocal := by
  have he : ChapterB.baumann ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      ChapterB.baumann (T : Subgroup G) :=
    baumann_eq_of_intermediate _ _ (le_inf inf_le_left hB) inf_le_left
  exact (normalizer_le_normalizer_baumann _).trans (he.symm ▸ h1021)

/-- Ambient Sylow promotion in the Baumann-fixed branch of original 10.2.9(1). -/
theorem source_element_sylow_of_baumann_centralizes
    (h1021 : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {v : G} (hB : ChapterB.baumann (T : Subgroup G) ≤ centralizer ({v} : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)) :=
  exists_sylow_eq_of_relative_normalizer_le hs inf_le_right
    (le_inf (inf_le_right.trans
      (source_element_sylow_normalizer_of_baumann_centralizes D h1021 hB)) inf_le_left)

/-- The characteristic-Baumann alternative of C.1.24 is impossible for
an enlarged source component escaping M. -/
theorem source_overgroup_characteristic_baumann_eq_bot
    (I : Subgroup G) (hLI : L ≤ I) (hout : ¬ I ≤ D.maximalLocal)
    (R : Subgroup (ChapterB.baumann (T : Subgroup G))) [R.Characteristic]
    (hn : I ≤ normalizer (R.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G)) :
    R = ⊥ := by
  by_contra hne
  let B := ChapterB.baumann (T : Subgroup G)
  let W := R.map B.subtype
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)).trans
      (normalizer_le_normalizer_characteristic_image B R)
  have hJW : localJoin T L ≤ normalizer (W : Set G) :=
    sup_le (iSup_conjugates_le_of_le_normalizer L T _ (hLI.trans hn)
      (hTW.trans (normalizer (W : Set G)).le_normalizer)) hTW
  have hp : IsPGroup 2 W :=
    ((T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)).to_subgroup R).map B.subtype
  have hWne : W ≠ ⊥ := fun he => hne ((R.map_eq_bot_iff_of_injective B.subtype_injective).mp he)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  exact hout (hn.trans (normalizer_le_of_unique_maximalTwoLocal
    (D.lemma_3_2_3_uniqueness hu).2.2 hp hWne hJW))

end CFSG.Quasithin.Chapter10
