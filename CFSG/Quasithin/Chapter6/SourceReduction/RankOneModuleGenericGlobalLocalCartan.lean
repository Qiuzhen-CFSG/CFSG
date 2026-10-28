module
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanPreparation
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.KnownSimple
public import CFSG.Quasithin.ChapterE.Section01.QuotientLifting.Generation
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.SpecificGroups.LinearSylowNormalizers
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.SylowLocalCore

/-!
# The common Cartan preparation before the residual-normalization split

The actual PSL₂ quotient places every proper overgroup of T∩L in its
Sylow normalizer. Thus O₂(H∩L)=T∩L, and N_G(L)∩H normalizes this
intersection and its local Borel. The Borel is solvable by its solvable
two-kernel and the triangular model. When n(H)>1, the original E.2.2
construction gives solvability of the unique maximal overgroup of T in H;
minimality identifies that subgroup with N_G(L)∩H.

These are the three geometric inputs to the existing compatible-Hall
construction. No assumption that the Borel normalizes O²(H) is made.
The same argument proves S∩L=T∩L for S=O₂(N_G(L)∩H).
The Chapter 12 extension discharges the proper-intersection hypothesis
using uniqueness over LT, before the stronger theorem 4.3.2 is needed.

Source: Aschbacher--Smith, 5.1.5 and 5.1.9--11, printed pp.631,634--635
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The normal restriction retains the original ambient Sylow intersection. -/
theorem exists_sylow_component {T : Sylow 2 G} {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
  obtain ⟨P, hP⟩ := (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) (sup_le L.le_normalizer hTL)
  exact ⟨P, by simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using hP⟩

omit [Finite G] in
private theorem sylow_eq_subgroupOf {T : Sylow 2 G} {L : Subgroup G}
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L) :
    (P : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  apply (map_injective L.subtype_injective)
  rw [hP, subgroupOf_map_subtype]

/-- The literal local Borel is an extension of a solvable triangular group by a two-group. -/
theorem localBorel_isSolvable {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Group.IsSolvable (localBorel T L) := by
  obtain ⟨P, hP⟩ := exists_sylow_component hTL
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext x
    exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  let : Group.IsSolvable q.ker := by
    rw [hk]
    exact @IsNilpotent.to_isSolvable _ _ pCore_isPGroup.isNilpotent
  let R := P.mapSurjective hq
  let : Group.IsSolvable (normalizer (R : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) :=
    Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_psl_two_normalizer hn hF R
  let : Group.IsSolvable ((normalizer (R : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))).comap q) :=
    isSolvable_comap_of_solvable_ker q _
  have hN : normalizer (P : Set L) ≤
      (normalizer (R : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))).comap q :=
    map_le_iff_le_comap.mp ((P : Subgroup L).le_normalizer_map q)
  let : Group.IsSolvable (normalizer (P : Set L)) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hN)
  rw [localBorel_eq_map, ← sylow_eq_subgroupOf P hP]
  exact Group.isSolvable_of_surjective (L.subtype.subgroupMap_surjective _)

/-- Source 5.1.5(1): the intersection normalizes T∩L through O₂(H∩L). -/
theorem intersection_normalizes_localSylow {T : Sylow 2 G} {L H : Subgroup G} {n : ℕ}
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hLH : ¬ L ≤ H) :
    normalizer (L : Set G) ⊓ H ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨P, hP⟩ := exists_sylow_component hTL
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e' := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext x
    exact e'.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  have hPH : (P : Subgroup L) ≤ H.subgroupOf L := by
    rw [sylow_eq_subgroupOf P hP]
    exact comap_mono hTH
  have hproper : H.subgroupOf L ≠ ⊤ := fun he => hLH (subgroupOf_eq_top.mp he)
  have hN := Matrix.SpecialLinearGroup.proper_overgroup_le_sylow_normalizer_of_two_kernel
    q hq P (hk ▸ pCore_isPGroup.le_sylow_of_normal P) _ hPH hproper
  have hHLN : H ⊓ L ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    have hh := (map_mono (f := L.subtype) hN).trans ((P : Subgroup L).le_normalizer_map L.subtype)
    simpa only [subgroupOf_map_subtype, hP] using hh
  have hcore : (H ⊓ L).pCoreIn 2 = (T : Subgroup G) ⊓ L := by
    apply le_antisymm
    · obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
        (show H ⊓ L ≤ L from inf_le_right) (hP ▸ le_inf (inf_le_left.trans hTH) inf_le_right)
      exact (pCoreIn_le_sylow _ Q).trans_eq (hQ.trans hP)
    · exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
        (le_inf (inf_le_left.trans hTH) inf_le_right) hHLN
  have hn : normalizer (L : Set G) ⊓ H ≤ normalizer ((H ⊓ L : Subgroup G) : Set G) :=
    (le_inf (inf_le_right.trans H.le_normalizer) inf_le_left).trans inf_normalizer_le_normalizer_inf
  rw [← hcore]
  exact hn.trans (normalizer_le_normalizer_characteristic_image (H ⊓ L) (pCore 2 (H ⊓ L : Subgroup G)))

/-- The same intersection acts on the original relative Borel N_L(T∩L). -/
theorem intersection_normalizes_localBorel {T : Sylow 2 G} {L H : Subgroup G} {n : ℕ}
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hLH : ¬ L ≤ H) :
    normalizer (L : Set G) ⊓ H ≤ normalizer (localBorel T L : Set G) := by
  intro g hg
  have hs := intersection_normalizes_localSylow hpsl hTL hTH hLH hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (L ⊓ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom = _
  have heL : L.map (MulAut.conj g).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hg.1
  have heS : ((T : Subgroup G) ⊓ L).map (MulAut.conj g).toMonoidHom = (T : Subgroup G) ⊓ L :=
    mem_normalizer_iff_map_conj_eq.mp hs
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, heL,
    map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
    heS]

open ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- A large generation parameter excludes a normal Sylow subgroup in the outside member. -/
theorem hstar_minimalParabolic_of_generation_gt_one {T : Sylow 2 G} {M H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hgen : 1 < ChapterE.generationParameter H) :
    IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  apply minimalParabolic_subtype T H
  apply Chapter3.HStar.minimalParabolic T hTM hH (Or.inr ?_)
  intro hn
  let : Group.IsSolvable H := ChapterE.IsTwoClosed.isSolvable ⟨T.subtype hH.1.1.2, hn⟩
  exact (Nat.not_le_of_gt hgen) ChapterE.generationParameter_le_one_of_solvable

omit [Finite G] in
private theorem hstar_maximal_eq_overlap {T : Sylow 2 G} {M H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    minimalParabolicMax (T.subtype hH.1.1.2) hP = M.subgroupOf H := by
  let J := minimalParabolicMax (T.subtype hH.1.1.2) hP
  have hJ := minimalParabolicMax_spec (T.subtype hH.1.1.2) hP
  have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
    have hh := map_mono (f := H.subtype) hJ.2
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hJH : J.map H.subtype < H := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hJ.1.lt_top
    change J.map H.subtype < (⊤ : Subgroup H).map H.subtype at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hJM : J ≤ M.subgroupOf H := map_le_iff_le_comap.mp
    (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
  have hn : M.subgroupOf H ≠ ⊤ := fun he => hH.1.2 (subgroupOf_eq_top.mp he)
  exact ((hJ.1.le_iff.mp hJM).resolve_left hn).symm

/-- The solvable maximal subgroup supplied by E.2.2 is the literal outside intersection. -/
theorem hstar_intersection_isSolvable {T : Sylow 2 G} {M H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hgen : 1 < ChapterE.generationParameter H) : Group.IsSolvable (M ⊓ H : Subgroup G) := by
  let hP := hstar_minimalParabolic_of_generation_gt_one hTM hH hgen
  obtain ⟨_, _, _, d, _⟩ := MarkedModels.Inverted.source_intrinsic_escape_knownSimple
    (Chapter3.sqtk_of_mem_H hG hH.1.1.1) (T.subtype hH.1.1.2) hP hgen
  have hs := d.maximal_solvable
  rw [hstar_maximal_eq_overlap hH hP] at hs
  let : Group.IsSolvable (M.subgroupOf H) := hs
  have hm : (M.subgroupOf H).map H.subtype = M ⊓ H := subgroupOf_map_subtype M H
  rw [← hm]
  exact Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective _)

/-- All inputs to the compatible-Hall construction follow from the earlier geometry. -/
theorem cartanPreparation_of_not_le {T : Sylow 2 G} {L H W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (hLH : ¬ L ≤ H) :
    CartanPreparation T L H :=
  ⟨localBorel_isSolvable h.exponent h.linear h.sylow_normalizes,
    hstar_intersection_isSolvable h.qtke h.sylow_normalizes hH hgen,
    intersection_normalizes_localBorel h.linear h.sylow_normalizes hH.1.1.2 hLH⟩

/-- Source 5.1.11(2): the two-core of the intersection contains the full left Sylow. -/
theorem sourceS_intersection_left {T : Sylow 2 G} {L H : Subgroup G} {n : ℕ}
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hLH : ¬ L ≤ H) :
    Global.sourceS L H ⊓ L = (T : Subgroup G) ⊓ L := by
  have hn := intersection_normalizes_localSylow hpsl hTL hTH hLH
  have hle : (T : Subgroup G) ⊓ L ≤ Global.sourceS L H :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (le_inf (inf_le_left.trans hTL) (inf_le_left.trans hTH)) hn
  exact le_antisymm (inf_le_inf_right L (Global.sourceS_le_sylow hTL hTH))
    (le_inf hle inf_le_right)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
