module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.PerfectFactor
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.NaturalBorelAction
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.FullSylowBlocks
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.OddDegree
public import Theory.GroupTheory.PCoreQuotientCoprimeSylowNormalizer
public import Theory.GroupTheory.PCoreNormalizerAction.Sylow

/-!
# The radical normalizes the actual escaping component

If the radical moves the component, rank-one relative normality forces
five-rank zero, while C.2.4(1) makes the full-Sylow component a chi-zero
block. Its binary field degree is odd. Coprime outer action and Thompson
heredity therefore place its actual Sylow normalizer in Mc. The original
intersection control makes this Borel normalize the first-factor action
on J/O₂(J). The binary Borel theorem forces that action to be inner,
contradicting its existing outer element of order five.

Consequently every extracted source component supplies C.2.7 and excludes
the marked natural row, without an additional normalization premise or
the disputed ordinary-centralizer identity. The quintic-exclusion owner
retains construction of NormalizerGeometry, the other model rows and final
p=3 assembly; the suitable-element odd-normalizer owner retains discharge
of the original 14.6.12--14 inputs.

Source: Aschbacher--Smith 14.6.15, printed p.1035, using C.2.4 and C.2.7.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- C.2.4(1) applies to the actual full-Sylow intersection in the second normalizer. -/
theorem source_component_chiZero_of_sylow_intersection
    (hSylow : Chapter1.IsSylowIn 2 (Mc.pCoreIn 2 ⊓ j.J) j.J) :
    ChapterC.IsChiZeroBlock j.J := by
  let N := normalizer (d.K2 : Set G)
  let R := (Mc.pCoreIn 2).subgroupOf N
  let B := (Mc ⊓ N).subgroupOf N
  let J := j.J.subgroupOf N
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  let e : J ≃* j.J := subgroupOfEquivOfLe j.component_le
  let : IsQuasisimple (j.J ⧸ pCore 2 j.J) := j.quasisimple
  let : IsQuasisimple (J ⧸ pCore 2 J) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hf : generalizedFitting J = pCore 2 J :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr
        ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp j.characteristic_component))
  have ho : pPrimeCore 2 N = ⊥ := pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp j.characteristic_normalizer)
  obtain ⟨P,hP⟩ := hSylow
  let S := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hS : (S : Subgroup J).map J.subtype ≤ R := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := hx
    have hyR : (y : G) ∈ Mc.pCoreIn 2 :=
      (hP.le (mem_map_of_mem j.J.subtype hy)).1
    have heG : (y : G) = ((x : N) : G) := by
      have he' := congrArg (fun z : J => ((z : N) : G)) he
      exact he'
    change ((x : N) : G) ∈ Mc.pCoreIn 2
    exact heG ▸ hyR
  have hblock := ChapterC.CatalogueFullSylow.constrained_component_chiZero_of_full_sylow
    hs.sqtk R B J hs.radical hs.characteristic_control j.component ho hf
    (fun h => j.outside (fun x hx => h (show (⟨x,j.component_le hx⟩ : N) ∈ J from hx)))
    S hS
  exact hblock.of_mulEquiv e

/-- Rank-one relative normality excludes a moved component of five-rank one. -/
theorem source_component_nonnormalized_rank_zero
    (hn : ¬Mc.pCoreIn 2 ≤ normalizer (j.J : Set G)) : primeRank 5 j.J = 0 := by
  have hr := j.quintic_rank
  have hne : primeRank 5 j.J ≠ 1 := by
    intro he
    exact hn (source_component_rank_one_input s d j he).normalizes
  omega

/-- The moved-component alternative is a genuine chi-zero block. -/
theorem source_component_nonnormalized_chiZero
    (hn : ¬Mc.pCoreIn 2 ≤ normalizer (j.J : Set G)) : ChapterC.IsChiZeroBlock j.J :=
  source_component_chiZero_of_sylow_intersection s d j
    (j.pushingUp_alternative.resolve_right hn)


/-- Thompson heredity controls the original radical-stabilizer normalizer. -/
theorem source_component_stabilizer_normalizer_control :
    normalizer (d.K2 : Set G) ⊓ normalizer
      ((Mc.pCoreIn 2 ⊓ normalizer (j.J : Set G) : Subgroup G) : Set G) ≤ Mc := by
  let N := normalizer (d.K2 : Set G)
  let R := (Mc.pCoreIn 2).subgroupOf N
  let B := (Mc ⊓ N).subgroupOf N
  let J := j.J.subgroupOf N
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  let e : J ≃* j.J := subgroupOfEquivOfLe j.component_le
  let : IsQuasisimple (j.J ⧸ pCore 2 j.J) := j.quasisimple
  let : IsQuasisimple (J ⧸ pCore 2 J) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have ht := ChapterC.Section02Source.thompson_le_component_normalizer_of_characteristicTwo
    R B J hs.radical ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp j.characteristic_normalizer)
    hs.characteristic_control
    (fun h => j.outside (fun x hx => h (show (⟨x,j.component_le hx⟩ : N) ∈ J from hx)))
    j.component
  have hc := ChapterC.Section02Source.stabilizer_normalizer_control hs.radical
    hs.characteristic_control ht
  have he : R ⊓ normalizer (J : Set N) =
      (Mc.pCoreIn 2 ⊓ normalizer (j.J : Set G)).subgroupOf N := by
    rw [←subgroupOf_normalizer_eq j.component_le]
    rfl
  rw [he] at hc
  rintro x ⟨hxN,hx⟩
  exact (hc (le_normalizer_comap N.subtype hx : (⟨x,hxN⟩ : N) ∈ _)).1

/-- Coprime outer action places the original component Borel inside Mc. -/
theorem source_component_sylow_normalizer_le_control
    (P : Sylow 2 j.J) (hP : (P : Subgroup j.J).map j.J.subtype = Mc.pCoreIn 2 ⊓ j.J)
    (hz : center (j.J ⧸ pCore 2 j.J) = ⊥)
    (ho : Nat.Coprime 2 (Nat.card (MulAut.Outer (j.J ⧸ pCore 2 j.J)))) :
    (normalizer (P : Set j.J)).map j.J.subtype ≤ Mc := by
  let R := Mc.pCoreIn 2 ⊓ normalizer (j.J : Set G)
  have hPR : (P : Subgroup j.J).map j.J.subtype ≤ R := by
    rw [hP]
    exact inf_le_inf_left _ j.J.le_normalizer
  have h := pGroup_sylow_normalizer_le_of_coprime_outer R j.J
    ((isPGroup_pCoreIn 2 Mc).to_le inf_le_left) inf_le_right hz ho P hPR
  exact (le_inf ((map_subtype_le _).trans j.component_le) h).trans
    (source_component_stabilizer_normalizer_control s d j)


/-- Full-Sylow pushing-up and odd binary field degree exclude the moved-component branch. -/
theorem source_component_radical_normalizes :
    Mc.pCoreIn 2 ≤ normalizer (j.J : Set G) := by
  by_contra hn
  have hr := source_component_nonnormalized_rank_zero s d j hn
  obtain ⟨P,hP⟩ := j.pushingUp_alternative.resolve_right hn
  let : IsQuasisimple (j.J ⧸ pCore 2 j.J) := j.quasisimple
  obtain ⟨n,hb,hodd⟩ := (source_component_nonnormalized_chiZero s d j hn).l2Even_of_five_rank_zero hr
  have ho : Nat.Coprime 2 (Nat.card (MulAut.Outer (j.J ⧸ pCore 2 j.J))) := by
    rw [hb.outer_card]
    exact Nat.coprime_two_left.mpr hodd
  obtain ⟨_,_,F,_,_,hF,_,hm⟩ := hb
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨e₀⟩ := hm.quotient_iso
  let C := j.J ⧸ pCore 2 j.J
  let e : C ≃* PSL(2,F) := e₀.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL
  have hz : center C = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hh : e z ∈ center PSL(2,F) := (centerCongr e ⟨z,hz⟩).property
    rw [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hB := source_component_sylow_normalizer_le_control s d j P hP hz ho
  have hK : d.K1 ≤ normalizer (j.J : Set G) :=
    (source_first_le_common_normalizer s d j).trans inf_le_left
  have hKP : d.K1 ≤ normalizer ((P : Subgroup j.J).map j.J.subtype : Set G) := by
    rw [hP]
    exact (le_inf ((source_first_le_common_normalizer s d j).trans inf_le_right) hK).trans
      (inf_normalizer_le_normalizer_inf)
  have hBK : (normalizer (P : Set j.J)).map j.J.subtype ≤ normalizer (d.K1 : Set G) := by
    intro x hx
    have hxJ : x ∈ j.J := map_subtype_le _ hx
    exact j.intersection_normalizes_first
      ⟨le_conjugateSpanBy _ _ hxJ, hB hx, j.component_le hxJ⟩
  let f : d.K1 →* MulAut C := (pCoreNormalizerAction 2 j.J).comp (inclusion hK)
  let Q := P.mapSurjective (f := QuotientGroup.mk' (pCore 2 j.J)) (QuotientGroup.mk'_surjective _)
  obtain ⟨k,hk,_,_,_,hout,hq⟩ := source_component_outer_quintic_of_rank_zero s d j hr
  let y : d.K1 := ⟨k,hk⟩
  have he : f y = pCoreNormalizerAction 2 j.J k := rfl
  let q := QuotientGroup.mk' (MulAut.innerSubgroup C)
  let g := q.comp f
  have hmem : q (pCoreNormalizerAction 2 j.J k) ∈ g.range := ⟨y,congrArg q he⟩
  have horder : orderOf (⟨q (pCoreNormalizerAction 2 j.J k),hmem⟩ : g.range) = 5 :=
    (Subgroup.orderOf_coe _).symm.trans hq
  have hd : 5 ∣ Nat.card g.range := horder ▸ orderOf_dvd_natCard
    (⟨q (pCoreNormalizerAction 2 j.J k),hmem⟩ : g.range)
  let : Group.IsSolvable (MulAut.Outer C) := source_component_core_outer_solvable s d j
  have hi2 := source_first_inner_intersection_isTwoGroup (s := s) d C f hd
  have hin := Theory.PSL2.borelActorInner_of_mulEquiv F e Q f.range
    (pCoreNormalizerAction_preserves_sylow j.J d.K1 hK P hKP)
    (pCoreNormalizerAction_borel_normalizes j.J d.K1 hK P hBK) hi2
  exact hout (hin ⟨y,he⟩)

/-- The extracted component always supplies the literal C.2.7 comparison input. -/
theorem source_component_input :
    Input KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G))
      (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G)) j.J :=
  source_component_normalized_input s d j (source_component_radical_normalizes s d j)

/-- The marked natural row is excluded without a separate normalization premise. -/
theorem source_component_no_natural_row :
    ¬Nonempty (NaturalStarRow j.J (Mc.pCoreIn 2)) := by
  rintro ⟨row⟩
  exact source_false_of_natural_row s d j (source_component_radical_normalizes s d j) row

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
