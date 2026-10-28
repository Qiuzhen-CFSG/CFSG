module
public import CFSG.Quasithin.Chapter10.SourceA5ElementComponent
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.Alternating.PrimeRank
/-!
# A strict opposite-component enlargement inside the original normalizer

For the original nonnormal A5 source, the prescribed half-Sylow T1 is
Sylow in N_G(L): it is already Sylow in N_M(L), and its full normalizer
lies in M. The original L is a normal C-component of N_G(L), whose
nontrivial two-core places this normalizer inside a two-local overgroup.

Apply the proved source containment theorem directly inside N_G(L) to
the opposite factor B=L^t. If N_G(L) is not contained in M, its normal
containing C-component I properly contains B and is distinct from L.
In the literal two-core quotient, the two distinct component images
commute. The centerless A5 image of L contributes rank one at both 3
and 5, leaving rank at most one for I at each prime.

This gives the actual single-enlargement obligation in 10.2.6(2), with
only D, its A5 quotient and nonnormality as source inputs. Excluding
that strict enlargement still requires the A.3.12/C.2.7 source inspection;
this module does not assert the final normalizer containment.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 10.2.6, printed pp.748--749, using 1.2.4 and 10.2.5.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The original half-Sylow is Sylow in the full component normalizer. -/
theorem source_a5_component_normalizer_sylow
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (normalizer (L : Set G)) :=
  exists_sylow_eq_of_relative_normalizer_le
    (source_nonnormal_stabilizer_sylow D hn) inf_le_right
    (le_inf (inf_le_right.trans (source_a5_sylow_stabilizer_normalizer_le D e hn)) inf_le_left)

/-- The original local C-component has the intrinsic minimality property. -/
theorem source_component_intrinsic : (⊤ : Subgroup L).IsCComponent := by
  simpa only [subgroupOf_self] using
    D.maximal.1.1.subgroupOf_of_le le_rfl (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)

/-- The original L is a genuine C-component of its full normalizer. -/
theorem source_component_in_normalizer :
    (L.subgroupOf (normalizer (L : Set G))).IsCComponent := by
  let B := L.subgroupOf (normalizer (L : Set G))
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  have ht : (⊤ : Subgroup B).IsCComponent := by
    have h := (source_component_intrinsic D).map_equiv
      (subgroupOfEquivOfLe L.le_normalizer).symm
    simpa only [map_top_of_surjective
      (subgroupOfEquivOfLe L.le_normalizer).symm.toMonoidHom
      (subgroupOfEquivOfLe L.le_normalizer).symm.surjective] using h
  have hh := ht.map_subtype (inferInstance : B.Normal).isSubnormal
  simpa only [←MonoidHom.range_eq_map,range_subtype] using hh

/-- The full normalizer has nontrivial two-core, inherited from L. -/
theorem source_component_normalizer_core_ne_bot :
    pCore 2 (normalizer (L : Set G)) ≠ ⊥ := by
  have hL : pCore 2 L ≠ ⊥ := by
    intro he
    have hc := centralizer_generalizedFitting_le L
    rw [(uniqueness D).generalizedFitting_eq_pCore,he] at hc
    apply (source_component_intrinsic D).ne_bot
    apply le_antisymm _ bot_le
    intro l _
    apply hc
    intro b hb
    have hb' : b = 1 := mem_bot.mp hb
    simp only [hb',one_mul,mul_one]
  intro he
  have hh : L.pCoreIn 2 ≤ (normalizer (L : Set G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes L.le_normalizer le_rfl
  have hbot : L.pCoreIn 2 = ⊥ := by
    apply bot_unique
    simpa only [pCoreIn,he,Subgroup.map_bot] using hh
  exact hL ((map_eq_bot_iff_of_injective _ L.subtype_injective).mp hbot)

/-- The actual full component normalizer is SQTK. -/
theorem source_component_normalizer_sqtk :
    IsSQTK KnownSimple.IsKnownSimple (normalizer (L : Set G)) := by
  obtain ⟨H,hH,hNH⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (normalizer (L : Set G)) (source_component_normalizer_core_ne_bot D)
  have hS := D.simpleQTKE.twoLocal_sqtk hH.1
  exact ⟨hS.stronglyQuasithin.of_injective (inclusion hNH) (inclusion_injective hNH),
    hS.isKGroup.of_injective (inclusion hNH) (inclusion_injective hNH)⟩

private theorem normalizer_quotient_sqtk :
    IsSQTK KnownSimple.IsKnownSimple
      ((normalizer (L : Set G)) ⧸ pCore 2 (normalizer (L : Set G))) := by
  have hs := source_component_normalizer_sqtk D
  refine ⟨?_,hs.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hs.stronglyQuasithin p hp ho)

private theorem normalizer_local_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {B : Subgroup G} (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hBL : B ≤ localOrbit T L) :
    B ∈ Chapter1.L G ((T : Subgroup G) ⊓ normalizer (L : Set G)) := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hBJ : B ⊔ R ≤ localJoin T L := sup_le (hBL.trans le_sup_left)
    (inf_le_left.trans le_sup_right)
  have hVR : D.moduleSubgroup ≤ R :=
    le_inf D.module_le_sylow (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hcore : D.moduleSubgroup ≤ (B ⊔ R).pCoreIn 2 :=
    le_pCoreIn_of_normalizes D.module_elementary.isPGroup
      (hVR.trans le_sup_right) (hBJ.trans D.join_normalizes_module)
  refine ⟨hB.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left (inf_le_left.trans le_sup_right)),?_,?_⟩
  · exact (source_a5_component_normalizer_sylow D e hn).restrict
      le_sup_right (sup_le (hBL.trans (source_nonnormal_orbit_le_normalizer D hn)) inf_le_right)
  · intro he
    exact D.module_ne_bot (bot_unique (hcore.trans_eq he))

/-- The original A5 factor leaves rank at most one at 3 and 5 for any other C-component of its normalizer. -/
theorem source_a5_component_normalizer_other_rank
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup (normalizer (L : Set G))} (hI : I.IsCComponent)
    (hne : I ≠ L.subgroupOf (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5) : primeRank p I ≤ 1 := by
  let N := normalizer (L : Set G)
  let A := L.subgroupOf N
  let q := QuotientGroup.mk' (pCore 2 N)
  let B := A.map q
  let E := I.map q
  let := pCore_isNilpotent (p := 2) (G := N)
  have hA : A.IsCComponent := source_component_in_normalizer D
  let eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe L.le_normalizer)
      (pCore_map_iso 2 (subgroupOfEquivOfLe L.le_normalizer))).trans e
  let eB : B ≃* alternatingGroup (Fin 5) := (cComponentTwoCoreQuotientEquiv hA).symm.trans eA
  have hcomm : E ≤ centralizer (B : Set (N ⧸ pCore 2 N)) := by
    rw [←commutator_eq_bot_iff_le_centralizer]
    exact ChapterA.Section03.CComponentCommutation.commutator_eq_bot
      (normalizer_quotient_sqtk D) (pCore_quotient_pCore_eq_bot 2)
      (hI.map_quotient _) (hA.map_quotient _)
      (fun he => hne (hI.eq_of_map_quotient_eq hA _ he))
  have hz : Nat.card (center B) = 1 := by
    rw [Nat.card_congr (centerCongr eB).toEquiv,
      alternatingGroup.center_eq_bot (by simp),card_bot]
  have hsum := ResidualCentralizerRank.primeRank_add_le_of_center_coprime E B hcomm
    (show Nat.Coprime p (Nat.card (center B)) by rw [hz]; exact Nat.coprime_one_right p)
  have ho : Odd p := by rcases hp with rfl | rfl <;> decide
  have hB : primeRank p B = 1 := by
    rw [primeRank_congr p eB]
    rcases hp with rfl | rfl <;>
      rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 _ (by decide) (by decide)]
  have hE : primeRank p I = primeRank p E := by
    rw [←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 I) pCore_isPGroup]
    exact primeRank_congr p (cComponentTwoCoreQuotientEquiv hI)
  have hQ : primeRank p (N ⧸ pCore 2 N) ≤ 2 :=
    (normalizer_quotient_sqtk D).stronglyQuasithin p (Fact.out : p.Prime) ho
  omega

/-- Failure of the desired normalizer containment forces a strict opposite-component enlargement with the source rank bounds. -/
theorem source_a5_escaping_component_normalizer_enlargement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (L : Set G) ≤ D.maximalLocal) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
      ∃ I : Subgroup (normalizer (L : Set G)), I.IsCComponent ∧ I.Normal ∧
        (L.map (MulAut.conj t).toMonoidHom).subgroupOf (normalizer (L : Set G)) < I ∧
        I ≠ L.subgroupOf (normalizer (L : Set G)) ∧
        primeRank 3 I ≤ 1 ∧ primeRank 5 I ≤ 1 := by
  let N := normalizer (L : Set G)
  let R := (T : Subgroup G) ⊓ N
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let B := L.map (MulAut.conj t).toMonoidHom
  have hBorb : B ≤ localOrbit T L := le_sup_right.trans hpair.ge
  have hBN : B ≤ N := hBorb.trans (source_nonnormal_orbit_le_normalizer D hn)
  have hlocalB : B ∈ Chapter1.L G (T : Subgroup G) := by
    have hh := (Chapter1.mem_L_map_iff (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).mpr D.maximal.1
    have he : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    rwa [he] at hh
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    have he : R.subgroupOf (T : Subgroup G) = N.subgroupOf (T : Subgroup G) := by
      ext x
      exact and_iff_right x.property
    have hnormal : (R.subgroupOf (T : Subgroup G)).Normal := by
      rw [he]
      exact normal_of_index_eq_two
        (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
    exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mp hnormal
  have hRB : R ≤ normalizer (B : Set G) := by
    have he : R.map (MulAut.conj t).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (hTR ht)
    rw [←he, show normalizer (B : Set G) =
      N.map (MulAut.conj t).toMonoidHom from
      (map_normalizer_eq_of_bijective L (MulAut.conj t).bijective).symm]
    exact map_mono inf_le_right
  obtain ⟨P,hP⟩ := source_a5_component_normalizer_sylow D e hn
  have hP' : (P : Subgroup N) = R.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hlocal : B.subgroupOf N ∈ Chapter1.L N (P : Subgroup N) := by
    rw [hP']
    exact (Chapter1.mem_LIn_iff_subgroupOf inf_le_right hBN).mp
      ⟨hBN,normalizer_local_component D e hn hlocalB hBorb⟩
  have hPN : (P : Subgroup N) ≤ normalizer (B.subgroupOf N : Set N) := by
    rw [hP',←subgroupOf_normalizer_eq hBN]
    exact fun x hx => hRB hx
  obtain ⟨I,⟨hI,hBI,hIN⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (normalizer_quotient_sqtk D) P hlocal hPN
  have hstrict : B.subgroupOf N < I := lt_of_le_of_ne hBI (by
    intro he
    apply hout
    change N ≤ normalizer (localOrbit T L : Set G)
    rw [hpair]
    apply (le_inf le_rfl ?_).trans (normalizer_inf_normalizer_le_normalizer_sup L B)
    exact (normal_subgroupOf_iff_le_normalizer hBN).mp (he ▸ hIN))
  have hne : I ≠ L.subgroupOf N := by
    intro he
    have hBL : B ≤ L := by
      intro b hb
      have hh := hBI (show (⟨b,hBN hb⟩ : N) ∈ B.subgroupOf N from hb)
      rwa [he] at hh
    have hJ : B ⊔ (T : Subgroup G) = L ⊔ (T : Subgroup G) := by
      have hh := mem_normalizer_iff_map_conj_eq.mp
        ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_right ht))
      rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)] at hh
      exact hh
    have hBc : (B.subgroupOf (L ⊔ (T : Subgroup G))).IsCComponent := hJ ▸ hlocalB.1
    have hcmp : B.subgroupOf (L ⊔ (T : Subgroup G)) =
        L.subgroupOf (L ⊔ (T : Subgroup G)) := by
      exact hBc.eq_of_le D.maximal.1.1 (comap_mono hBL)
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    change B = L
    have hm := congrArg (map (L ⊔ (T : Subgroup G)).subtype) hcmp
    rw [map_subgroupOf_eq_of_le ((show B ≤ B ⊔ (T : Subgroup G) from le_sup_left).trans_eq hJ),
      map_subgroupOf_eq_of_le le_sup_left] at hm
    exact hm
  exact ⟨t,ht,htn,hpair,I,hI,hIN,hstrict,hne,
    source_a5_component_normalizer_other_rank D e hI hne (Or.inl rfl),
    source_a5_component_normalizer_other_rank D e hI hne (Or.inr rfl)⟩
end CFSG.Quasithin.Chapter10
