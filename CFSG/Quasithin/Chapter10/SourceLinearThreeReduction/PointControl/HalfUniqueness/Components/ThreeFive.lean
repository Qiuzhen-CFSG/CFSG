module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.Nonconstrained
public import Theory.GroupAction.SimpleQuotientFiveAction
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LargeTwoRankBender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups

/-!
# Excluding strict containing components when three and five divide

The original moved factor retains a nontrivial perfect action after every
central quotient. Simplicity of the original two-core quotient and its
factor of five force the surviving elementary subgroup to have at least
sixteen elements. Thus a quasisimple containing component has two-core
quotient of two-rank at least four.

For a strict ranked enlargement, the existing C.2.7 comparison already
excludes the constrained case. Module choice removes the odd core and makes
the remaining component quasisimple. Its actual simple quotient is on the
full Theorem C list. The large two-rank, cubic-rank bound and factor of five
force a Bender model, where a nonsolvable proper full-Sylow overgroup is
impossible. The literal containing-pair applications preserve its exchanger
and specialize this to every even-degree binary rank-one quotient.

This completes both enlargement cases under the three-and-five hypothesis;
it does not assert containing-component distinctness or half-Sylow uniqueness.
Those steps, the remaining quotient rows and the binary-three normalizer
remain with qt-d-10-nona5-half-sylow-unique. The only independent source input
used here is ModuleChoiceAt, owned by qt-d-10-nona5-point-selection, with its
ultimate discharge retained by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.6, printed pp.748--749, using A.3.12 and C.2.7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
private theorem uniq : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- Every quasisimple overgroup of the original conjugate has large two-core quotient rank. -/
theorem quasisimple_overgroup_quotient_twoRank_of_five
    (h5 : 5 ∣ Nat.card (L ⧸ pCore 2 L))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} {K : Subgroup G} [IsQuasisimple K]
    (hBK : L.map (MulAut.conj t).toMonoidHom ≤ K) :
    4 ≤ primeRank 2 (K ⧸ pCore 2 K) := by
  let c := (MulAut.conj t).toMonoidHom
  let U₀ := ⁅D.fullModule,L⁆
  let U := U₀.map c
  let B := L.map c
  let A := B.subgroupOf K
  let E := U.subgroupOf K
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hU₀V : U₀ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp hLV
  have hU₀L : U₀ ≤ L := le_normalizer_iff_commutator_le_right.mp
    (D.fullModule_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hUB : U ≤ B := map_mono hU₀L
  have hUK : U ≤ K := hUB.trans hBK
  let := D.fullModule_elementary (uniq D)
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.of_injective
    (inclusion hU₀V) (inclusion_injective hU₀V)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map c
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hUK
  let j : A ≃* L := (subgroupOfEquivOfLe hBK).trans
    (L.equivMapOfInjective c (MulAut.conj t).injective).symm
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := j.symm.toMonoidHom) j.symm.surjective
  have hp : IsPPerfect 2 A := D.faithful.1.2.1.of_surjective
    j.symm.toMonoidHom j.symm.surjective
  let eA := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  let := SmallOffender.Recognition.FixedSpaces.quotient_simple D hn
  let : IsSimpleGroup (A ⧸ pCore 2 A) := eA.isSimpleGroup
  have h5A : 5 ∣ Nat.card (A ⧸ pCore 2 A) := (Nat.card_congr eA.toEquiv).symm ▸ h5
  have hBU : B ≤ normalizer (U : Set G) :=
    (map_mono (normalizer_commutator_ge_right D.fullModule L)).trans (U₀.le_normalizer_map c)
  have hAE : A ≤ normalizer (E : Set K) := by
    rw [←subgroupOf_normalizer_eq hUK]
    exact comap_mono hBU
  have hne : ⁅E,A⁆ ≠ ⊥ := by
    intro hz
    have hh := congrArg (map K.subtype) hz
    rw [map_commutator,map_subgroupOf_eq_of_le hUK,map_subgroupOf_eq_of_le hBK,
      Subgroup.map_bot] at hh
    have hzero : ⁅U₀,L⁆ = ⊥ := by
      apply (map_eq_bot_iff_of_injective (f := c) _ (MulAut.conj t).injective).mp
      simpa only [map_commutator] using hh
    exact source_full_moved_ne_bot D
      (commutator_eq_bot_of_iterated_eq_bot D.fullModule L hzero)
  exact Theory.GroupAction.SimpleQuotientFiveAction.four_le_twoRank_central_quotient
    A E (pCore 2 K) hp h5A hAE hne (IsQuasisimple.pCore_le_center 2)

omit D in
/-- Three and five exclude every strict ranked enlargement, including the
nonconstrained case. The only earlier source input is module choice. -/
theorem RankedEnlargement.impossible_of_three_five
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H K : Subgroup G} {s : G}
    (E : RankedEnlargement D H s K)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (h5 : 5 ∣ Nat.card (L ⧸ pCore 2 L)) : False := by
  let : IsQuasisimple K := E.quasisimple_of_nonconstrained hchoice hmany hn hna
    (E.not_constrained_of_three_five h3 h5)
  have h2 : 4 ≤ primeRank 2 (K ⧸ pCore 2 K) :=
    quasisimple_overgroup_quotient_twoRank_of_five D h5 hn E.strict.le
  have ho : pPrimeCore 2 K = ⊥ := by
    have hh := E.component.2.subnormal.pPrimeCore_eq_bot
      (oddCore_eq_bot_of_moduleChoice hchoice hmany D hn hna E.half_le) (K.subgroupOf H)
    have heq := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe E.component.1)
    rw [hh] at heq
    simpa only [Subgroup.map_bot] using heq.symm
  have hz : center K = pCore 2 K := IsQuasisimple.center_eq_pCore ho
  let qk : (K ⧸ pCore 2 K) ≃* (K ⧸ center K) :=
    QuotientGroup.quotientMulEquivOfEq hz.symm
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple (K ⧸ pCore 2 K) := by
    have hs := D.simpleQTKE.twoLocal_sqtk E.maximal.1
    have hKsq : IsSQTK KnownSimple.IsKnownSimple K := ⟨
      hs.stronglyQuasithin.of_injective (inclusion E.component.1) (inclusion_injective _),
      hs.isKGroup.of_injective (inclusion E.component.1) (inclusion_injective _)⟩
    refine ⟨?_,hKsq.isKGroup.quotient _⟩
    intro p hp hop
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p hop _ pCore_isPGroup).trans
      (hKsq.stronglyQuasithin p hp hop)
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    (MulEquiv.isSimpleGroup_congr qk).mpr IsQuasisimple.simple
  have hmodel : Chapter1.Section02.LocalModels.TheoremCModel (K ⧸ pCore 2 K) :=
    ChapterA.Section03.SourceComponents.sourceTheoremC_to_local
      (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K))
      (ChapterA.Section02.theoremC_knownSimple (G := K ⧸ pCore 2 K) inferInstance
        (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K))
        hsqtk.stronglyQuasithin hsqtk.isKGroup)
  have hb := SourceEmbeddings.bender_of_large_twoRank_low_threeRank_five hmodel h2
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      (E.ranks 3 (by decide) (by decide) h3))
    (E.odd_primes_retained (by decide) h5)
  obtain ⟨S,_,hlocal⟩ := E.local_sylow
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using E.component.2.subgroupOf_of_le le_rfl E.component.1
  have hproper : ∀ (S' : Sylow 2 K) (P : Subgroup K),
      (S' : Subgroup K) ≤ P → P ≠ ⊤ → Group.IsSolvable P := by
    intro S' P hSP hneP
    exact isSolvable_proper_sylow_overgroup_of_twoCore_quotient
      (G := K) (fun Q' P' hQ' hneQ' =>
        SourceEmbeddings.bender_solvable_proper_sylow_overgroup hb Q' P' hQ' hneQ')
      S' P hSP hneP
  have heB := SourceEmbeddings.eq_of_solvable_sylow_overgroups S hlocal htop le_top
    (isSolvable_proper_sylow_overgroup_of_equiv topEquiv hproper)
  exact E.strict.ne (le_antisymm E.strict.le (subgroupOf_eq_top.mp heB))

omit D in
/-- Apply the complete enlargement exclusion to the original pair and its
same exchanger. Only the still-separate distinctness step remains explicit. -/
theorem ContainingPair.impossible_of_distinct_three_five
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂) (hne : K₁ ≠ K₂)
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (h5 : 5 ∣ Nat.card (L ⧸ pCore 2 L)) : False := by
  obtain ⟨s,K,E⟩ := C.exists_rankedEnlargement hn hne
  exact E.impossible_of_three_five hchoice hmany hn hna h3 h5

omit D [Finite G] in
private theorem binary_quotient_three_five {n : ℕ} (he : Even n)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) ∧ 5 ∣ Nat.card (L ⧸ pCore 2 L) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let d := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  have hc : Nat.card (L ⧸ pCore 2 L) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr d.toEquiv,GorensteinWalter.sl2_card_formula,hF]
  have hpos : 1 ≤ (2 ^ n) ^ 2 := one_le_pow₀ (one_le_pow₀ (by decide : (1 : ℕ) ≤ 2))
  have hthree : (2 ^ n) ^ 2 % 3 = 1 := by
    rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num [Nat.pow_mod]
  have hfive : (2 ^ n) ^ 2 % 5 = 1 := by
    obtain ⟨k,rfl⟩ := he
    rw [← pow_mul,show (k + k) * 2 = 4 * k by omega,pow_mul]
    norm_num [Nat.pow_mod]
  have hsub := Nat.sub_add_cancel hpos
  have h3 : 3 ∣ (2 ^ n) ^ 2 - 1 := by omega
  have h5 : 5 ∣ (2 ^ n) ^ 2 - 1 := by omega
  rw [hc]
  exact ⟨dvd_mul_of_dvd_right h3 _,dvd_mul_of_dvd_right h5 _⟩

omit D in
/-- The full even-degree rank-one row of the strict-enlargement argument. -/
theorem RankedEnlargement.impossible_of_even_binary_quotient
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H K : Subgroup G} {s : G}
    (E : RankedEnlargement D H s K)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (he : Even n)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) : False := by
  obtain ⟨h3,h5⟩ := binary_quotient_three_five he hm
  exact E.impossible_of_three_five hchoice hmany hn hna h3 h5

omit D in
/-- The literal containing-pair consumer in the even-degree binary row;
distinctness is the remaining independent step within this task. -/
theorem ContainingPair.impossible_of_distinct_even_binary_quotient
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂) (hne : K₁ ≠ K₂)
    {n : ℕ} (he : Even n)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) : False := by
  obtain ⟨s,K,E⟩ := C.exists_rankedEnlargement hn hne
  exact E.impossible_of_even_binary_quotient hchoice hmany hn hna he hm

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
