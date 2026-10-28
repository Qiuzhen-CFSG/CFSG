module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.QuotientRank
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.LowCubic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LowCubicModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LinearThreePrimeRank
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups
public import Theory.SpecificGroups.Janko1.PerfectSubgroupCore

/-!
# Excluding every strict ranked enlargement with a cubic divisor

The cubic rank bound reduces C.2.7 to binary SL₂ or SL₃. Full-Sylow
solvability excludes the first. In the second, the literal smaller component
maps to a proper local component of PSL₃. Parabolic placement identifies its
two-core quotient over the containing field; a split-torus prime contradicts
the original odd-prime rank bounds. This includes odd field degrees.

For a nonconstrained enlargement, module choice removes the odd core and
makes the containing component quasisimple. The original moved quotient
provides two-rank at least three. The low-cubic-rank catalogue leaves Bender,
binary PSL₃, or J₁. The first two are excluded as above. In J₁ every perfect
subgroup has central two-core; lifting through the actual central kernel
would make the original component quasisimple, contradicting its moved module.

The final applications keep the literal containing pair, half-join, relative
normality and original exchanger. They require component distinctness and
do not assert the source uniqueness theorem. That step, the three-free row,
the binary-three normalizer and final assembly remain with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the independent input from
qt-d-10-nona5-point-selection, with its final discharge retained by
qt-d-10-nona5-point-control.
Source: Aschbacher--Smith A.3.12, C.2.7 and 10.2.6,
printed pp.47--48,145--147,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H K : Subgroup G} {s : G}
namespace RankedEnlargement
variable (E : RankedEnlargement D H s K)
include E

private theorem local_join_ne_top (S : Sylow 2 K)
    (hlocal : (L.map (MulAut.conj s).toMonoidHom).subgroupOf K ∈ localCComponents S) :
    (L.map (MulAut.conj s).toMonoidHom).subgroupOf K ⊔ (S : Subgroup K) ≠ ⊤ := by
  intro ht
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  have hB : B.IsCComponent := by
    change (B.subgroupOf (B ⊔ (S : Subgroup K))).IsCComponent at hlocal
    rw [ht] at hlocal
    simpa only [map_subgroupOf_eq_of_le le_top] using
      hlocal.map_subtype (show (⊤ : Subgroup K).IsSubnormal from .top)
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using E.component.2.subgroupOf_of_le le_rfl E.component.1
  exact E.strict.ne (le_antisymm E.strict.le
    (subgroupOf_eq_top.mp (hB.eq_of_le htop le_top)))

/-- A strict local enlargement cannot have solvable proper full-Sylow overgroups. -/
theorem not_solvable_sylow_core_quotient
    (hproper : ∀ (S : Sylow 2 (K ⧸ pCore 2 K)) (P : Subgroup (K ⧸ pCore 2 K)),
      (S : Subgroup (K ⧸ pCore 2 K)) ≤ P → P ≠ ⊤ → Group.IsSolvable P) : False := by
  obtain ⟨S,_,hl⟩ := E.local_sylow
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let := isSolvable_proper_sylow_overgroup_of_twoCore_quotient hproper S
    (B ⊔ (S : Subgroup K)) le_sup_right (E.local_join_ne_top S hl)
  exact hl.not_isSolvable inferInstance

/-- The actual image of the smaller component stays proper under the two-core quotient. -/
theorem core_image_proper {X : Type*} [Group X]
    (q : K →* X) (hk : q.ker ≤ pCore 2 K) :
    ((L.map (MulAut.conj s).toMonoidHom).subgroupOf K).map q ≠ ⊤ := by
  obtain ⟨S,_,hl⟩ := E.local_sylow
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let P := B ⊔ (S : Subgroup K)
  intro hb
  have hp : P.map q = ⊤ := top_unique (hb ▸ map_mono (show B ≤ P from le_sup_left))
  have hker : q.ker ≤ P := (hk.trans (pCore_isPGroup.le_sylow_of_normal S)).trans le_sup_right
  have hh := congrArg (Subgroup.comap q) hp
  have he : P = ⊤ := by simpa only [Subgroup.comap_map_eq_self hker,Subgroup.comap_top] using hh
  exact E.local_join_ne_top S hl he

/-- The split torus in a containing PSL₃ contradicts the ranks of the literal smaller quotient. -/
theorem not_linear_three_of_three
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (dK : (K ⧸ pCore 2 K) ≃* PSL(3,F)) : False := by
  by_cases hn1 : n = 1
  · have hc : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
    exact E.not_solvable_sylow_core_quotient
      (isSolvable_proper_sylow_overgroup_of_equiv dK
        (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two hc))
  obtain ⟨S,_,hl⟩ := E.local_sylow
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let eB : L ≃* B := ((MulAut.conj s).subgroupMap L).trans
    (subgroupOfEquivOfLe E.strict.le).symm
  let q := dK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := dK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    ext x
    change dK (QuotientGroup.mk' (pCore 2 K) x) = 1 ↔ x ∈ pCore 2 K
    rw [dK.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let : Group.IsNilpotent q.ker := hk.symm ▸ pCore_isNilpotent
  have hB : B.map q ∈ localCComponents (S.mapSurjective hq) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have hkb : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective
  let eb := (q.subgroupMap B).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective B) hkb
  let e : (L ⧸ pCore 2 L) ≃* ((B.map q) ⧸ pCore 2 (B.map q)) :=
    (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans eb
  have hr (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
      primeRank p PSL(3,F) ≤ 1 := by
    let : Fact p.Prime := ⟨hp⟩
    rw [←primeRank_equiv p dK]
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans (E.ranks p hp ho hd)
  obtain ⟨p,hp,ho,hd,hrank⟩ := SourceEmbeddings.linear_three_local_shared_prime_rank
    hF (by omega) (S.mapSurjective hq) (B.map q) hB (E.core_image_proper q hk.le)
    (hr 3 (by decide) (by decide) h3)
  have hlrank := hr p hp ho ((Nat.card_congr e.toEquiv).symm ▸ hd)
  omega

/-- C.2.7 has no constrained enlargement as soon as three divides the original quotient. -/
theorem not_constrained_of_three
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L)) : generalizedFitting K ≠ pCore 2 K := by
  intro hf
  have hr := E.ranks 3 (by decide) (by decide) h3
  obtain ⟨F,hF⟩ := source_low_cubic_coreQuotient_linear (E.c27_input hf) hr
  rcases hF with hF | hF
  · exact E.not_binary_rank_one hF.some
  · obtain ⟨e⟩ := hF
    have hz : center SL(3,F.Carrier) = ⊥ := by
      apply (eq_bot_iff_card _).mpr
      rw [←Nat.card_congr (centerCongr e).toEquiv,
        source_rank_one_coreQuotient_center (E.c27_input hf) hr,card_bot]
    let d : SL(3,F.Carrier) ≃* PSL(3,F.Carrier) :=
      MulEquiv.ofBijective (Matrix.PSL3.projection F.Carrier) ⟨
        (MonoidHom.ker_eq_bot_iff _).mp (by rw [Matrix.PSL3.projection_ker,hz]),
        Matrix.PSL3.projection_surjective F.Carrier⟩
    exact E.not_linear_three_of_three h3 F.degree_pos F.card_eq (e.trans d)

/-- Perfect subgroups of J₁ have central two-core; central lifting contradicts the original moved factor. -/
theorem not_janko_one_core_quotient [IsQuasisimple K]
    (dK : (K ⧸ pCore 2 K) ≃* Janko1.Model) : False := by
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let eB : L ≃* B := ((MulAut.conj s).subgroupMap L).trans
    (subgroupOfEquivOfLe E.strict.le).symm
  let q : L →* Janko1.Model := (dK.toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 K))).comp (B.subtype.comp eB.toMonoidHom)
  have hk : q.ker ≤ center L := by
    intro l hl
    have he : dK (QuotientGroup.mk (eB l : K)) = 1 := hl
    have hz := IsQuasisimple.pCore_le_center 2
      ((QuotientGroup.eq_one_iff (eB l : K)).mp (dK.map_eq_one_iff.mp he))
    apply mem_center_iff.mpr
    intro m
    apply eB.injective
    simp only [map_mul]
    apply Subtype.ext
    exact mem_center_iff.mp hz (eB m : K)
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let f : PerfectCentralCovering.Cover L q.range := {
    toMonoidHom := q.rangeRestrict
    surjective := q.rangeRestrict_surjective
    isPerfect := inferInstance
    ker_le_center := fun l hl => hk (congrArg Subtype.val hl) }
  let : Group.IsPerfect q.range := Group.IsPerfect.range q
  have hm : (pCore 2 L).map q.rangeRestrict ≤ pCore 2 q.range :=
    le_sSup ⟨(inferInstance : (pCore 2 L).Normal).map _ q.rangeRestrict_surjective,
      pCore_isPGroup.map q.rangeRestrict⟩
  have hc : pCore 2 L ≤ center L := by
    rw [←f.comap_center]
    exact map_le_iff_le_comap.mp (hm.trans (Janko1.perfect_subgroup_pCore_two_le_center q.range))
  let := D.quasisimple
  exact source_component_not_quasisimple D (show PerfectCentralCovering.Cover L (L ⧸ pCore 2 L) from {
    toMonoidHom := QuotientGroup.mk' (pCore 2 L)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := by simpa only [QuotientGroup.ker_mk'] using hc }).isQuasisimple

/-- Both Fitting cases are impossible whenever three divides the original quotient. -/
theorem impossible_of_three
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L)) : False := by
  let : IsQuasisimple K := E.quasisimple_of_nonconstrained hchoice hmany hn hna
    (E.not_constrained_of_three h3)
  have h2 : 3 ≤ primeRank 2 (K ⧸ pCore 2 K) :=
    quasisimple_overgroup_quotient_twoRank D E.strict.le
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
  have hr := (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
    (E.ranks 3 (by decide) (by decide) h3)
  rcases SourceEmbeddings.models_of_three_le_twoRank_low_threeRank hmodel h2 hr
      with hb | hm | hm
  · exact E.not_solvable_sylow_core_quotient
      (SourceEmbeddings.bender_solvable_proper_sylow_overgroup hb)
  · obtain ⟨n,hnn,F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact E.not_linear_three_of_three h3 (by omega) hF e
  · exact E.not_janko_one_core_quotient hm.some

end RankedEnlargement

/-- Literal containing-pair application: three alone suffices after distinctness. -/
theorem ContainingPair.impossible_of_distinct_three
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hne : K₁ ≠ K₂) (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L)) : False := by
  obtain ⟨s,K,E⟩ := C.exists_rankedEnlargement hn hne
  exact E.impossible_of_three hchoice hmany hn hna h3

/-- Every binary rank-one quotient, in either field parity, supplies the cubic divisor. -/
theorem ContainingPair.impossible_of_distinct_binary_quotient
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hne : K₁ ≠ K₂)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) : False := by
  apply C.impossible_of_distinct_three hchoice hmany hn hna hne
  rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula]
  have hq : 0 < Nat.card F := Nat.card_pos
  by_cases hdiv : 3 ∣ Nat.card F
  · exact dvd_mul_of_dvd_left hdiv _
  · have hmod : Nat.card F % 3 = 1 ∨ Nat.card F % 3 = 2 := by omega
    apply dvd_mul_of_dvd_right
    apply Nat.dvd_of_mod_eq_zero
    have hsq : Nat.card F ^ 2 % 3 = 1 := by
      rcases hmod with hm | hm <;> simp [Nat.pow_mod,hm]
    have hpos : 0 < Nat.card F ^ 2 := pow_pos hq _
    omega
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
