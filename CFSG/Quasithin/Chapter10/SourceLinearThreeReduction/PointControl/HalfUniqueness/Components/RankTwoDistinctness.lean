module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.ContainingQuotients
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.ThreeDivisor
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.PairQuotient
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.AtlasPort.LinearGroups.G2.PerfectSubgroups

/-!
# Noncontainment and distinctness in binary rank-two containing models

The two original component quotients give odd rank at least two in L₀
at every odd prime dividing L/O₂(L). If a strict containing component K
contained L₀, that rank survives the literal map to K/O₂(K). Its image
is perfect. In binary PSL₃, Sp₄ and G₂, a full-Sylow overgroup containing
such an image is the whole model. Lifting across the two-core puts K
in L₀N_T(L), hence in M, contradicting strict containment.

The pair applications prove K₁ ≠ K₂ for these actual quotient markings,
with the original exchanger unchanged. Combining this with the proved
three-divisor enlargement contradiction excludes the corresponding pairs.
No point-centralizer control or normalizer bound is assumed. The remaining
containing models, three-free enlargement, binary-three zero-kernel
normalizer and final assembly remain with qt-d-10-nona5-half-sylow-unique.
ModuleChoiceAt is supplied by qt-d-10-nona5-point-selection, with its
ultimate discharge retained by qt-d-10-nona5-point-control.

Source: Aschbacher--Smith A.3.12 and 10.2.6, pp.47--48 and748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- Both original factors survive every odd prime in the literal orbit quotient. -/
theorem orbit_odd_primeRank_ge_two
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    2 ≤ primeRank p (localOrbit T L) := by
  obtain ⟨e⟩ := source_nonnormal_orbit_product_equiv D hn
  rw [←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 (localOrbit T L)) pCore_isPGroup,
    primeRank_congr p e,primeRank_prod_eq_add]
  have hp : primeRank p (L ⧸ pCore 2 L) ≠ 0 :=
    fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hd
  omega

private theorem ContainingPair.not_orbit_le_of_sylow_generation
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hstrict : L.map (MulAut.conj s).toMonoidHom < K)
    {X : Type*} [Group X] [Finite X]
    (e : (K ⧸ pCore 2 K) ≃* X)
    (hgen : ∀ (p : ℕ) (_ : Fact p.Prime), Odd p →
      ∀ A : Subgroup X, Group.IsPerfect A → 2 ≤ primeRank p A →
      ∀ (S : Sylow 2 X) (P : Subgroup X), (S : Subgroup X) ≤ P → A ≤ P → P = ⊤) :
    ¬ localOrbit T L ≤ K := by
  intro hOK
  let O := localOrbit T L
  let B := O.subgroupOf K
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨S,hS,_⟩ := C.local_sylow_in_containing hs hK hstrict.le
  let P := B ⊔ (S : Subgroup K)
  let A := B.map q
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect O := isPerfect_iSup_conjugates L T
  let b : O ≃* B := (subgroupOfEquivOfLe hOK).symm
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective
  let : Group.IsPerfect A := Group.IsPerfect.map q
  obtain ⟨p,hp,ho,hd⟩ := source_component_quotient_has_odd_prime D
  let : Fact p.Prime := ⟨hp⟩
  have hr : 2 ≤ primeRank p A := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q (hk.symm ▸ pCore_isPGroup),
      ←primeRank_congr p b]
    exact orbit_odd_primeRank_ge_two D hn ho hd
  have htop : P.map q = ⊤ := hgen p inferInstance ho A inferInstance hr
    (S.mapSurjective hq) (P.map q) (map_mono le_sup_right) (map_mono le_sup_left)
  have hker : q.ker ≤ P := (hk.le.trans (pCore_isPGroup.le_sylow_of_normal S)).trans le_sup_right
  have hP : P = ⊤ := by
    have he := congrArg (Subgroup.comap q) htop
    simpa only [comap_map_eq_self hker,comap_top] using he
  have hPM : P.map K.subtype ≤ D.maximalLocal := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hOK]
    refine sup_le O.le_normalizer ?_
    rw [hS,subgroupOf_map_subtype]
    exact inf_le_left.trans (inf_le_left.trans (le_normalizer_componentOrbit L T))
  have hKM : K ≤ D.maximalLocal := by
    simpa only [hP,←MonoidHom.range_eq_map,range_subtype] using hPM
  exact source_strict_conjugate_component_outside D hs hK hstrict hKM

/-- A binary PSL₃ containing component cannot contain both original factors.
The full Sylow and the orbit's odd rank two force its Sylow join to be full. -/
theorem ContainingPair.not_orbit_le_of_linear_three_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hstrict : L.map (MulAut.conj s).toMonoidHom < K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hnn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K ⧸ pCore 2 K) ≃* PSL(3,F)) : ¬ localOrbit T L ≤ K := by
  apply C.not_orbit_le_of_sylow_generation hn hs hK hstrict e
  intro p hp ho A hA hr S P hSP hAP
  let := hp
  let := hA
  apply Matrix.PSL3.LinearThree.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
    F ho hr hnn hF S P hSP A.subtype A.subtype_injective
  simpa only [range_subtype] using hAP

/-- The corresponding noncontainment for binary symplectic degree four. -/
theorem ContainingPair.not_orbit_le_of_symplectic_four_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hstrict : L.map (MulAut.conj s).toMonoidHom < K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (K ⧸ pCore 2 K) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    ¬ localOrbit T L ≤ K := by
  apply C.not_orbit_le_of_sylow_generation hn hs hK hstrict e
  intro p hp ho A hA hr S P hSP hAP
  let := hp
  let := hA
  apply Theory.SpecificGroups.SymplecticFour.perfect_odd_rank_two_sylow_overgroup_eq_top
    ho hr hF S P hSP A.subtype A.subtype_injective
  simpa only [range_subtype] using hAP

/-- The same full-Sylow argument excludes a common binary G₂ component. -/
theorem ContainingPair.not_orbit_le_of_g2_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hstrict : L.map (MulAut.conj s).toMonoidHom < K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (K ⧸ pCore 2 K) ≃* Atlas.G2.Model F) : ¬ localOrbit T L ≤ K := by
  apply C.not_orbit_le_of_sylow_generation hn hs hK hstrict e
  intro p hp ho A hA hr S P hSP hAP
  let := hp
  let := hA
  apply Atlas.G2.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
    ho hr hF S P hSP A.subtype A.subtype_injective
  simpa only [range_subtype] using hAP

private theorem ContainingPair.coincident_first
    (C : ContainingPair D H t K₁ K₂) (he : K₁ = K₂) :
    K₁.map H.subtype ∈ cComponentsIn H ∧
    L < K₁.map H.subtype ∧ localOrbit T L ≤ K₁.map H.subtype := by
  have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  have hL : L ≤ K₁.map H.subtype := by
    have h := map_mono (f := H.subtype) C.first_le
    rwa [map_subgroupOf_eq_of_le C.left_le] at h
  have hB : L.map (MulAut.conj t).toMonoidHom ≤ K₁.map H.subtype := by
    have h := map_mono (f := H.subtype) C.second_le
    rwa [map_subgroupOf_eq_of_le C.right_le,←he] at h
  refine ⟨⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩,?_,?_⟩
  · refine lt_of_le_of_ne hL ?_
    intro hEq
    have hc : L.map (MulAut.conj t).toMonoidHom = L :=
      Subgroup.eq_of_le_of_card_ge (hB.trans_eq hEq.symm)
        (card_map_of_injective (MulAut.conj t).injective).ge
    exact C.t_not_normalizes (mem_normalizer_iff_map_conj_eq.mpr hc)
  · rw [C.orbit_eq]
    exact sup_le hL hB

/-- Binary PSL₃ quotients force distinctness of the actual containing pair. -/
theorem ContainingPair.distinct_of_first_linear_three_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hnn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K₁ ⧸ pCore 2 K₁) ≃* PSL(3,F)) : K₁ ≠ K₂ := by
  intro he
  obtain ⟨hK,hLK,hOK⟩ := C.coincident_first he
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  have hs : L.map (MulAut.conj (1 : G)).toMonoidHom < K₁.map H.subtype := by
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    simpa only [hid,Subgroup.map_id] using hLK
  exact C.not_orbit_le_of_linear_three_quotient hn (one_mem _) hK hs hnn hF b hOK

/-- Binary Sp₄ quotients force distinctness without any original cubic divisor. -/
theorem ContainingPair.distinct_of_first_symplectic_four_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (K₁ ⧸ pCore 2 K₁) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) : K₁ ≠ K₂ := by
  intro he
  obtain ⟨hK,hLK,hOK⟩ := C.coincident_first he
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  have hs : L.map (MulAut.conj (1 : G)).toMonoidHom < K₁.map H.subtype := by
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    simpa only [hid,Subgroup.map_id] using hLK
  exact C.not_orbit_le_of_symplectic_four_quotient hn (one_mem _) hK hs hF b hOK

/-- Binary G₂ quotients also force distinctness on the original pair. -/
theorem ContainingPair.distinct_of_first_g2_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (K₁ ⧸ pCore 2 K₁) ≃* Atlas.G2.Model F) : K₁ ≠ K₂ := by
  intro he
  obtain ⟨hK,hLK,hOK⟩ := C.coincident_first he
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  have hs : L.map (MulAut.conj (1 : G)).toMonoidHom < K₁.map H.subtype := by
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    simpa only [hid,Subgroup.map_id] using hLK
  exact C.not_orbit_le_of_g2_quotient hn (one_mem _) hK hs hF b hOK

/-- The strict-enlargement consumer for a binary PSL₃ containing quotient,
with containing-component distinctness now discharged. -/
theorem ContainingPair.impossible_of_three_and_first_linear_three_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hnn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K₁ ⧸ pCore 2 K₁) ≃* PSL(3,F)) : False :=
  C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_first_linear_three_quotient hn hnn hF e) h3

/-- Apply symplectic distinctness to the same literal pair-exclusion consumer. -/
theorem ContainingPair.impossible_of_three_and_first_symplectic_four_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (K₁ ⧸ pCore 2 K₁) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) : False :=
  C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_first_symplectic_four_quotient hn hF e) h3

/-- Apply G₂ distinctness to the same literal pair-exclusion consumer. -/
theorem ContainingPair.impossible_of_three_and_first_g2_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (K₁ ⧸ pCore 2 K₁) ≃* Atlas.G2.Model F) : False :=
  C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_first_g2_quotient hn hF e) h3

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
