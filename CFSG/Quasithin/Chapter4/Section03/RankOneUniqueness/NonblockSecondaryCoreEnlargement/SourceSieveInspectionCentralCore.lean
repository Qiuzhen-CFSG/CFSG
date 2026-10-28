module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionDegrees
public import Theory.Representation.SL2.SmallTwoGroupAction
public import Theory.GroupTheory.CenterlessSubgroupPrimeCentralizer
public import Theory.SpecificGroups.PSL2.EightCentralCovers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterTwoGroup

/-!
# Central secondary cores in the remaining source rows

The odd ternary models have sectional two-rank at most three. The binary
Frattini action bound therefore makes the literal secondary two-core
central. At degree three, the perfect-cover theorem identifies the secondary
image with PSL₂(8), contradicting the ordinary two-rank bound two. These
rows consequently have degree two, and the source cubic actor makes the
full component quotient centerless.

For J₂, the original secondary quotient and the actual model order bound
its two-core by sixteen. The same action bound makes that core central;
PSL₂(8) has no nontrivial perfect central cover. Generation forces a
nontrivial torus image, and faithful descent through the component center
makes its seven-element inner. Centralization would force 49 to divide
the model order, a contradiction. All source images use the unchanged
normalQuotientAction, including the whole-radical generation identity.

The final frontier is consumed by NonblockSecondaryCoreEnlargement.SourceSieveAssembly.
Odd ternary degree-two, binary rank-two, M₂₄, J₄ and Ru local inspection
still remain; no exceptional-model conclusion is claimed here.
Source: Aschbacher--Smith 4.3.12(2), 4.3.14--16, pp.617--618,
E.2.13(4), p.225, and the PSL₂(8) cover calculation cited in EightCentralCovers.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

private theorem secondary_core_central_of_section_bound
    (s : SecondaryActionData c n) (hn : 1<n)
    {A : Type*} [Group A] [Finite A] (e : SecondaryActionData.componentImage s ≃* A)
    (hb : ∀ (B : Subgroup A) (N : Subgroup B) [N.Normal], primeRank 2 (B ⧸ N) ≤ 3) :
    pCore 2 (SecondaryActionData.secondaryImage s) ≤
      center (SecondaryActionData.secondaryImage s) := by
  let := s.normal
  let X := SecondaryActionData.secondaryImage s
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component
    (s.secondary_le.trans (map_subtype_le _))
  have hXI := SecondaryActionData.secondaryImage_le_componentImage s
  let f := e.toMonoidHom.comp (inclusion hXI)
  have hf : Function.Injective f := e.injective.comp (inclusion_injective hXI)
  have hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^n) :=
    SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
  obtain ⟨F,_,_,hF,⟨d⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact Representation.SL2.core_le_center_of_section_rank_bound
    (d.trans (Theory.PSL2.sl2QuotientEquiv F).symm) (by omega) hF f hf hb (by omega)

/-- The entire two-core of the actual secondary image is central in every odd ternary row. -/
theorem SecondaryActionData.odd_ternary_secondary_core_central
    (s : SecondaryActionData c n) (hn : 1<n) {p : ℕ} (_hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 p ∨
      ClassicalGroup.IsPSU (SecondaryActionData.componentImage s) 3 p) :
    pCore 2 (SecondaryActionData.secondaryImage s) ≤
      center (SecondaryActionData.secondaryImage s) := by
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact secondary_core_central_of_section_bound s hn e (fun B N _ =>
      Theory.SpecificGroups.OddThreeSectionRank.psl3_subgroup_quotient_twoRank_le_three
        (by rwa [hF]) B N)
  · obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_equiv (SecondaryActionData.componentImage s) e.toEquiv
    exact secondary_core_central_of_section_bound s hn e (fun B N _ =>
      Theory.SpecificGroups.OddThreeSectionRank.psu3_subgroup_quotient_twoRank_le_three J
        (by rw [hF]; exact ho.pow) B N)

/-- The original secondary-core image satisfies the corrected centrality interface. -/
theorem SecondaryActionData.odd_ternary_coreImageCentral
    (s : SecondaryActionData c n) (hn : 1<n) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 p ∨
      ClassicalGroup.IsPSU (SecondaryActionData.componentImage s) 3 p) :
    SecondaryActionData.CoreImageCentral s := by
  let := s.normal
  have hc := SecondaryActionData.odd_ternary_secondary_core_central s hn hp ho hm
  intro a ha
  obtain ⟨x,hx,rfl⟩ := SourceImages.secondary_core_le c s.component ha
  intro y hy
  exact congrArg Subtype.val (mem_center_iff.mp (hc hx) ⟨y,hy⟩)
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- Odd ternary rows force the original source degree to be two, with central covers retained. -/
theorem SecondaryActionData.odd_ternary_degree_eq_two
    (s : SecondaryActionData c n) (hn : 1<n) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 p ∨
      ClassicalGroup.IsPSU (SecondaryActionData.componentImage s) 3 p) : n=2 := by
  have hn3 := SecondaryActionData.odd_ternary_degree_le_three s hp ho hm
  by_contra hne
  have heq : n=3 := by omega
  subst n
  let := s.normal
  let X := SecondaryActionData.secondaryImage s
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component
    (s.secondary_le.trans (map_subtype_le _))
  have hc := SecondaryActionData.odd_ternary_secondary_core_central s hn hp ho hm
  have hmodel : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^3) :=
    SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
  obtain ⟨F,_,_,hF,⟨d⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (GaloisField 2 3)
  let eF : F ≃+* GaloisField 2 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,GaloisField.card 2 3 (by decide)] using hF)
  let d' := d.trans (Atlas.fieldEquivPSL 2 eF)
  let cover : PerfectCentralCovering.Cover X (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 2 3)) := {
    toMonoidHom := d'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
    surjective := d'.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ d'.injective,QuotientGroup.ker_mk']
      exact hc }
  let e := Theory.SpecificGroups.PSL2Eight.coverEquiv cover
  have hl : 3 ≤ primeRank 2 X := by
    rw [primeRank_congr 2 e]
    exact Theory.PSL2.root_two_rank_ge (GaloisField 2 3) (GaloisField.card 2 3 (by decide))
  have hr : primeRank 2 (SecondaryActionData.componentImage s) ≤ 2 := by
    rcases hm with ⟨E,_,_,hE,⟨a⟩⟩ | ⟨E,_,_,J,hE,hJ,⟨a⟩⟩
    · rw [primeRank_congr 2 a]
      exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le hp ho hE
    · rw [primeRank_congr 2 a]
      exact Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J hp ho hE hJ
  have hu := Theory.GroupTheory.primeRank_le_of_injective 2
    (inclusion (SecondaryActionData.secondaryImage_le_componentImage s))
    (inclusion_injective (SecondaryActionData.secondaryImage_le_componentImage s))
  change 3 ≤ primeRank 2 (SecondaryActionData.secondaryImage s) at hl
  omega
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L}

private theorem janko_two_secondary_core_central
    (s : SecondaryActionData c 3)
    (e : SecondaryActionData.componentImage s ≃* Sporadic.LeechRelated.J2.Carrier) :
    pCore 2 (SecondaryActionData.secondaryImage s) ≤
      center (SecondaryActionData.secondaryImage s) := by
  let := s.normal
  let X := SecondaryActionData.secondaryImage s
  let P := pCore 2 X
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component
    (s.secondary_le.trans (map_subtype_le _))
  have hmodel : ClassicalGroup.IsPSL (X ⧸ P) 2 (2^3) :=
    SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let d := a.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  have hc : Nat.card (X ⧸ P) = 504 := by
    rw [Nat.card_congr d.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
    decide
  have hd : Nat.card X ∣ 604800 := by
    have hh := card_dvd_of_le (SecondaryActionData.secondaryImage_le_componentImage s)
    rw [Nat.card_congr e.toEquiv,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hh
    exact hh
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  have hcount : 2^k*504 = Nat.card X := by
    have hh := P.card_mul_index
    change Nat.card P * Nat.card (X ⧸ P) = Nat.card X at hh
    rwa [hk,hc] at hh
  have hk5 : k<5 := by
    by_contra! hh
    have hdiv : 2^5*504 ∣ 604800 :=
      (Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 hh) dvd_rfl).trans (hcount ▸ hd)
    norm_num at hdiv
  let W := P ⧸ frattini P
  have hw : Nat.card W ≤ 16 := by
    have hh := Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (frattini P))
    apply hh.trans
    rw [hk]
    exact Nat.pow_le_pow_right (by decide) (by omega : k≤4)
  have hr : primeRank 2 W < 2*3 := by
    have hh : primeRank 2 W ≤ 4 := (primeRank_le_iff_elementary_card_le W).mpr (by
      intro E _
      exact E.card_le_card_group.trans hw)
    omega
  have hzero := Representation.SL2.action_eq_one_of_small_frattini d (by decide) hF
    pCore_isPGroup hr (MulAut.conjNormal : X →* MulAut P)
  intro x hx
  apply mem_center_iff.mpr
  intro y
  have he := congrArg (fun f : X →* MulAut P => (f y ⟨x,hx⟩ : X)) hzero
  exact mul_inv_eq_iff_eq_mul.mp he

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L}

private theorem secondary_eight_equiv
    (s : SecondaryActionData c 3)
    (hc : pCore 2 (SecondaryActionData.secondaryImage s) ≤
      center (SecondaryActionData.secondaryImage s)) :
    Nonempty (SecondaryActionData.secondaryImage s ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 2 3)) := by
  let := s.normal
  let X := SecondaryActionData.secondaryImage s
  let : Group.IsPerfect X := SourceImages.secondary_perfect c s.component
    (s.secondary_le.trans (map_subtype_le _))
  have hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^3) :=
    SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
  obtain ⟨F,_,_,hF,⟨d⟩⟩ := hm
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (GaloisField 2 3)
  let eF : F ≃+* GaloisField 2 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,GaloisField.card 2 3 (by decide)] using hF)
  let d' := d.trans (Atlas.fieldEquivPSL 2 eF)
  exact ⟨Theory.SpecificGroups.PSL2Eight.coverEquiv {
    toMonoidHom := d'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
    surjective := d'.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ d'.injective,QuotientGroup.ker_mk']
      exact hc }⟩

/-- The degree-three J₂ inner model contradicts the actual torus action and generation. -/
theorem SecondaryActionData.not_janko_two_inner_degree_three
    (s : SecondaryActionData c 3) (hg : SecondaryActionData.ActionGeneration s)
    (e : SecondaryActionData.componentImage s ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  let := s.normal
  let := s.quasisimple
  let X := SecondaryActionData.secondaryImage s
  let I := SecondaryActionData.componentImage s
  have hXI : X ≤ I := SecondaryActionData.secondaryImage_le_componentImage s
  have hc := janko_two_secondary_core_central s e
  let a := (secondary_eight_equiv s hc).some
  have hz : center X = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have ha : a x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
      ((centerCongr a) ⟨x,hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot,mem_bot] at ha
    exact mem_bot.mpr (a.map_eq_one_iff.mp ha)
  have hcore : SecondaryActionData.CoreImageCentral s := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := SourceImages.secondary_core_le c s.component hx
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp (hc hz) ⟨y,hy⟩)
  have hY := SourceImages.torus_centralizes c s.component s.torus
    (s.secondary_le.trans (map_subtype_le _)) s.torus_le s.torus_secondary hcore
  obtain ⟨p,hp,ho,hd,y,hy,hyord⟩ :=
    SecondaryActionData.torus_prime_action_of_nontrivial_image s (by decide)
      (SecondaryActionData.torusImage_ne_bot_of_central_core_and_generation s hcore hg)
  have hp7 : p=7 := (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd |>.resolve_left hp.ne_one
  have hy7 := hyord.trans hp7
  have houtI : IsPGroup 2 (MulAut.Outer I) :=
    Sporadic.LeechRelated.J2.outer_isTwoGroup.of_equiv (MulAut.outerCongr e).symm
  have hout : IsPGroup 2 (MulAut.Outer (s.component ⧸ pCore 2 s.component)) :=
    houtI.of_injective (MulAut.centralQuotientOuter (SecondaryActionData.sieveCentralQuotientEquiv s))
      (MulAut.centralQuotientOuter_injective (SecondaryActionData.sieveCentralQuotientEquiv s))
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component))
  have hyI : s.action y ∈ I := by
    change s.action y ∈ SecondaryActionData.componentImage s
    rw [SecondaryActionData.componentImage_eq_inner]
    apply (QuotientGroup.eq_one_iff _).mp
    apply orderOf_eq_one_iff.mp
    have hcop := hout.orderOf_coprime (by decide : Nat.Coprime 2 7) (q (s.action y))
    have hdiv : orderOf (q (s.action y)) ∣ 7 := hy7 ▸ orderOf_map_dvd q (s.action y)
    exact Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdiv
  let B := X.subgroupOf I
  let b := subgroupOfEquivOfLe hXI
  have hzB : center B = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hb : b x ∈ center X := ((centerCongr b) ⟨x,hx⟩).property
    rw [hz,mem_bot] at hb
    exact mem_bot.mpr (b.map_eq_one_iff.mp hb)
  have h7 : 7 ∣ Nat.card B := by
    rw [Nat.card_congr (b.trans a).toEquiv]
    rw [←Nat.card_congr (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,
      GaloisField.card 2 3 (by decide)]
    decide
  have h49 : ¬7*7 ∣ Nat.card I := by
    rw [Nat.card_congr e.toEquiv,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    decide
  apply no_prime_centralizer_of_square_free_order B hzB h7 h49 ⟨s.action y,hyI⟩
  · intro x hx
    exact Subtype.ext (hY (mem_map_of_mem s.action hy) x hx)
  · exact (Subgroup.orderOf_coe ⟨s.action y,hyI⟩).symm.trans hy7
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The original secondary quotient excludes J₂ in every source degree greater than one. -/
theorem SecondaryActionData.not_janko_two_inner
    (s : SecondaryActionData c n) (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (e : SecondaryActionData.componentImage s ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  have hd := SecondaryActionData.secondary_order_dvd_inner s
  rw [Nat.card_congr e.toEquiv,
    Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
  have hn8 : n<8 := by
    by_contra! hh
    have hb := (Nat.pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hd)
    norm_num at hb
  have hdegree : n=2 ∨ n=3 := by
    interval_cases n
    all_goals first | (solve | left; rfl) | (solve | right; rfl) | (solve | norm_num at hd)
  rcases hdegree with rfl | rfl
  · exact SecondaryActionData.not_sporadic_inner_of_even s (by decide) D h
      (Or.inl ⟨.j2,(fun hh => by cases hh),⟨e⟩⟩) (by
        rw [primeRank_congr 3 e]
        exact Sporadic.LeechRelated.J2.three_rank_ge_two)
  · exact SecondaryActionData.not_janko_two_inner_degree_three s hg e

/-- Centrality of the secondary core and perfectness kill the radical-secondary commutator. -/
theorem SecondaryActionData.radical_centralizes_secondary_of_coreImageCentral
    (s : SecondaryActionData c n) (hc : SecondaryActionData.CoreImageCentral s) :
    SecondaryActionData.radicalImage s ≤ centralizer (SecondaryActionData.secondaryImage s : Set _) := by
  let := s.normal
  let : Group.IsPerfect (SecondaryActionData.secondaryImage s) :=
    SourceImages.secondary_perfect c s.component
    (s.secondary_le.trans (map_subtype_le _))
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_eq_bot_of_iterated_eq_bot
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_trans _ hc
  change ⁅SourceImages.image c s.component (R₂ c),
    SourceImages.image c s.component (secondary c)⁆ ≤
      SourceImages.image c s.component ((secondary c).pCoreIn 2)
  rw [←SourceImages.image_commutator c s.component _ _ s.radical_le
    (s.secondary_le.trans (map_subtype_le _))]
  apply map_mono
  apply subgroupOf_mono
  rw [commutator_comm]
  exact commutator_le_pCore_of_mutual_normalization _ _ (isPGroup_pCoreIn 2 _)
    (secondary_normalizes_radical c)
    ((R₂ c).le_normalizer.trans (s.radical_normalizer.trans inf_le_right))

/-- Only the moved core remains in the radical image; its torus image is nontrivial. -/
theorem SecondaryActionData.odd_ternary_action_structure
    (s : SecondaryActionData c n) (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 p ∨
      ClassicalGroup.IsPSU (SecondaryActionData.componentImage s) 3 p) :
    SecondaryActionData.CoreImageCentral s ∧
      SecondaryActionData.torusImage s ≤ centralizer (SecondaryActionData.secondaryImage s : Set _) ∧
      SecondaryActionData.radicalImage s ≤ centralizer (SecondaryActionData.secondaryImage s : Set _) ∧
      SecondaryActionData.radicalImage s = SecondaryActionData.coreImage s ∧
      SecondaryActionData.torusImage s ≠ ⊥ := by
  let := s.normal
  have hc := SecondaryActionData.odd_ternary_coreImageCentral s hn hp ho hm
  have hR := SecondaryActionData.radical_centralizes_secondary_of_coreImageCentral s hc
  refine ⟨hc,SourceImages.torus_centralizes c s.component s.torus
    (s.secondary_le.trans (map_subtype_le _)) s.torus_le s.torus_secondary hc,hR,?_,
    SecondaryActionData.torusImage_ne_bot_of_central_core_and_generation s hc hg⟩
  have hh := commutator_eq_bot_iff_le_centralizer.mpr hR
  change SecondaryActionData.coreImage s ⊔
    ⁅SecondaryActionData.radicalImage s,SecondaryActionData.secondaryImage s⁆ =
      SecondaryActionData.radicalImage s at hg
  rw [hh,sup_bot_eq] at hg
  exact hg.symm

/-- The remaining actual models, with degree-three odd ternary rows and J₂ removed. -/
theorem SecondaryActionData.inspection_remaining_rows_after_core_analysis
    (s : SecondaryActionData c n) (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (n=2 ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 p ∨
        ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 p)) ∨
      (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
        (SecondaryActionData.componentImage s) f) ∨
      (Odd n ∧ ((n=3 ∧ ∃ name : ClassificationModels.SporadicName,
        (name = .m24 ∨ name = .ru) ∧
        Nonempty (SecondaryActionData.componentImage s ≃* name.Carrier)) ∨
        Nonempty (SecondaryActionData.componentImage s ≃* Janko4.Model))) := by
  rcases SecondaryActionData.inspection_remaining_rows s hn hg D h with
    ⟨_,p,hp,ho,hm⟩ | hm | ⟨ho,hm⟩
  · have heq := SecondaryActionData.odd_ternary_degree_eq_two s hn hp ho hm
    subst n
    have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h (by decide)
    let a : (s.component ⧸ pCore 2 s.component) ≃* SecondaryActionData.componentImage s :=
      ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
        (SecondaryActionData.sieveCentralQuotientEquiv s)
    exact Or.inl ⟨rfl,p,hp,ho,hm.elim
      (fun hm => Or.inl (hm.of_mulEquiv a)) (fun hm => Or.inr (hm.of_mulEquiv a))⟩
  · exact Or.inr (Or.inl hm)
  · apply Or.inr ∘ Or.inr
    refine ⟨ho,?_⟩
    rcases hm with ⟨hn3,name,hname,⟨e⟩⟩ | hm
    · rcases hname with rfl | rfl | rfl
      · exact Or.inl ⟨hn3,.m24,by simp,⟨e⟩⟩
      · exact (SecondaryActionData.not_janko_two_inner s hn hg D h e).elim
      · exact Or.inl ⟨hn3,.ru,by simp,⟨e⟩⟩
    · exact Or.inr hm
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
