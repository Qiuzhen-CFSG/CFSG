module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentNaturalAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentNaturalResidual

/-!
# Guarded reciprocal residuals for the natural selected A6 component

Split the omega orbit to project the original fixed-line generator to a
nonzero natural point with exactly the same centralizer in K. The point
centralizer has order 24 times the two-core order. Consequently the actual
L1 has three-rank one, excluding a covered original quotient. Intersecting
the two literal cubic residuals gives the reciprocal identity; their
{2,3}-group structure also gives the source two-residual identity.

The proofs specialize Nonsolvable/ComponentDoubled, ComponentContainment
and ComponentNaturalResidual at the same G,T. All quotient actions, subgroup
maps and relative normality hypotheses are retained. ComponentSixGeometryAt
applies this together with the nonsplit branch to the original module.
Source: Aschbacher--Smith 13.4.10(2--5), printed pp.908--909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V U : Subgroup G}

theorem component_fixed_generator_point_at
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G)) :
    ∃ w : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G),
      w ≠ 1 ∧ K ⊓ centralizer ({m.constant.val} : Set G) =
        K ⊓ centralizer ({w.val} : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z K
  let U := ⁅W,K⁆
  let C := Z ⊓ centralizer (K : Set G)
  let X := K ⊔ (T : Subgroup G)
  have hWX : W ≤ X := conjugateSpanBy_le
    ((show Z ≤ (T : Subgroup G) from fun _ hz =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans le_sup_right)
    (le_sup_left.trans X.le_normalizer)
  have hred := component_orbit_reduced h₀ hzT hz1 hKz hTK
  let := hred.elementary
  let : IsElementaryAbelian 2 W := by
    have hh : IsElementaryAbelian 2 ((W.subgroupOf X).map X.subtype) := IsElementaryAbelian.map _
    rwa [map_subgroupOf_eq_of_le hWX] at hh
  have hUW : U ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy Z K)
  have hCW : C ≤ W := inf_le_left.trans (le_conjugateSpanBy Z K)
  have hsplit : W = U ⊔ C := component_seed_split h₀ hzT hz1 hKz hTK
  have hdW : m.constant.val ∈ W := le_conjugateSpanBy _ _
    (m.constant_mem_central_four_at h structural).2
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hs : U.subgroupOf W ⊔ C.subgroupOf W = ⊤ := by
    rw [←subgroupOf_sup hUW hCW,←hsplit,subgroupOf_self]
  let : (U.subgroupOf W).Normal := normal_of_isMulCommutative _
  obtain ⟨a,ha,c,hc,hac⟩ := mem_sup_of_normal_left.mp
    (show (⟨m.constant.val,hdW⟩ : W) ∈ U.subgroupOf W ⊔ C.subgroupOf W from
      hs ▸ mem_top _)
  have he : a.val * c.val = m.constant.val := congrArg Subtype.val hac
  refine ⟨⟨a.val,ha⟩,?_,?_⟩
  · intro ha1
    have hh : a.val = 1 := congrArg Subtype.val ha1
    rw [hh,one_mul] at he
    exact hdK (he ▸ hc.2)
  · ext k
    constructor
    · rintro ⟨hk,hd⟩
      refine ⟨hk,mem_centralizer_singleton_iff.mpr ?_⟩
      have hck : k * c.val = c.val * k := hc.2 k hk
      have hh := mem_centralizer_singleton_iff.mp hd
      rw [←he] at hh
      have hh' : (k * a.val) * c.val = (a.val * k) * c.val := by
        simpa only [mul_assoc,←hck] using hh
      exact mul_right_cancel hh'
    · rintro ⟨hk,ha⟩
      refine ⟨hk,mem_centralizer_singleton_iff.mpr ?_⟩
      rw [←he]
      have hck : k * c.val = c.val * k := hc.2 k hk
      calc
        k * (a.val * c.val) = (k * a.val) * c.val := (mul_assoc _ _ _).symm
        _ = (a.val * k) * c.val := by rw [mem_centralizer_singleton_iff.mp ha]
        _ = a.val * (c.val * k) := by rw [mul_assoc,hck]
        _ = (a.val * c.val) * k := (mul_assoc _ _ _).symm


/-- The reciprocal point centralizers have the same literal residual when
both component quotients are ordinary A₆. -/
theorem component_reciprocal_residual_of_ordinary_six_at
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z} : Set G)))
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    Solvable.firstCentralizerResidual K m.constant.val =
      Solvable.firstCentralizerResidual L z := by
  let H := centralizer ({z} : Set G)
  let M := normalizer (L : Set G)
  let := h.quasisimple
  have hresH := (component_residual_of_ordinary_six h₀ hzT hz1 hK hHN hqK eK).1
  have hrM : primeRank 3 M ≤ 2 :=
    (h.source_normalizer_sqtk_at structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have hresM : (primeToResidual 3 M).map M.subtype = L :=
    (h.source_normalizer_component_at structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).map_primeToResidual_three_eq_of_quotient_alternating
        L.le_normalizer le_rfl (Or.inl rfl) eL hrM
  have he := embedded_primeToResidual_intersection_of_le 3 H K (H ⊓ M) inf_le_left hresH
  have hi : K ⊓ (H ⊓ M) = K ⊓ M :=
    le_antisymm (inf_le_inf_left _ inf_le_right)
      (le_inf inf_le_left (le_inf (inf_le_left.trans hK.1) inf_le_right))
  rw [hi] at he
  have hd : centralizer ({m.constant.val} : Set G) = M :=
    fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))
  rw [Solvable.firstCentralizerResidual_eq,hd]
  exact he.symm.trans (Solvable.firstCentralizerResidual_eq_intersection_residual z hresM)


private theorem natural_six_point_structure
    (DK : ChosenModule T K U)
    (q : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (v : U),
      (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
          (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd)
    (w : U) (hw : w ≠ 1) :
    primeRank 3 (K ⊓ centralizer ({w.val} : Set G) : Subgroup G) ≤ 1 ∧
      IsPiGroup twoThreePrimes (K ⊓ centralizer ({w.val} : Set G) : Subgroup G) := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
  have hc := BinaryPermutation.six_natural_point_card K U DK.normalizes q e he w hw
  rw [hn] at hc
  constructor
  · by_contra hh
    obtain ⟨E,_,hE⟩ := exists_elementary_nine_of_three_rank (by omega :
      2 ≤ primeRank 3 (K ⊓ centralizer ({w.val} : Set G) : Subgroup G))
    have hd := E.card_subgroup_dvd_card
    rw [hE,hc] at hd
    exact (by decide : ¬ 9 ∣ 24)
      (((by decide : Nat.Coprime 9 2).pow_right n).dvd_mul_right.mp hd)
  · rw [IsPiGroup_iff]
    intro p hp
    rw [hc] at hp
    change p.val = 2 ∨ p.val = 3
    have he : 24 * 2 ^ n = 2 ^ (n+3) * 3 := by ring
    rw [he] at hp
    rcases p.property.dvd_mul.mp hp with h2 | h3
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
        (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)

private theorem four_seed_generated
    (Z : Subgroup G) (hZ : Nat.card Z = 4) {z d : G}
    (hz : z ∈ Z) (hd : d ∈ Z) (hzcard : Nat.card (zpowers z) = 2)
    (hne : d ∉ zpowers z) : Z = zpowers z ⊔ zpowers d := by
  let S := zpowers z ⊔ zpowers d
  have hZS : S ≤ Z := sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hd)
  have hm : Nat.card (zpowers z) * (zpowers z).relIndex S = Nat.card S := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe (show zpowers z ≤ S from le_sup_left)).toEquiv]
    exact ((zpowers z).subgroupOf S).card_mul_index
  have hi : (zpowers z).relIndex S ≠ 1 := fun he =>
    hne (relIndex_eq_one.mp he (mem_sup_right (mem_zpowers d)))
  have hp := Nat.card_pos (α := S)
  have hu : Nat.card S ≤ 4 := hZ ▸ Nat.card_le_card_of_injective (inclusion hZS) (inclusion_injective _)
  rw [hzcard] at hm
  exact (eq_of_le_of_card_ge hZS (by rw [hZ]; omega)).symm

/-- The literal four-group seed has the same centralizer in K as the
original fixed-line generator. This does not assume that generator lies in U. -/
theorem component_four_seed_centralizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    {z : G} (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) :
    K ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) =
      K ⊓ centralizer ({m.constant.val} : Set G) := by
  have hzcard : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hzd : m.constant.val ∉ zpowers z := by
    intro hd
    exact hdK ((zpowers_le.mpr (show z ∈ centralizer (K : Set G) from
      fun k hk => mem_centralizer_singleton_iff.mp (hKz hk))) hd)
  have hZgen := four_seed_generated _ hcard hzT
    (m.constant_mem_central_four_at h structural).2 hzcard hzd
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr
      (m.constant_mem_central_four_at h structural).2))
  · intro k hk
    refine ⟨hk.1,?_⟩
    have hkz : zpowers z ≤ centralizer ({k} : Set G) := zpowers_le.mpr
      (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hKz hk.1)).symm)
    have hkd : zpowers m.constant.val ≤ centralizer ({k} : Set G) := zpowers_le.mpr
      (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hk.2).symm)
    have hc : omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer ({k} : Set G) := by
      rw [hZgen]
      exact sup_le hkz hkd
    exact fun a ha => mem_centralizer_singleton_iff.mp (hc ha)

/-- The fixed-free ordinary selected A₆ forces the original L quotient to be
ordinary, and identifies the two actual O² point residuals. No natural marking
or chosen-module minimality is assumed for the selected moved orbit. -/
theorem ordinary_original_of_fixedFree_six_component_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) = ⊥) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Solvable.firstCentralizerResidual L z.val ≤ K ∧
      primeRank 3 (Solvable.firstCentralizerResidual L z.val) = 1 ∧
      omegaOneCenterAmbient (T : Subgroup G) =
        V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 ∧
      Solvable.firstCentralizerResidual K m.constant.val =
        Solvable.firstCentralizerResidual L z.val ∧
      (pResidual 2 (K ⊓ centralizer
          (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Subgroup G)).map
          (K ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype =
        (pResidual 2 (L ⊓ centralizer ({z.val} : Set G) : Subgroup G)).map
          (L ⊓ centralizer ({z.val} : Set G)).subtype := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hqK := component_quotient_quasisimple h1332 hfK
  have hTK := (h1332 K hfK).1
  have hLK := (component_residual_of_ordinary_six h₀ hzT hz1 hK hHN hqK eK).2
  obtain ⟨DK,q,e,he,_,_,hZ,hcard⟩ := ordinary_six_component_marking_at h₀ h structural modules
    D m h1332 hindex z hzT hzL hK.1 hHN hKM hfK eK hfixed
  obtain ⟨w,hw,hCw⟩ := component_fixed_generator_point_at h₀ h structural m hzT hz1 hK.1 hTK hKM
  obtain ⟨hr,h23⟩ := natural_six_point_structure DK q e he w hw
  rw [←hCw] at hr h23
  have hLC : Solvable.firstCentralizerResidual L z.val ≤
      K ⊓ centralizer ({m.constant.val} : Set G) := by
    refine le_inf hLK ?_
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (m.constant_fixed a ((Solvable.firstCentralizerResidual_le L z.val ha).1))
  have hrl : primeRank 3 (Solvable.firstCentralizerResidual L z.val) ≤ 1 :=
    (_root_.primeRank_le_of_injective 3 (inclusion hLC) (inclusion_injective _)).trans hr
  let := h.quasisimple
  obtain ⟨eL⟩ := Solvable.ordinary_of_firstCentralizerResidual_threeRank D m z hzL hrl
  obtain ⟨_,hthree⟩ := Solvable.firstCentralizerResidual_order_of_marking D m z hzL
  have hrne : primeRank 3 (Solvable.firstCentralizerResidual L z.val) ≠ 0 :=
    fun hh => PrimeRank.eq_zero_iff_not_dvd_card.mp hh hthree
  have hrec := component_reciprocal_residual_of_ordinary_six_at h₀ h structural m hzT hz1
    hK hHN hqK eK eL
  refine ⟨⟨eL⟩,hLK,by omega,hZ,hcard,hrec,?_⟩
  rw [component_four_seed_centralizer_at h structural D m hzT hz1 hK.1 hKM hcard,
    twoResidual_eq_primeToResidual_three h23,←Solvable.firstCentralizerResidual_eq,hrec]
  exact (core_component_point_twoResidual D m eL z hzL).symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
