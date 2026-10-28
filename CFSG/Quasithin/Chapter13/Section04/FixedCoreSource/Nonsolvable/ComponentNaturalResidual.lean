module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentNaturalSix
public import Theory.Representation.BinaryPermutation.SixNaturalPoint

/-!
# Reciprocal residuals for both ordinary A₆ module cases

In the fixed-free case, splitting projects the original fixed-line generator
to a nonzero point of the selected natural module, with the same centralizer
in K. Its order 24 |O₂(K)| gives three-rank at most one. The actual L₁ lies
in this centralizer, so the original augmentation quotient is ordinary A₆.
The point centralizer is a {2,3}-group, allowing passage from O^{3′} to O².
The full order-four central seed identifies C_K(Ω₁Z(T)) with this same
point centralizer, retaining every ambient inclusion map.

The final theorem combines this result with the checked nonsplit branch.
It constructs ChosenModule and the module marking on the actual moved orbit,
its equality with [R₂(KT),K], the ordinary original quotient, full central
seed, and the reciprocal residual identities. No fixed-space alternative,
minimality callback or selected-module marking remains as an input.
The selected ordinary quotient is still the branch hypothesis.

The earlier module and structural inputs retain their existing producers
qt-d-1222-modules, qt-d-1222-source and qt-d-1332-source; final discharge
belongs to qt-d-1341-fixed-core-source. The remaining selected rows,
comparison, commutator and graph arguments stay with
qt-d-1341-nonsolvable-source. Both escaping weights still require their
own nonsolvability input, and the independent LargeDistanceInput remains
in the other branches. This does not complete the source contradiction.
Source: Aschbacher–Smith 13.4.10(2–5), printed pp.908–909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V U : Subgroup G}

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
theorem component_four_seed_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hzd : m.constant.val ∉ zpowers z := by
    intro hd
    exact hdK ((zpowers_le.mpr (show z ∈ centralizer (K : Set G) from
      fun k hk => mem_centralizer_singleton_iff.mp (hKz hk))) hd)
  have hZgen := four_seed_generated _ hcard hzT
    (m.constant_mem_central_four h structural).2 hzcard hzd
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr
      (m.constant_mem_central_four h structural).2))
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
theorem ordinary_original_of_fixedFree_six_component
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  obtain ⟨DK,q,e,he,_,_,hZ,hcard⟩ := ordinary_six_component_marking h₀ h structural modules
    D m h1332 hindex z hzT hzL hK.1 hHN hKM hfK eK hfixed
  obtain ⟨w,hw,hCw⟩ := component_fixed_generator_point h₀ h structural m hzT hz1 hK.1 hTK hKM
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
  have hrec := component_reciprocal_residual_of_ordinary_six h₀ h structural m hzT hz1
    hK hHN hqK eK eL
  refine ⟨⟨eL⟩,hLK,by omega,hZ,hcard,hrec,?_⟩
  rw [component_four_seed_centralizer h structural D m hzT hz1 hK.1 hKM hcard,
    twoResidual_eq_primeToResidual_three h23,←Solvable.firstCentralizerResidual_eq,hrec]
  exact (core_component_point_twoResidual D m eL z hzL).symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- Original 13.4.10(2--5) in the ordinary selected A₆ row, with both possible
fixed-space cases assembled on the same literal moved orbit. -/
theorem ordinary_six_component_geometry
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U,
      Nonempty (ComponentModuleAt DK z.val) ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
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
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  by_cases hfixed : U ⊓ centralizer (K : Set G) = ⊥
  · obtain ⟨DK,_,_,_,hUR,mark,hZ,hcard⟩ := ordinary_six_component_marking
      h₀ h structural modules D m h1332 hindex z hzT hzL hK.1 hHN hKM hfK eK hfixed
    obtain ⟨hL,hLK,hr,_,_,hrec,hres⟩ := ordinary_original_of_fixedFree_six_component
      h₀ h structural modules D m h1332 hindex z hzT hzL hK hHN hKM hfK eK hfixed
    exact ⟨DK,mark,hUR,hL,hLK,hr,hZ,hcard,hrec,hres⟩
  · obtain ⟨DK,_,_,hUR,mark,hZ,hcard⟩ := component_core_marking_of_source_fixed
      h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
    obtain ⟨hL,hLK,hr,_,hres⟩ := ordinary_original_of_nonsplit_ordinary_component
      h₀ h structural m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK hfixed
    obtain ⟨eL⟩ := hL
    have hrec := component_reciprocal_residual_of_ordinary_six h₀ h structural m hzT hz1
      hK hHN (component_quotient_quasisimple h1332 hfK) eK eL
    exact ⟨DK,mark,hUR,⟨eL⟩,hLK,hr,hZ,hcard,hrec,hres⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

