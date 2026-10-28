module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentGeneration
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.OrdinaryRow
public import Theory.GroupTheory.CComponent.AlternatingResidual
public import Theory.Quasithin.CoprimeRank

/-!
# The reciprocal residuals in the nonsplit ordinary component branch

For the actual normal component K of C_G(z), an ordinary A₆ two-core
quotient and the local three-rank bound give K=O^{3′}(C_G(z)). In particular
K contains the original L₁=O^{3′}(C_L(z)). When the moved omega-orbit has
nonzero fixed space, its already proved augmentation marking and splitting
put the original fixed-line generator d in that same module. Escape makes d
nonfixed under K. Its literal point centralizer has S₃ two-core quotient,
so L₁ has three-rank one. The marked original L action then excludes 3.A₆.

The two ordinary residual identities identify O^{3′}(C_K(d)) with L₁ by
intersection in C_G(z) and N_G(L)=C_G(d). Both actual point centralizers
are {2,3}-groups, allowing passage to O². Since Ω₁Z(T)=⟨z,d⟩, the final
application proves the source equality O²(C_K(Ω₁Z(T)))=O²(C_L(z)),
with both residuals mapped through their original subgroup inclusions.

This proves the ordinary-A₆, nonsplit branch of the containment and
reciprocal-residual analysis. It assumes the quotient row, not its
recognition, and derives the whole-module marking internally from the
genuine earlier 13.3.2 clause. The A₅, covered-A₆ and doubled L₃(2)
exclusions, fixed-free markings, comparison and graph arguments remain
with qt-d-1341-nonsolvable-source. Earlier inputs retain their producers
qt-d-1222-source and qt-d-1332-source, and final discharge with
qt-d-1341-fixed-core-source. Nonsolvability must still be supplied
separately at both escaping weight choices in the final assembly.

Source: Aschbacher–Smith, 13.4.10(2–5), printed pp.907–909;
A.3.18 and 12.2.8 supply the actual cubic residual identity.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K V : Subgroup G}

/-- In the ordinary A₆ row the selected component is the actual cubic residual
of the entire involution centralizer, so it contains the original L₁. -/
theorem component_residual_of_ordinary_six
    (h₀ : Hypothesis1331 T L) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z} : Set G)))
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    (primeToResidual 3 (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype = K ∧
      Solvable.firstCentralizerResidual L z ≤ K := by
  let := hqK
  have hr : primeRank 3 (centralizer ({z} : Set G)) ≤ 2 :=
    (isQuasithin_iff_twoLocal.mp h₀.qtke.quasithin) _
      (isTwoLocal_involution_centralizer
        (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1))
      3 (by decide) (by decide)
  have he := hK.2.map_primeToResidual_three_eq_of_quotient_alternating
    hK.1 hHN (Or.inl rfl) eK hr
  refine ⟨he,?_⟩
  rw [Solvable.firstCentralizerResidual_eq,←he]
  exact embedded_primeToResidual_mono 3 inf_le_right

/-- The reciprocal point centralizers have the same literal residual when
both component quotients are ordinary A₆. -/
theorem component_reciprocal_residual_of_ordinary_six
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    (h.source_normalizer_sqtk structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have hresM : (primeToResidual 3 M).map M.subtype = L :=
    (h.source_normalizer_component structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).map_primeToResidual_three_eq_of_quotient_alternating
        L.le_normalizer le_rfl (Or.inl rfl) eL hrM
  have he := embedded_primeToResidual_intersection_of_le 3 H K (H ⊓ M) inf_le_left hresH
  have hi : K ⊓ (H ⊓ M) = K ⊓ M :=
    le_antisymm (inf_le_inf_left _ inf_le_right)
      (le_inf inf_le_left (le_inf (inf_le_left.trans hK.1) inf_le_right))
  rw [hi] at he
  have hd : centralizer ({m.constant.val} : Set G) = M :=
    fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))
  rw [Solvable.firstCentralizerResidual_eq,hd]
  exact he.symm.trans (Solvable.firstCentralizerResidual_eq_intersection_residual z hresM)

private theorem threeRank_le_one_of_symmetric_three_quotient
    (A : Type*) [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) : primeRank 3 A ≤ 1 := by
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 A) pCore_isPGroup,
    primeRank_congr 3 e]
  by_contra hn
  obtain ⟨E,_,hE⟩ := exists_elementary_nine_of_three_rank (by omega :
    2 ≤ primeRank 3 (Equiv.Perm (Fin 3)))
  have hd := E.card_subgroup_dvd_card
  rw [hE,Nat.card_perm,Nat.card_fin] at hd
  norm_num at hd

/-- A nonfixed point in an ordinary augmentation component bounds every
subgroup of its literal centralizer by three-rank one. -/
theorem core_component_point_threeRank_le_one
    {U : Subgroup G} (DK : ChosenModule T K U) (mK : CoreMarking DK)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (w : U) (hw : w.val ∉ centralizer (K : Set G)) :
    primeRank 3 (K ⊓ centralizer ({w.val} : Set G) : Subgroup G) ≤ 1 := by
  have hc : IsPGroup 2 (Section08.TransvectionRecognition.Component.ModelExtension.centralCore K) := by
    rw [Solvable.centralCore_eq_twoCore_of_ordinary eK]
    exact pCore_isPGroup
  obtain ⟨e⟩ := Solvable.component_centralizer_quotient DK mK hc w hw
  exact threeRank_le_one_of_symmetric_three_quotient _ e

private theorem twoThree_of_symmetric_three_quotient
    (A : Type*) [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) : IsPiGroup twoThreePrimes A := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  have hcard : Nat.card A = 6 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),
      Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin,hn]
    rfl
  rw [IsPiGroup_iff]
  intro p hp
  rw [hcard] at hp
  change p.val = 2 ∨ p.val = 3
  rcases p.property.dvd_mul.mp hp with hs | ht
  · rcases p.property.dvd_mul.mp (show p.val ∣ 2 * 3 from hs) with h2 | h3
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow ht) |>.resolve_left p.property.ne_one)

/-- On the original ordinary augmentation point centralizer, O² and O^{3′}
agree. This bridge retains the exact two-residual convention of 13.4.10. -/
theorem core_component_point_twoResidual
    {U : Subgroup G} (DK : ChosenModule T K U) (mK : CoreMarking DK)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (w : U) (hw : w.val ∉ centralizer (K : Set G)) :
    (pResidual 2 (K ⊓ centralizer ({w.val} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({w.val} : Set G)).subtype =
      Solvable.firstCentralizerResidual K w.val := by
  have hc : IsPGroup 2 (Section08.TransvectionRecognition.Component.ModelExtension.centralCore K) := by
    rw [Solvable.centralCore_eq_twoCore_of_ordinary eK]
    exact pCore_isPGroup
  obtain ⟨e⟩ := Solvable.component_centralizer_quotient DK mK hc w hw
  rw [twoResidual_eq_primeToResidual_three (twoThree_of_symmetric_three_quotient _ e)]
  exact (Solvable.firstCentralizerResidual_eq K w.val).symm

private theorem central_seed_generated
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

/-- The actual nonsplit orbit, not a separately chosen component module,
puts L₁ in a point centralizer of K and excludes the covered original L. -/
theorem ordinary_original_of_nonsplit_ordinary_component
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D)
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
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Solvable.firstCentralizerResidual L z.val ≤ K ∧
      primeRank 3 (Solvable.firstCentralizerResidual L z.val) = 1 ∧
      m.constant.val ∈ U ∧
      (pResidual 2 (K ⊓ centralizer
          (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Subgroup G)).map
          (K ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype =
        (pResidual 2 (L ⊓ centralizer ({z.val} : Set G) : Subgroup G)).map
          (L ⊓ centralizer ({z.val} : Set G)).subtype := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hqK := component_quotient_quasisimple h1332 hfK
  have hTK := (h1332 K hfK).1
  obtain ⟨_,hL₁K⟩ := component_residual_of_ordinary_six h₀ hzT hz1 hK hHN hqK eK
  obtain ⟨DK,⟨mK⟩,hfix,_,_,_,hZcard⟩ := component_core_marking_of_source_fixed
    h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have hzU : zpowers z.val ≤ U := hfix.symm ▸ inf_le_left
  have hsplit : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K = U := by
    have hh := component_seed_split h₀ hzT hz1 hK.1 hTK
    rw [component_full_fixed_line h structural z.val hz1 hzT hindex K hK.1 hKM,
      sup_eq_left.mpr hzU] at hh
    exact hh
  have hdU : m.constant.val ∈ U := hsplit ▸
    le_conjugateSpanBy _ _ (m.constant_mem_central_four h structural).2
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hzcard : Nat.card (zpowers z.val) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1
  have hzd : m.constant.val ∉ zpowers z.val := by
    intro hd
    exact hdK ((hfix.symm ▸ hd).2)
  have hZgen := central_seed_generated _ hZcard hzT
    (m.constant_mem_central_four h structural).2 hzcard hzd
  have hCKZ : K ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) =
      K ⊓ centralizer ({m.constant.val} : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr
        (m.constant_mem_central_four h structural).2))
    · intro k hk
      refine ⟨hk.1,?_⟩
      have hkz : zpowers z.val ≤ centralizer ({k} : Set G) := zpowers_le.mpr
        (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hK.1 hk.1)).symm)
      have hkd : zpowers m.constant.val ≤ centralizer ({k} : Set G) := zpowers_le.mpr
        (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hk.2).symm)
      have hc : omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer ({k} : Set G) := by
        rw [hZgen]
        exact sup_le hkz hkd
      exact fun a ha => mem_centralizer_singleton_iff.mp (hc ha)
  have hLC : Solvable.firstCentralizerResidual L z.val ≤
      K ⊓ centralizer ({m.constant.val} : Set G) := by
    refine le_inf hL₁K ?_
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (m.constant_fixed a ((Solvable.firstCentralizerResidual_le L z.val ha).1))
  have hr : primeRank 3 (Solvable.firstCentralizerResidual L z.val) ≤ 1 :=
    (_root_.primeRank_le_of_injective 3 (inclusion hLC) (inclusion_injective _)).trans
      (core_component_point_threeRank_le_one DK mK eK ⟨m.constant.val,hdU⟩ hdK)
  let := h.quasisimple
  have hordinary := Solvable.ordinary_of_firstCentralizerResidual_threeRank D m z hzL hr
  obtain ⟨_,hthree⟩ := Solvable.firstCentralizerResidual_order_of_marking D m z hzL
  have hrne : primeRank 3 (Solvable.firstCentralizerResidual L z.val) ≠ 0 :=
    fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hthree
  obtain ⟨eL⟩ := hordinary
  refine ⟨⟨eL⟩,hL₁K,by omega,hdU,?_⟩
  rw [hCKZ]
  exact (core_component_point_twoResidual DK mK eK ⟨m.constant.val,hdU⟩ hdK).trans
      ((component_reciprocal_residual_of_ordinary_six h₀ h structural m hzT hz1
        hK hHN hqK eK eL).trans (core_component_point_twoResidual D m eL z hzL).symm)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
