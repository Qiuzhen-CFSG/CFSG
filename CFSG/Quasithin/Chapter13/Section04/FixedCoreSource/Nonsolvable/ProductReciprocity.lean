module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.WeightFourClosure
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ProductMixed
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedReciprocity
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.EscapingUniqueness

/-!
# Product reciprocity and the original two reciprocal exclusions

The weight-four weak closure has normalizer in M. For an outside cubic
parabolic P and its invariant four-group U₀ containing C_V(L), the kernel
C_P(U₀) is a two-group: it lies in P∩M=T, using the literal index three.
Thus some original conjugate A=Vˣ≤T moves U₀. Its action fixes C_V(L), so
it has order at most two. The rank-three bound makes U₀ normalize A;
normalized index two then gives [U₀,A]=C_V(L)≤A. Original fusion and the
weight-four intersection theorem force A=V, contradicting [V,U₀]=1.

Apply this to the actual fixed-line orbit constructed in ProductMixed.
The already-proved reciprocal reduction supplies [V,V₀]=1, so the product
case of 13.4.16 is excluded. The final theorem selects and recognizes the
original escaping component and constructs its pair. It discharges unique
escape from universal escaping nonsolvability and proves both 13.4.15 and
13.4.16 for the same pair in both amalgam alternatives.

All original earlier-source premises remain explicit, including the two
distinct amalgam inputs, original 13.3.8/16 and covered module clause,
universal Structural1222, same-T modules and independent LargeDistanceInput.
The coset graph with both vertex types, 13.4.17 and the final nonsolvable
contradiction remain to be proved; reciprocal commutation alone is not that
contradiction. Source: Aschbacher–Smith 13.4.16, printed pp.912–913,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The fixed-line plane in an outside cubic parabolic cannot centralize V
in the weight-four branch. -/
theorem weight_four_fixed_plane_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hweight : m.weight z = 4)
    (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (hout : ¬ P ≤ normalizer (L : Set G))
    (U : Subgroup G) (hU : Nat.card U = 4)
    (hPU : P ≤ normalizer (U : Set G))
    (hFU : V ⊓ centralizer (L : Set G) ≤ U)
    (hVU : ⁅V,U⁆ = ⊥) : False := by
  let F := V ⊓ centralizer (L : Set G)
  let M := normalizer (L : Set G)
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hPM : P ⊓ M ≤ (T : Subgroup G) := by
    have hTQ : (T : Subgroup G) ≤ P ⊓ M := le_inf hTP hTM
    have hi : (T : Subgroup G).relIndex P = 3 :=
      SymmetricThreeTwoCore.sylow_index_three eP (T.subtype hTP)
    have hh := relIndex_mul_relIndex (T : Subgroup G) (P ⊓ M) P hTQ inf_le_left
    rw [hi] at hh
    rcases Nat.prime_mul_iff.mp (hh ▸ Nat.prime_three) with ⟨_,h1⟩ | ⟨_,h1⟩
    · exact (hout ((relIndex_eq_one.mp h1).trans inf_le_right)).elim
    · exact relIndex_eq_one.mp h1
  have hCT : P ⊓ centralizer (U : Set G) ≤ (T : Subgroup G) := by
    apply le_trans (inf_le_inf_left P (centralizer_le hFU))
    exact (inf_le_inf_left P (fixed_centralizer_eq_normalizer h structural D m).le).trans hPM
  have hCQ : P ⊓ centralizer (U : Set G) ≤ P.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes (T.isPGroup'.to_le hCT) inf_le_left
    exact (le_inf P.le_normalizer (hPU.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨_,_,hWN⟩ := weight_four_weakClosure_control h structural D m z hz1 hzT hzout
    hunique hfusion hweight
  have hWnot : ¬ ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (U : Set G) := by
    intro hc
    have hWQ : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ P.pCoreIn 2 :=
      (le_inf ((ChapterE.indexedWeakClosure_le _ _ _).trans hTP) hc).trans hCQ
    have he : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 =
        ChapterE.indexedWeakClosure V (P.pCoreIn 2) 0 :=
      SubgroupFamily.span_eq_in_p_overgroup (ChapterE.conjugateCorankFamily_invariant V 0)
        T (P.pCoreIn 2) (isPGroup_pCoreIn 2 P) hWQ
    have hn : P ≤ normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) := by
      rw [he]
      exact (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))).trans
        (ChapterE.normalizer_le_weakClosure_normalizer _ _ _)
    exact hout (hn.trans hWN)
  obtain ⟨x,hxT,hxC⟩ : ∃ x : G, V.conjBy x ≤ (T : Subgroup G) ∧
      ¬ V.conjBy x ≤ centralizer (U : Set G) := by
    by_contra! hn
    apply hWnot
    rw [ChapterE.weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro A hA
    obtain ⟨x,rfl,hx⟩ := (ChapterE.mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
    exact hn x hx
  let A := V.conjBy x
  have hAN : A ≤ normalizer (U : Set G) := hxT.trans (hTP.trans hPU)
  have hTF : (T : Subgroup G) ≤ centralizer (F : Set G) :=
    hTM.trans (normalizer_component_le_fixed_centralizer h structural D m)
  let f := U.normalizerMonoidHom.comp (inclusion hAN)
  let d : U := ⟨m.constant.val,hFU ⟨m.constant.property,m.constant_fixed⟩⟩
  have hd1 : d ≠ 1 := fun he => m.constant_ne_one (Subtype.ext (congrArg (fun a : U => a.val) he))
  have hfix : ∀ a ∈ f.range, a d = d := by
    rintro _ ⟨a,rfl⟩
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp (hTF (hxT a.property)) m.constant.val
        ⟨m.constant.property,m.constant_fixed⟩).symm
  have hfcard := card_mulAut_subgroup_le_two_of_fixed_point hU d hd1 f.range hfix
  have hker : f.ker = (centralizer (U : Set G)).subgroupOf A := by
    ext a
    change U.normalizerMonoidHom (inclusion hAN a) = 1 ↔ _
    change inclusion hAN a ∈ U.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hidx : (centralizer (U : Set G)).relIndex A ≤ 2 := by
    rw [←index_ker,hker] at hfcard
    exact hfcard
  have hcor : ChapterE.subgroupCorank A (A ⊓ centralizer (U : Set G)) ≤ 1 := by
    rw [ChapterE.subgroupCorank,inf_relIndex_left]
    exact (Nat.log_mono_right hidx).trans (by decide)
  have hr := m.three_le_globalR_of_unique_escape h structural z hz1 hzT hzout hunique
  have hrA : 3 ≤ ChapterE.globalR A := by
    change 3 ≤ ChapterE.globalR (V.map (MulAut.conj x).toMonoidHom)
    rwa [ChapterE.globalR_map_equiv]
  have hUA : U ≤ normalizer (A : Set G) := by
    apply (le_centralizer_iff.mpr (show A ⊓ centralizer (U : Set G) ≤
      centralizer (U : Set G) from inf_le_right)).trans
    apply ChapterE.centralizer_le_normalizer_of_corank_lt_globalR inf_le_left
    exact lt_of_lt_of_le (by exact_mod_cast (show ChapterE.subgroupCorank A
      (A ⊓ centralizer (U : Set G)) < 3 by omega)) hrA
  have hFi : F.relIndex U = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) F U bot_le hFU
    rw [relIndex_bot_left,relIndex_bot_left,m.card_fixed,hU] at hh
    omega
  have hEF : ⁅U,A⁆ ≤ F := commutator_le_of_normalized_index_two U F A hFU hFi hAN
    ((hxT.trans hTF).trans (Subgroup.centralizer_le_normalizer _))
  have hEA : ⁅U,A⁆ ≤ A := le_normalizer_iff_commutator_le_right.mp hUA
  have hEne : ⁅U,A⁆ ≠ ⊥ := fun he => hxC
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  have hFE : F ≤ ⁅U,A⁆ := by
    have hh := (one_lt_card_iff_ne_bot _).mpr hEne
    exact (eq_of_le_of_card_ge hEF (by rw [m.card_fixed]; omega)).ge
  have hFA : F ≤ A := hFE.trans hEA
  have hxM : x ∈ M := by
    by_contra hx
    have hw := m.conjugate_intersection_weight_of_unique_escape h structural z hz1 hzT hzout
      hunique hfusion x hx m.constant m.constant_ne_one
      (hFA ⟨m.constant.property,m.constant_fixed⟩)
    rw [m.weight_constant,hweight] at hw
    omega
  have hAV : A = V := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_component_le_module h structural D m hxM)
  exact hxC (hAV.le.trans (commutator_eq_bot_iff_le_centralizer.mp hVU))

/-- Product case of original 13.4.16, using the actual fixed-line plane and
weak closure; the same conjugator satisfies both reciprocal containments. -/
theorem original_product_pair_reciprocal_commute
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (P B : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hTB : (T : Subgroup G) ≤ B)
    (hout : ¬ P ⊔ B ≤ normalizer (L : Set G))
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : P ≠ B)
    (hiP : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := P ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hcomm : ⁅(pResidual 2 P).map P.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      ((pResidual 2 P).map P.subtype).pCoreIn 2)
    (hBM : B ≤ normalizer (L : Set G))
    (hfixed : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) =
      V ⊓ centralizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hweight : m.weight z = 4)
    : let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (P ⊔ B)
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → U ≤ (B.pCoreIn 2).conjBy g →
      ⁅U,U.conjBy g⁆ = ⊥ := by
  dsimp only
  intro g h₁ h₂
  by_contra hmove
  obtain ⟨_,hVU,_⟩ := original_product_pair_reciprocal_reduction h₀ D m h structural
    hindexL P B hTP hTB hout eP eB hne hiP hiB hcentral hcomm hBM hfixed hfusion
    g h₁ h₂ hmove
  let F := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)
  let U₀ := conjugateSpanBy F P
  have hPout : ¬ P ≤ normalizer (L : Set G) := fun hp => hout (sup_le hp hBM)
  have hFcard : Nat.card F = 2 := by
    change Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) : Subgroup G) = 2
    rw [hfixed,m.card_fixed]
  have hzero : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G) ⊓
      centralizer (B : Set G) = ⊥ := by
    apply bot_unique
    intro a ha
    by_contra hn
    have ha1 : a ≠ 1 := hn
    have haF := hfixed.le ⟨ha.1.1,ha.2⟩
    apply hPout
    apply le_trans ?_ (fixed_generator_centralizer h structural D m haF ha1).le
    exact fun p hp => mem_centralizer_singleton_iff.mpr (ha.1.2 p hp)
  obtain ⟨_,_,hnU,hUcard⟩ := product_line_orbit h₀ D m P B hTP hTB eP eB hne
    hiP hiB hcentral hcomm hFcard hzero
  have hFU : V ⊓ centralizer (L : Set G) ≤ U₀ := by
    rw [←hfixed]
    exact le_conjugateSpanBy F P
  have hVU₀ : ⁅V,U₀⁆ = ⊥ := bot_unique
    ((commutator_mono le_rfl (conjugateSpanBy_mono inf_le_left le_sup_left)).trans hVU.le)
  exact weight_four_fixed_plane_impossible h structural D m z hz1 hzT hzout hunique
    hfusion hweight P hTP eP hPout U₀ hUcard (le_sup_left.trans hnU) hFU hVU₀

/-- Source 13.4.15–16 for the original selected pair. Universal escaping
nonsolvability supplies uniqueness; both genuine amalgam inputs are retained. -/
theorem escaping_original_reciprocity
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1347 : Solvable.PlaneAmalgamSource1347 D m)
    (hpair1347 : PairAmalgamSource1347 T)
    (h1338 : ∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G),
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        IsPPerfect 2 Y → Y ≤ normalizer (L : Set G) → IsPiGroup twoThreePrimes Y)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hnonsolvable : ∀ w : V,
      w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      w.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({w.val} : Set G)))
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧
      centralizer ({z.val} : Set G) ≤ normalizer (K : Set G) ∧
      (¬ K ≤ normalizer (L : Set G)) ∧
      (Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))) ∧
      ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
        Module.finrank (ZMod 2) W = 2 ∧
        (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
        ∃ P : Subgroup G,
          P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
          P ⋖ centralizer ({z.val} : Set G) ∧
          Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
          let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
          let X := P ⊔ B
          let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
          Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
          X ∈ Chapter1.HOver G (T : Set G) ∧
          X ⊓ normalizer (L : Set G) = B ∧
          X ⊓ centralizer ({z.val} : Set G) = P ∧
          (∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
            ⁅V,U.conjBy g⁆ = ⊥) ∧
          ((⁅(pResidual 2 P).map P.subtype,(pResidual 2 B).map B.subtype⁆ ≤
              ((pResidual 2 P).map P.subtype).pCoreIn 2 ∧
            m.weight z = 4 ∧ ⁅U,B.pCoreIn 2⁆ ≤ V ⊓ centralizer (L : Set G) ∧
            (∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → U ≤ (B.pCoreIn 2).conjBy g →
              ⁅U,U.conjBy g⁆ = ⊥)) ∨
            (Solvable.LinearAmalgamConclusion T X ∧
              (∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → U ≤ (B.pCoreIn 2).conjBy g →
                ⁅U,U.conjBy g⁆ = ⊥))) := by
  have hzL : z.val ∉ centralizer (L : Set G) := by
    intro hz
    exact hzout (fixed_generator_centralizer h structural D m ⟨z.property,hz⟩
      (fun he => hz1 (Subtype.ext he))).le
  have hnonsolv := hnonsolvable z hzT hzL hzout
  have hunique := (escaping_seed_uniqueness_and_rank hl h₀ h structural modules D m h1332
    fixed five covered h13316 hindex hM h1347 hpair1347 h1338 hnonsolvable
    z hz1 hzT hzout).2.2.1
  obtain ⟨K,hK,hfK,_,hHN,_,hKM,_⟩ := exists_escaping_component h₀ h structural m
    h1332 h1338 hzT (fun he => hz1 (Subtype.ext he)) hzout hnonsolv
  have model := selected_component_ordinary_or_linear hl h₀ h structural D m h1332
    fixed five covered h13316 hindex z hzT hzL hK hHN hKM hfK
  have hgeom : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      omegaOneCenterAmbient (T : Subgroup G) ≤ V := by
    rcases model with he | he <;> obtain ⟨eK⟩ := he
    · obtain ⟨_,_,hL,_,_,_,_,_,_,hZ,_⟩ := linear_component_geometry
        hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK.1 hHN hKM hfK eK
      exact ⟨hL,hZ.le.trans inf_le_left⟩
    · obtain ⟨_,_,_,hL,_,_,hZ,_⟩ := ordinary_six_component_geometry
        h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
      exact ⟨hL,hZ.le.trans inf_le_left⟩
  obtain ⟨⟨eL⟩,hZV⟩ := hgeom
  obtain ⟨W,hW,hTW,P,hP,hPH,⟨eP⟩,⟨eB⟩,_,hlocal,_,hchief,hiP,hiB,hfixed,hcentral⟩ :=
    small_component_original_pair hl h₀ h structural modules D m h1332 fixed hindex hM
      z hzT hzL hK hHN hKM hfK model
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  let X := P ⊔ B
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hTW
  have hBM : B ≤ normalizer (L : Set G) := by rw [hM]; exact inf_le_left
  have hne : P ≠ B := fun he => hP.1.2 (he ▸ hBM)
  have hout : ¬ X ≤ normalizer (L : Set G) := fun hx => hP.1.2 (le_sup_left.trans hx)
  have hBlocal : B ∈ Chapter1.HOver G (T : Set G) := by
    have hVB : V ≤ B.pCoreIn 2 := by
      let := D.elementary
      exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
        (D.le_sylow.trans hTB) (hBM.trans (normalizer_component_le_module h structural D m))
    refine ⟨?_,hTB⟩
    intro he
    have hv : V = ⊥ := bot_unique (he ▸ hVB)
    have hc := m.card_module
    rw [hv,card_bot] at hc
    omega
  have hcentral' :
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂) := by
    dsimp only
    intro hx
    obtain ⟨_,_,_,_,h₁,h₂,hr⟩ := hcentral X hx.1 le_sup_left le_sup_right
    exact ⟨h₁,h₂,Or.inl hr⟩
  have hfixedB : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) =
      V ⊓ centralizer (L : Set G) := by
    rw [←Amalgam.omega_fixed_twoResidual B hTB]
    exact hfixed
  have hc := h1347 W hW hTW P hP.1.1 hBlocal ⟨eP⟩ ⟨eB⟩ hne
    (Solvable.original_second_flag_residual_eq_inner D m W hTW)
    (Or.inr (fun s hs ht => le_trans (by decide : 2 ≤ 3) (hchief s hs ht))) hiP hiB hcentral'
  obtain ⟨hXM,hXH,_⟩ := hcentral X hlocal.1 le_sup_left le_sup_right
  refine ⟨K,hK,hfK,hHN,hKM,model,W,hW,hTW,P,hP,hPH,⟨eP⟩,⟨eB⟩,hlocal,hXM,hXH,?_⟩
  rcases hc.2 with hc | hc
  · refine ⟨original_product_pair_mixed_commute h₀ D m h structural hindex P B
      hP.1.1.2 hTB hout eP eB hne hiP hiB hcentral' hc hBM hfixedB hfusion,Or.inl ⟨hc,?_,?_,?_⟩⟩
    · exact original_product_weight_four h structural D m W hW hTW P hP z hzL hPH.le hc
    · rw [←hfixedB]
      exact original_product_radical_movement h₀ D m h structural hindex P B
        hP.1.1.2 hTB hout eP eB hne hiP hiB hcentral' hc
    · exact original_product_pair_reciprocal_commute h₀ D m h structural hindex P B
        hP.1.1.2 hTB hout eP eB hne hiP hiB hcentral' hc hBM hfixedB hfusion
        z hz1 hzT hzout hunique
        (original_product_weight_four h structural D m W hW hTW P hP z hzL hPH.le hc)
  · refine ⟨?_,Or.inr ⟨hc,?_⟩⟩
    · exact original_linear_pair_mixed_commute hl h₀ h structural modules D m
        hP.1.1.2 hTB eP eB hne hout hindex hiP hiB (hcentral' hlocal).2.2
        h1332 fixed five covered h13316 h1338 hc eL hM hZV W hW hTW rfl
        hfusion z hzT hzL hPH.le hnonsolv
    · obtain ⟨_,_,_,hr⟩ := original_linear_pair_module_nonFF h₀ h structural D m
        hP.1.1.2 hTB eP eB hne hout hindex hiP hiB (hcentral' hlocal).2.2 h1332 hc
      intro g h₁ h₂
      have hR : B.pCoreIn 2 ≤ X := (pCoreIn_le 2 B).trans le_sup_right
      exact hr g (h₁.trans hR) (h₂.trans (map_mono hR))


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
