module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CentralFourAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentFullSixQuotientAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentLinearGeometryAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.ComponentRecognition
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.CosetGraph
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.EscapingUniqueness
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.OriginalResidualWeights
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.WeightTwoComponent
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.WeightTwoReturning
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentPoints
/-!
# The selected component after the weight-two graph argument: structure at the original group

The graph's fixed-line containment in the original parabolic residual puts
C_V(L) in the actual moved module of the selected component K. In the two
natural rows this supplies the required point conjugacies. In the remaining
five-dimensional row, identify the actual outside parabolics and obtain
weight four for the original fixed generator in the component core.

The same central four-group transfers unique escape to N_G(K): the
complementary point's centralizer lies inside both original local groups.
The fixed generator really escapes N_G(K), and its centralizer contains
the original nonsolvable L. Thus universal nonsolvability is proved for
reciprocal escapes; it is not inferred from just one arbitrary centralizer.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/WeightTwoComponent` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- Uniqueness transfers to the reciprocal normalizer on the same central
four-group. The complementary point has centralizer inside both local groups. -/
theorem reciprocal_omega_escape_unique_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) (hwz : m.weight z = 2)
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (hcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) ≤ 4)
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (K : Subgroup G) (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G)) :
    ∀ w : G, w ≠ 1 → w ∈ omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w} : Set G) ≤ normalizer (K : Set G) → w = m.constant.val := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hdT : m.constant.val ∈ Z := (m.constant_mem_central_four_at h structural).2
  let b : V := z * m.constant
  have hbT : b.val ∈ Z := Z.mul_mem hzT hdT
  have hbw : m.weight b = 4 := by
    change m.weight (z*m.constant) = 4
    rw [m.weight_mul_constant,hwz]
  have hbL : b.val ∉ centralizer (L : Set G) := by
    intro hf
    rcases (m.fixed_iff b).mp hf with he | he
    · rw [he,m.weight_one] at hbw
      contradiction
    · rw [he,m.weight_constant] at hbw
      contradiction
  have hb1 : b ≠ 1 := fun he => hbL (congrArg Subtype.val he ▸ one_mem _)
  have hbz : b ≠ z := by intro he; rw [he,hwz] at hbw; contradiction
  have hbM : centralizer ({b.val} : Set G) ≤ normalizer (L : Set G) := by
    by_contra he
    exact hbz (hunique b hb1 hbT he)
  have hbH : centralizer ({b.val} : Set G) ≤ centralizer ({z.val} : Set G) := by
    intro a ha
    have had : a ∈ centralizer ({m.constant.val} : Set G) := by
      rw [fixed_generator_centralizer_at h structural D m
        ⟨m.constant.property,m.constant_fixed⟩
        (fun he => m.constant_ne_one (Subtype.ext he))]
      exact hbM ha
    have hba : b.val ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp ha).symm
    have hda : m.constant.val ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp had).symm
    have hza : z.val ∈ centralizer ({a} : Set G) := by
      have hh := (centralizer ({a} : Set G)).mul_mem hba
        ((centralizer ({a} : Set G)).inv_mem hda)
      simpa only [b,coe_mul,mul_inv_cancel_right] using hh
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hza).symm
  intro w hw1 hwT hwout
  let v : V := ⟨w,hZV hwT⟩
  by_cases hvL : v.val ∈ centralizer (L : Set G)
  · rcases (m.fixed_iff v).mp hvL with he | he
    · exact (hw1 (congrArg Subtype.val he)).elim
    · exact congrArg Subtype.val he
  · rcases m.nonfixed_weight v hvL with hw | hw
    · have he : v = z := m.central_weight_injective Z hZV hcard hdT z v hzT hwT
        hzL (hw.trans hwz.symm)
      exfalso
      apply hwout
      have hew : w = z.val := congrArg Subtype.val he
      rw [hew]
      exact hHN
    · have he : v = b := m.central_weight_injective Z hZV hcard hdT b v hbT hwT
        hbL (hw.trans hbw.symm)
      exfalso
      apply hwout
      have hew : w = b.val := congrArg Subtype.val he
      rw [hew]
      exact hbH.trans hHN


/-- The graph constructs the component containing the fixed line. Its natural
rows supply point fusion; its core row supplies the reciprocal weight-four
escape, its uniqueness, and nonsolvability at every reciprocal escape. -/
theorem escaping_original_component_fixed_line_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
      let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      ∃ DK : ChosenModule T K U, Nonempty (ComponentModuleAt DK z.val) ∧
        V ⊓ centralizer (L : Set G) ≤ U ∧
        ((U ⊓ centralizer (K : Set G) = ⊥ ∧
          ∀ w ∈ U, w ≠ 1 → IsConj m.constant.val w) ∨
        (∃ mK : CoreMarking DK, ∃ hd : m.constant.val ∈ U,
          mK.weight ⟨m.constant.val,hd⟩ = 4 ∧
          (¬ centralizer ({m.constant.val} : Set G) ≤ normalizer (K : Set G)) ∧
          ∀ w : U, w ≠ 1 → w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
            ¬ centralizer ({w.val} : Set G) ≤ normalizer (K : Set G) →
              w.val = m.constant.val ∧ ¬ Group.IsSolvable (centralizer ({w.val} : Set G)))) := by
  obtain ⟨hw2,hr,hw,K,hK,hfK,hHN,hKM,model,W,hW,hTW,P,hP,hPH,eP,eB,
    hlocal,hXM,hXH,hmixed,hlin,hsecond,he,hcard,hF,hSoc,g,hg,hgout,hg₁,hg₂,hgc,hcomm⟩ :=
    escaping_original_graph_pair_at hl h₀ h structural modules D m h1332 fixed five covered
      h13316 hindex hM h1347 hpair1347 h1338 hfusion hnonsolvable z hz1 hzT hzout
  have hzL : z.val ∉ centralizer (L : Set G) := by
    intro hz
    exact hzout (fixed_generator_centralizer_at h structural D m ⟨z.property,hz⟩
      (fun he => hz1 (Subtype.ext he))).le
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨DK₀,⟨mark₀⟩,hfull,hZ,hZcard⟩ := selected_component_marking_and_seed_at
    hl h₀ h structural modules D m h1332 fixed five covered h13316 hindex
    z hzT hzL hK hHN hKM hfK
  have huni := (escaping_seed_uniqueness_and_rank_at hl h₀ h structural modules D m h1332
    fixed five covered h13316 hindex hM h1347 hpair1347 h1338 hnonsolvable
    z hz1 hzT hzout).2.2.1
  have hrecip := reciprocal_omega_escape_unique_at h structural D m z hzT hzL hw2
    (hZ.le.trans inf_le_left) hZcard.le huni K hHN
  refine ⟨K,hK,hfK,hHN,hKM,?_⟩
  by_cases hfix : U ⊓ centralizer (K : Set G) = ⊥
  · have hFU : V ⊓ centralizer (L : Set G) ≤ U :=
      (small_component_natural_residual_fixed_iff_at hl h₀ h structural modules D m h1332 fixed
        hindex hM z hzT hzL hK hHN hKM hfK model hfix P hP hPH.le).mp hF
    exact ⟨DK₀,⟨mark₀⟩,hFU,Or.inl ⟨hfix,component_points_of_fixed_line m DK₀ mark₀ hfix
      (hFU ⟨m.constant.property,m.constant_fixed⟩)⟩⟩
  · have heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) := by
      rcases model with hlin | hA
      · obtain ⟨eK⟩ := hlin
        obtain ⟨_,_,_,_,_,_,_,_,hzero,_⟩ := linear_component_geometry_at
          hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK.1 hHN hKM hfK eK
        exact (hfix hzero).elim
      · exact hA
    obtain ⟨eK⟩ := heK
    obtain ⟨DK,mK,hd,W',WK,hW',hWK,hT',hTK,P',hP',hP'H,hplane,hZU,htest,hfour,htwo⟩ :=
      ordinary_six_original_reciprocal_weight_detection_at h₀ h structural modules D m
        h1332 fixed hindex hM z hzT hzL hK hHN hKM hfK eK hfix
    obtain ⟨P₀,_,_,_,_,_,_,_,_,_,_,_,_,hunique⟩ :=
      ordinary_six_full_centralizer_parabolic_at h₀ h structural modules D m h1332 fixed
        hindex z hzT hzL hK hHN hKM hfK eK
    have hPP : P = P' := (hunique P hP hPH.le).trans (hunique P' hP' hP'H.le).symm
    have hd4 : mK.weight ⟨m.constant.val,hd⟩ = 4 := hfour.mp (hPP ▸ hF)
    have hFU : V ⊓ centralizer (L : Set G) ≤ U := by
      intro v hv
      rcases (m.fixed_iff ⟨v,hv.1⟩).mp hv.2 with hh | hh
      · have hv1 : v = 1 := congrArg Subtype.val hh
        rw [hv1]
        exact one_mem _
      · have hvd : v = m.constant.val := congrArg Subtype.val hh
        exact hvd.symm ▸ hd
    have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
    have hK12 := h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
      (component_quotient_quasisimple h1332 hfK)
    have hzK : z.val ∈ centralizer (K : Set G) := by
      intro k hk
      exact (hK.1 hk z.val (Set.mem_singleton _)).symm
    have hNK : centralizer ({z.val} : Set G) = normalizer (K : Set G) :=
      fixed_generator_centralizer_at hK12 structural DK mK ⟨hZU hzT,hzK⟩
        (fun he => hz1 (Subtype.ext he))
    have hLCd : L ≤ centralizer ({m.constant.val} : Set G) := by
      intro l hl
      exact mem_centralizer_singleton_iff.mpr (m.constant_fixed l hl)
    have hdout : ¬ centralizer ({m.constant.val} : Set G) ≤ normalizer (K : Set G) := by
      intro hh
      apply hzL
      intro l hl
      exact (hNK.symm.le (hh (hLCd hl)) z.val (Set.mem_singleton _)).symm
    have hdnon : ¬ Group.IsSolvable (centralizer ({m.constant.val} : Set G)) := by
      intro hs
      let := hs
      let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
        (f := inclusion hLCd) (inclusion_injective hLCd)
      let := h.quasisimple
      let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
      let : Nontrivial (L ⧸ pCore 2 L) :=
        (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
      exact Group.IsPerfect.not_isSolvable (L ⧸ pCore 2 L) inferInstance
    refine ⟨DK,⟨ComponentModuleAt.coreSix mK (hZU hzT)⟩,hFU,Or.inr ⟨mK,hd,hd4,hdout,?_⟩⟩
    intro w hw hwT hwout
    have heq := hrecip w.val (fun he => hw (Subtype.ext he)) hwT hwout
    exact ⟨heq,heq.symm ▸ hdnon⟩
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
