module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryFusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FixedModuleAssembly

/-!
# Ordinary recognition with normalizer fusion constructed

Apply the ordinary fusion theorem at the initial component and at the
actual reciprocal five-dimensional component, whose ordinary quotient
and source hypotheses are already constructed. This removes the universal
fusion callback without claiming fusion for unrelated covered components.

Under negated symplectic recognition, every escaping omega centralizer
is nonsolvable. The original escaping point and the reciprocal-core
contradiction then feed the completed nonsolvable terminal argument.
The final theorem starts from the original nonzero fixed part and
constructs its marking and omega index. The normalizer supplement,
ordinary quotient and earlier Chapter 12/13.3 and natural large-distance
inputs remain explicit; full 13.4.1 and the covered row remain to assemble.

Source: Aschbacher--Smith 13.4.1--3, 13.4.7--17,
printed pp.896--915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The reciprocal core exclusion with ordinary residual and fusion clauses proved at both cores. -/
theorem natural_component_of_ordinary_fusion_sources
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
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
        U ⊓ centralizer (K : Set G) = ⊥ ∧
        ∀ w ∈ U, w ≠ 1 → IsConj m.constant.val w := by
  have hplane := Amalgam.planeAmalgamSource1347 hl h₀ h structural modules D m h1332
    fixed covered h13316 hindex hM
  have hpair1347 := Amalgam.pairAmalgamSource1347 h₀ h structural D m h1332
    fixed covered h13316 hindex
  obtain ⟨K,hK,hfK,hHN,hKM,DK,mark,hFU,halt⟩ :=
    escaping_original_component_fixed_line hl h₀ h structural modules D m h1332
      fixed five covered h13316 hindex hM hplane hpair1347
      (ordinary_outside_twoThree h structural D eL hM) (fun v _ => ordinary_core_normalizer_fusion hl h₀ h structural D m earlier eL v) hnonsolvable z hz1 hzT hzout
  refine ⟨K,hK,hfK,hHN,hKM,DK,mark,hFU,?_⟩
  rcases halt with hnat | ⟨mK,hd,hd4,hdout,hrecip⟩
  · exact hnat
  · exfalso
    have hzL : z.val ∉ centralizer (L : Set G) := by
      intro hz
      exact hzout (fixed_generator_centralizer h structural D m ⟨z.property,hz⟩
        (fun he => hz1 (Subtype.ext he))).le
    obtain ⟨eK⟩ := ordinary_component_of_source_fixed h₀ h structural D m h1332 fixed
      hindex z hzT hzL hK hHN hKM hfK mK.fixed_ne_bot
    obtain ⟨hK₀,hK12,hiK,hNK⟩ := reciprocal_core_source_setup h₀ h structural modules
      D m h1332 fixed hindex hM z hzT hzL hK hHN hKM hfK DK mK
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    let d : U := ⟨m.constant.val,hd⟩
    have hd1 : d ≠ 1 := fun he => m.constant_ne_one (Subtype.ext (congrArg (fun w : U => w.val) he))
    have hdT := (m.constant_mem_central_four h structural).2
    have hnonsolvK : ∀ w : U,
        w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
        w.val ∉ centralizer (K : Set G) →
        ¬ centralizer ({w.val} : Set G) ≤ normalizer (K : Set G) →
        ¬ Group.IsSolvable (centralizer ({w.val} : Set G)) := by
      intro w hwT hwK hwout
      have hw1 : w ≠ 1 := fun he => hwK (he ▸ one_mem _)
      exact (hrecip w hw1 hwT hwout).2
    have hw2 := (escaping_original_graph_pair hl hK₀ hK12 structural modules DK mK h1332
      (fun _ => fixed h₀) (fun _ => five h₀) (fun _ => covered h₀)
      h13316 hiK hNK (Amalgam.planeAmalgamSource1347 hl hK₀ hK12 structural modules DK mK h1332
        (fun _ => fixed h₀) (fun _ => covered h₀) h13316 hiK hNK) hpair1347
      (ordinary_outside_twoThree hK12 structural DK eK hNK) (fun v _ => ordinary_core_normalizer_fusion hl hK₀ hK12 structural DK mK earlier eK v) hnonsolvK d hd1 hdT hdout).1
    change mK.weight d = 4 at hd4
    omega

/-- The ordinary nonsolvable contradiction with its full normalizer fusion constructed. -/
theorem false_of_ordinary_nonsolvable_fusion_sources
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
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hnonsolvable : ∀ w : V,
      w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      w.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({w.val} : Set G)))
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) : False := by
  classical
  have hplane := Amalgam.planeAmalgamSource1347 hl h₀ h structural modules D m h1332
    fixed covered h13316 hindex hM
  have hpair1347 := Amalgam.pairAmalgamSource1347 h₀ h structural D m h1332
    fixed covered h13316 hindex
  have hzL : z.val ∉ centralizer (L : Set G) := by
    intro hz
    exact hzout (fixed_generator_centralizer h structural D m ⟨z.property,hz⟩
      (fun he => hz1 (Subtype.ext he))).le
  obtain ⟨K,hK,hfK,hHN,hKM,DK,⟨mark⟩,hFU,hfixed,hpoints⟩ :=
    natural_component_of_ordinary_fusion_sources hl h₀ h structural modules D m h1332 fixed five
      covered h13316 hindex hM eL earlier hnonsolvable z hz1 hzT hzout
  have model := selected_component_ordinary_or_linear hl h₀ h structural D m h1332
    fixed five covered h13316 hindex z hzT hzL hK hHN hKM hfK
  have hdata : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Solvable.firstCentralizerResidual L z.val ≤ K := by
    rcases model with heK | heK <;> obtain ⟨eK⟩ := heK
    · obtain ⟨_,_,hL,hLK,_⟩ := linear_component_geometry hl h₀ h structural modules
        D m h1332 fixed hindex z hzT hzL hK.1 hHN hKM hfK eK
      exact ⟨hL,hLK⟩
    · obtain ⟨_,_,_,hL,hLK,_⟩ := ordinary_six_component_geometry h₀ h structural modules
        D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
      exact ⟨hL,hLK⟩
  obtain ⟨⟨eL⟩,hRK⟩ := hdata
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  obtain ⟨hw2,_,g,hg,hcomm,hzg,hgM⟩ := escaping_original_rank_one_return
    hl h₀ h structural modules D m h1332 fixed five covered h13316 hindex hM
      hplane hpair1347 (ordinary_outside_twoThree h structural D eL hM) (fun v _ => ordinary_core_normalizer_fusion hl h₀ h structural D m earlier eL v)
      hnonsolvable z hz1 hzT hzout
  let := D.elementary
  let A := V.conjBy g
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hzorder : orderOf z.val = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z.val z.property)
    (fun he => hz1 (Subtype.ext he))
  have hweights : ∀ v : V, v.val ∈ ⁅V,A⁆ → v ≠ 1 → m.weight v = 2 := by
    intro v hv hv1
    rw [hcomm,mem_zpowers_iff_mem_range_orderOf,hzorder] at hv
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hv
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact (hv1 (Subtype.ext (by simpa using he.symm))).elim
    · have hvz : v = z := Subtype.ext (by simpa using he.symm)
      rwa [hvz]
  have hmove : ⁅V,A⁆ ≠ ⊥ := by
    rw [hcomm]
    intro he
    have hh := he ▸ mem_zpowers z.val
    exact hz1 (Subtype.ext (mem_bot.mp hh))
  have hAM : A ≤ L ⊔ (T : Subgroup G) := hM ▸ hgM
  obtain ⟨l,hlL,hAT,hcubic⟩ := core_transposition_cubic_actor h structural D m eL
    z hzT hzL A hAM hweights hmove
  let y := l*g
  have hAy : V.conjBy y = A.conjBy l := by rw [conjBy_conjBy]
  have hyT : V.conjBy y ≤ (T : Subgroup G) := hAy.symm ▸ hAT
  have hyK := hyT.trans DK.sylow_normalizes_component
  have hyU := hyT.trans ((structural G T K hK12).2.2 _ DK).1
  let : Group.IsPerfect (K.subgroupOf (K ⊔ (T : Subgroup G))) := hfK.1.1.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).surjective
  let : IsSimpleGroup (K ⧸ pCore 2 K) := by
    rcases model with heK | heK <;> obtain ⟨eK⟩ := heK
    · let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
      let : IsSimpleGroup BinaryLinearThree.Group := Matrix.PSL3Two.equiv.isSimpleGroup
      exact eK.isSimpleGroup
    · let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact eK.isSimpleGroup
  have hgen : ⁅K,V.conjBy y⁆ = K := commutator_eq_of_perfect_simple_core K _ hyK (by
    intro hc
    rw [hAy] at hc
    exact hcubic ((isPGroup_pCoreIn 2 K).to_le ((commutator_mono hRK le_rfl).trans hc)))
  have hunique := (escaping_seed_uniqueness_and_rank hl h₀ h structural modules D m h1332
    fixed five covered h13316 hindex hM hplane hpair1347 (ordinary_outside_twoThree h structural D eL hM)
    hnonsolvable z hz1 hzT hzout).2.2.1
  exact false_of_terminal_component_fixed_free h structural D m z hz1 hzT hzout hunique
    (fun v _ => ordinary_core_normalizer_fusion hl h₀ h structural D m earlier eL v) (original_fixed_line_kernel h structural D m)
    K _ DK hpoints y hyK hyU hgen mark hfixed

/-- Combine both ordinary branches with fusion and 13.3.8 proved at the actual cores. -/
theorem ordinary_recognition_of_fusion_sources
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
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    ClassicalGroup.IsPSp G 3 2 := by
  classical
  by_contra hnot
  obtain ⟨z,hz1,hzT,_,hzout⟩ := exists_nonfixed_omega_escape h₀ h structural D m earlier
  have hnonsolv := ordinary_universal_escaping_nonsolvable h₀ h structural D m eL
    (fun v _ => ordinary_core_normalizer_fusion hl h₀ h structural D m earlier eL v) hindex h1332 modules fixed covered h13316 hl hM hnot
  exact false_of_ordinary_nonsolvable_fusion_sources hl h₀ h structural modules D m
    h1332 fixed five covered h13316 hindex hM eL earlier hnonsolv z hz1 hzT hzout

/-- Start from the original nonzero fixed part, constructing its marking, omega index and fusion. -/
theorem ordinary_recognition_of_fixed_module_fusion_sources
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    ClassicalGroup.IsPSp G 3 2 := by
  obtain ⟨m⟩ := coreMarking_of_original_fixed h₀ h D fixed hfixed
  exact ordinary_recognition_of_fusion_sources hl h₀ h structural modules D m h1332 fixed five
    covered h13316 (original_omega_fixed_index h₀ h structural D m earlier) hM eL earlier

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
