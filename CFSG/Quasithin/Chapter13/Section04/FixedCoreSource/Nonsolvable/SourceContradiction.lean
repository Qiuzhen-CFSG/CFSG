module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReciprocalSymmetry
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.TerminalActor
public import Theory.GroupTheory.Commutator.SimpleCoreAction
/-!
# The original nonsolvable fixed-core contradiction

Select and recognize the component of the actual escaping centralizer.
The two-type coset graph and source symmetry exclude its five-dimensional
row and give the natural component module with the original fixed line
and point orbit. The returning core conjugate acts as a transposition.
An even conjugator lifted from L puts a conjugate A of V in the original
T and gives a cubic commutator with the literal first residual inside K.
Perfectness and the simple two-core quotient give K=[K,A].

This actual normalized, moving actor feeds the rank-three offender
contradiction. Under Lean's left conjugation, its conjugator is l*g;
this is the source's gl in right-conjugation notation. All subgroup
inclusions, action kernels and component quotients retain their original
carriers. Universal nonsolvability at all escaping omega points and an
actual escaping point are both required.

Only the authorized earlier Chapter12/13.3, fusion and two distinct
amalgam inputs remain explicit. Source symmetry needs the earlier plane,
fusion and 13.3.8 clauses at both faithful core components; the guarded
13.3.2 module inputs already quantify over the same-T components. Their
producers are qt-d-1222-source, qt-d-1332-source, qt-d-13316-source and
qt-d-1341-fixed-core-source; the independent LargeDistanceInput retains
qt-e-ms-small-a6-exhaustion-large-distance. Final 13.4.1 recognition and
removal of 13.5's fixed-line hypothesis remain with their assembly owners.
Source: Aschbacher–Smith 13.4.10–17 and the final proof of 13.4.1,
printed pp.907–915, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- The nonsolvable branch of original 13.4.1: universal nonsolvability at
every escaping omega point, together with an actual escape, is impossible.
All source geometry is constructed; only genuine earlier-source inputs remain. -/
theorem false_of_universal_escaping_nonsolvable
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
    (h1347 : ∀ (A W : Subgroup G) (DA : ChosenModule T A W) (ma : CoreMarking DA),
      Hypothesis1331 T A → Solvable.PlaneAmalgamSource1347 DA ma)
    (hpair1347 : PairAmalgamSource1347 T)
    (h1338 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (A : Set G) : Set G),
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        IsPPerfect 2 Y → Y ≤ normalizer (A : Set G) → IsPiGroup twoThreePrimes Y)
    (hfusion : ∀ (A W : Subgroup G) (DA : ChosenModule T A W),
      CoreMarking DA → Hypothesis1331 T A →
      ∀ v : W, v ≠ 1 → ∀ w ∈ W, IsConj v.val w →
        ∃ n ∈ normalizer (W : Set G), MulAut.conj n v.val = w)
    (hnonsolvable : ∀ w : V,
      w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      w.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({w.val} : Set G)))
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) : False := by
  classical
  have hzL : z.val ∉ centralizer (L : Set G) := by
    intro hz
    exact hzout (fixed_generator_centralizer h structural D m ⟨z.property,hz⟩
      (fun he => hz1 (Subtype.ext he))).le
  obtain ⟨K,hK,hfK,hHN,hKM,DK,⟨mark⟩,hFU,hfixed,hpoints⟩ :=
    escaping_original_natural_component hl h₀ h structural modules D m h1332 fixed five
      covered h13316 hindex hM h1347 hpair1347 h1338 hfusion hnonsolvable z hz1 hzT hzout
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
      (h1347 L V D m h₀) hpair1347 (h1338 L h₀) (hfusion L V D m h₀)
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
    fixed five covered h13316 hindex hM (h1347 L V D m h₀) hpair1347 (h1338 L h₀)
    hnonsolvable z hz1 hzT hzout).2.2.1
  exact false_of_terminal_component_fixed_free h structural D m z hz1 hzT hzout hunique
    (hfusion L V D m h₀) (original_fixed_line_kernel h structural D m)
    K _ DK hpoints y hyK hyU hgen mark hfixed

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
