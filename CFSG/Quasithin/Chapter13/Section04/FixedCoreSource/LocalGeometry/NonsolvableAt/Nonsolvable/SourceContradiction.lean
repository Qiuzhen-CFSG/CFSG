module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.AugmentationOutsideAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentLinearGeometryAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSixGeometryAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.EscapingUniqueness
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.FixedLineKernel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.MixedReciprocity
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.ReciprocalSymmetry
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.TerminalActor
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.TerminalSource
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.WeightTwoReturning
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.SourceContradiction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReciprocalSymmetry
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.TerminalActor
public import Theory.GroupTheory.Commutator.SimpleCoreAction
/-!
# The original nonsolvable fixed-core contradiction: structure at the original group

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

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/SourceContradiction` proof for the local step.
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
/-- The nonsolvable branch of original 13.4.1: universal nonsolvability at
every escaping omega point, together with an actual escape, is impossible.
All source geometry is constructed; only genuine earlier-source inputs remain. -/
theorem false_of_universal_escaping_nonsolvable_at
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
    (h1347 : ∀ (A W : Subgroup G) (DA : ChosenModule T A W) (ma : CoreMarking DA),
      Hypothesis1331 T A → Solvable.PlaneAmalgamSource1347 DA ma)
    (hpair1347 : PairAmalgamSource1347 T)
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
    exact hzout (fixed_generator_centralizer_at h structural D m ⟨z.property,hz⟩
      (fun he => hz1 (Subtype.ext he))).le
  obtain ⟨K,hK,hfK,hHN,hKM,DK,⟨mark⟩,hFU,hfixed,hpoints⟩ :=
    escaping_original_natural_component_at hl h₀ h structural modules D m h1332 fixed five
      covered h13316 hindex hM h1347 hpair1347 hfusion hnonsolvable z hz1 hzT hzout
  have model := selected_component_ordinary_or_linear_at hl h₀ h structural D m h1332
    fixed five covered h13316 hindex z hzT hzL hK hHN hKM hfK
  have hdata : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Solvable.firstCentralizerResidual L z.val ≤ K := by
    rcases model with heK | heK <;> obtain ⟨eK⟩ := heK
    · obtain ⟨_,_,hL,hLK,_⟩ := linear_component_geometry_at hl h₀ h structural modules
        D m h1332 fixed hindex z hzT hzL hK.1 hHN hKM hfK eK
      exact ⟨hL,hLK⟩
    · obtain ⟨_,_,_,hL,hLK,_⟩ := ordinary_six_component_geometry_at h₀ h structural modules
        D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
      exact ⟨hL,hLK⟩
  obtain ⟨⟨eL⟩,hRK⟩ := hdata
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  obtain ⟨hw2,_,g,hg,hcomm,hzg,hgM⟩ := escaping_original_rank_one_return_at
    hl h₀ h structural modules D m h1332 fixed five covered h13316 hindex hM
      (h1347 L V D m h₀) hpair1347 (augmentation_outside_twoThree_at h structural D m) (hfusion L V D m h₀)
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
  obtain ⟨l,hlL,hAT,hcubic⟩ := core_transposition_cubic_actor_at h structural D m eL
    z hzT hzL A hAM hweights hmove
  let y := l*g
  have hAy : V.conjBy y = A.conjBy l := by rw [conjBy_conjBy]
  have hyT : V.conjBy y ≤ (T : Subgroup G) := hAy.symm ▸ hAT
  have hyK := hyT.trans DK.sylow_normalizes_component
  have hyU := hyT.trans ((structural K hK12).2.2 _ DK).1
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
  have hunique := (escaping_seed_uniqueness_and_rank_at hl h₀ h structural modules D m h1332
    fixed five covered h13316 hindex hM (h1347 L V D m h₀) hpair1347 (augmentation_outside_twoThree_at h structural D m)
    hnonsolvable z hz1 hzT hzout).2.2.1
  exact false_of_terminal_component_fixed_free_at h structural D m z hz1 hzT hzout hunique
    (hfusion L V D m h₀) (original_fixed_line_kernel_at h structural D m)
    K _ DK hpoints y hyK hyU hgen mark hfixed

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
