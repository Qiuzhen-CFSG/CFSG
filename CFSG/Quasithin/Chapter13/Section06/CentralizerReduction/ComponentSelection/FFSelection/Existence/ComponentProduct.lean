module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.Setup
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.Lifting

/-!
# Component selection from the central Fitting subgroup of J(G_v)*

The paragraph after 13.6.13 asserts that J(G_v)* is a product of components.
The cited B.5.1(1i) / B.5.6 alternatives include outer symmetric actors;
F(J) = Z(J) alone does not make such an actor perfect. In particular S₅
has F(S₅) = Z(S₅) = 1 and layer A₅. This observation concerns the reduced
inference, not a counterexample to the full local hypotheses on printed p.929.
We do not assert that stronger product equality here.

For the required selection there is a direct sufficient argument which also
retains the outer cases. Set N = J(G_v)* and A = J(T_v)*. The literal Thompson
span identity gives 1 ≠ A ≤ N, and Sylow containment makes A a two-group.
Normality of N and O₂(G_v*) = 1 give O₂(N) = 1. If A centralized every
component of N, then F(N) = Z(N) would make A centralize F*(N). The proved
self-centralization theorem says its intersection with a two-subgroup is
trivial, a contradiction. Components of the normal subgroup N are ambient
components. C.1.16(1) normalizes the selected component, so the component
commutator dichotomy yields [E,A] = E.

The final theorem applies the existing lifting construction and has exactly
the Y_z witness conclusion of `exists_mem_Yz_of_component_product`. Its
Fitting-center premise is still explicit, with independent producer
`qt-13-06-existence-fitting-center`; the parent `qt-13-06-ff-existence`
retains its discharge and the earlier universal A.3.8/A.3.9/C.1.16 inputs.
No B.5 classification or offender/Thompson identification is needed for this
conditional selection branch. Setup is imported directly to avoid an assembly
cycle; the existing Existence and Lifting interfaces are preserved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the paragraph
following 13.6.13, printed p.929 (PDF p.946); B.5.1(1i), printed p.99;
B.5.6, printed p.105. Generalized-Fitting self-centralization is the checked
Gorenstein–Walter proof already exposed by ChapterB.QuasisimpleSections.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A nontrivial two-subgroup in a normal subgroup with central Fitting
subgroup moves a component there. Ambient normalization turns movement into
commutator generation. -/
private theorem select_component (N A : Subgroup G) [N.Normal]
    (hF : fittingSubgroup N = center N) (hcore : pCore 2 G = ⊥)
    (hAN : A ≤ N) (hA : IsPGroup 2 A) (hne : A ≠ ⊥)
    (hnorm : ∀ E : Subgroup G, IsComponent G E → A ≤ normalizer (E : Set G)) :
    ∃ E : Subgroup G, IsComponent G E ∧ E ≤ N ∧ ⁅E, A⁆ = E := by
  classical
  have hcomponent (C : Subgroup N) (hC : IsComponent N C) :
      IsComponent G (C.map N.subtype) := by
    let := hC.2
    exact ⟨hC.1.trans' (inferInstance : N.Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (C.equivMapOfInjective N.subtype N.subtype_injective)⟩
  have hex : ∃ C : Subgroup N, IsComponent N C ∧ ⁅C.map N.subtype, A⁆ ≠ ⊥ := by
    by_contra hf
    have hc : A.subgroupOf N ≤ centralizer (componentLayer N : Set N) := by
      apply le_centralizer_iff.mpr
      apply sSup_le
      intro C hC c hc
      apply mem_centralizer_iff.mpr
      intro a ha
      have hzero : ⁅C.map N.subtype, A⁆ = ⊥ := by
        by_contra h
        exact hf ⟨C, hC, h⟩
      have hcomm := mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hzero (mem_map_of_mem N.subtype hc))
          (a : G) ha
      exact Subtype.ext hcomm
    have hfit : A.subgroupOf N ≤ centralizer (fittingSubgroup N : Set N) := by
      rw [hF]
      intro a _ c hc
      exact (mem_center_iff.mp hc a).symm
    have hcent : A.subgroupOf N ≤ centralizer (generalizedFitting N : Set N) := by
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp hfit) (le_centralizer_iff.mp hc)
    have hcoreN : pCore 2 N = ⊥ := by
      rw [pCore_subnormal_eq_comap 2 (inferInstance : N.Normal).isSubnormal, hcore]
      exact N.ker_subtype
    have hbot := (ChapterB.QuasisimpleSections.disjoint_centralizer_fitting hcoreN
      (A.subgroupOf N) hA.comap_subtype).eq_bot_of_le hcent
    apply hne
    simpa only [map_subgroupOf_eq_of_le hAN, Subgroup.map_bot] using
      congrArg (Subgroup.map N.subtype) hbot
  obtain ⟨C, hC, hCA⟩ := hex
  have hE := hcomponent C hC
  refine ⟨C.map N.subtype, hE, map_subtype_le C, ?_⟩
  rcases hE.commutator_dichotomy A with hb | he
  · exact (hCA hb).elim
  · exact le_antisymm (le_normalizer_iff_commutator_le_left.mp (hnorm _ hE))
      ((le_iSup_conjugates _ A).trans he.symm.le)


/-- A sufficient replacement for the component-product step after 13.6.13:
select an actual ambient component inside J(G_v)* generated by its commutators
with J(T_v)*. Only the independently produced Fitting equality remains explicit. -/
theorem exists_component_of_JGstar_fitting_eq_center
    (hC116 : SourceC116One.{u}) (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hF : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (hJne : JGstar z v ≠ ⊥)
    (hfit : fittingSubgroup (JGstar z v) = center (JGstar z v)) :
    ∃ E : Subgroup (Gstar z v), IsComponent (Gstar z v) E ∧ E ≤ JGstar z v ∧
      ⁅E, starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ = E := by
  let A := starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))
  have hspan : JGstar z v = conjugateSpanBy A ⊤ := JGstar_eq_conjugateSpan T z v hSyl
  have hAN : A ≤ JGstar z v := hspan ▸ le_conjugateSpanBy A ⊤
  have hAne : A ≠ ⊥ := by
    intro hbot
    apply hJne
    apply le_antisymm _ bot_le
    rw [hspan]
    exact conjugateSpanBy_le hbot.le (by rw [normalizer_eq_top])
  have hAp : IsPGroup 2 A := by
    obtain ⟨S, hS⟩ := hSyl
    have he := starImage_intrinsic_thompson z v (S : Subgroup (Gv v)) (Tv T v) hS
    change IsPGroup 2 (starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v)))
    rw [← he]
    have hle : Stellmacher.elementaryAbelianMaxJ (S : Subgroup (Gv v)) ≤
        (S : Subgroup (Gv v)) := sSup_le fun _ h => h.1
    exact (S.isPGroup'.of_injective (inclusion hle) (inclusion_injective hle)).map (starMk z v)
  let := JGstar_normal z v
  exact select_component (JGstar z v) A hfit hstarCore hAN hAp hAne
    (thompsonStar_normalizes_components hC116 T z v hz hF hSyl hstarCore)


/-- Apply the direct selection to the existing source lifting theorem. This
has the same witness and every Y_z clause as the component-product consumer,
with F(J(G_v)*) = Z(J(G_v)*) in place of the stronger product premise. The full
earlier-source implications retain exactly their original quantifiers. -/
theorem exists_mem_Yz_of_JGstar_fitting_eq_center {𝒦 : GroupClass.{u}}
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel B)
    (hC116 : SourceC116One.{u})
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hcore : Gv v ∈ Chapter1.H G)
    (hF : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (hJne : JGstar z v ≠ ⊥)
    (hfit : fittingSubgroup (JGstar z v) = center (JGstar z v)) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (Gv v) ∧
      IsComponent (Gstar z v) (starImage z v K) ∧
      ⁅starImage z v K, starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        starImage z v K ∧ K ∈ Yz L T z v := by
  obtain ⟨E, hE, _, hcomm⟩ := exists_component_of_JGstar_fitting_eq_center
    hC116 T z v hz hF hSyl hstarCore hJne hfit
  obtain ⟨K, hK, hKE, hY⟩ := exists_mem_Yz_of_moved_component hA39 hA38
    L T z v hlocal hcore hSyl hstarCore E hE hcomm
  refine ⟨K, hK, ?_, ?_, hY⟩
  · rwa [hKE]
  · rwa [hKE]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
