module

public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative.Defs
public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative.Rank
public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative.Sections
public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative.SourceStructure
public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative.ChiefConstruction

/-!
# The no-FF-module alternative with an outer two-group hypothesis

For finite G with F*(G) = O₂(G), quasisimple F*(G/O₂(G)), quotient two-rank
at most j > 0, and no faithful binary FF-modules for G/X with
O₂(G) ≤ X ≤ O∞(G), we prove the E.5.4 alternative under the additional
explicit hypothesis that (G/O₂(G))/F*(G/O₂(G)) is a two-group. Either J(P)
is normal in G, or O²(G) centralizes D = Ω₁(Z(Jⱼ(P))) and D is normal in G.

When J(P) is not normal and j is below the Sylow two-rank, the direct
structure argument selects an escaping maximum elementary subgroup A and
proves D ≤ E = Ω₁(Z(W)), with E normal and the sharp displacement bound.
The outer two-group hypothesis identifies the image of O²(G) with F*(G/O₂(G)).
The chief-section construction then proves O²(G) centralizes E: otherwise
it constructs a forbidden faithful FF-module of an actual quotient G/X.
Centralization passes to D, and the Sylow/residual product proves normality.
The degenerate-rank case has D = 1.

The separately named `noFF_alternative_of_outer_two_group` retains this extra
outer two-group hypothesis in its statement. The unrestricted numbered E.5.4
is not asserted here; the `SourceStructure` diagnostics remain applicable.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.5.4,
printed p.244 (PDF p.255).
-/

open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE.NoFFAlternative
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem twoCore_quotient_eq_bot : pCore 2 (G ⧸ pCore 2 G) = ⊥ := by
  let Q := pCore 2 G
  let π := QuotientGroup.mk' Q
  have hk : IsPGroup 2 π.ker := by
    change IsPGroup 2 (QuotientGroup.mk' Q).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hn : IsPGroup 2 ((pCore 2 (G ⧸ Q)).comap π) :=
    pCore_isPGroup.comap_of_ker_isPGroup π hk
  have hle : (pCore 2 (G ⧸ Q)).comap π ≤ Q := le_sSup ⟨inferInstance, hn⟩
  apply bot_unique
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q x
  exact (QuotientGroup.eq_one_iff g).mpr (hle hx)

/-- Characteristic two proves the actual E.5.1 centralizer bound once the
component alternative has been obtained. All top-subgroup transport is explicit. -/
public theorem top_weakClosureCentralizerBound (P A : Subgroup G)
    (hchar : generalizedFitting G = pCore 2 G)
    (hcase : ECaseComponent P A ⊤) : WeakClosureCentralizerBound P A ⊤ := by
  have hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
    rw [← hchar]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have ht : centralizer (pCore 2 (⊤ : Subgroup G) : Set (⊤ : Subgroup G)) ≤
      pCore 2 (⊤ : Subgroup G) := by
    intro x hx
    have hxG : (x : G) ∈ centralizer (pCore 2 G : Set G) := by
      intro y hy
      rw [← top_core_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact congrArg Subtype.val ((mem_centralizer_iff.mp hx) z hz)
    have hxQ : (x : G) ∈ (pCore 2 (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype := by
      rw [top_core_map]
      exact hc hxG
    obtain ⟨y, hy, he⟩ := hxQ
    exact (Subtype.ext he : y = x) ▸ hy
  let _ : Group.IsNilpotent (pCore 2 (⊤ : Subgroup G)) := pCore_isNilpotent
  exact Or.inr ⟨hcase, inf_le_right.trans (ht.trans
    (le_solvableRadical _ inferInstance inferInstance))⟩

/-- The exact no-FF assumption contradicts a section with nontrivial
quasisimple action and the sharp displacement bound. The faithful quotient,
its kernel interval and its offender are constructed, not assumed. -/
public theorem noFF_excludes_active_section (hno : HasNoFFQuotients G)
    (hL : IsQuasisimple (generalizedFitting (G ⧸ pCore 2 G)))
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (U W : Subrepresentation ρ)
    (hQ : pCore 2 G ≤ (actionHom (sectionRepresentation ρ U W)).ker)
    (hmove : ¬ (generalizedFitting (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) ≤
      (actionHom (sectionRepresentation ρ U W)).ker)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hne : ¬ A ≤ pCore 2 G)
    (hdisp : fixedCodim ρ A ≤ rank (A.map (QuotientGroup.mk' (pCore 2 G)))) : False := by
  let _ : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  obtain ⟨hQX, hXR, hfaith, hFF⟩ := faithful_ff_quotient_of_section (pCore 2 G)
    twoCore_quotient_eq_bot hL ρ U W hQ hmove A hne hdisp
  exact hno _ inferInstance hQX hXR _ (faithfulQuotient (sectionRepresentation ρ U W))
    hfaith hFF

open ChapterB Stellmacher

/-- The source-use E.5.4 alternative with the additional **outer two-group
hypothesis**: `(G/O₂(G))/F*(G/O₂(G))` is a two-group. Every other premise is a
source hypothesis, including the exact faithful binary FF-module exclusion.
The residual in the second alternative is O²(G), and both normality assertions
are in G. This does not assert the unrestricted numbered E.5.4. -/
public theorem noFF_alternative_of_outer_two_group (P : Sylow 2 G)
    (j : ℕ) (_hj : 0 < j)
    (hchar : generalizedFitting G = pCore 2 G)
    (hL : IsQuasisimple (generalizedFitting (G ⧸ pCore 2 G)))
    (hr : primeRank 2 (G ⧸ pCore 2 G) ≤ j)
    (hno : HasNoFFQuotients G)
    (houter : IsPGroup 2
      ((G ⧸ pCore 2 G) ⧸ generalizedFitting (G ⧸ pCore 2 G))) :
    (thompsonJ (P : Subgroup G) 0).Normal ∨
      (pResidual 2 G ≤ centralizer (higherThompsonCenter (P : Subgroup G) j : Set G) ∧
        (higherThompsonCenter (P : Subgroup G) j).Normal) := by
  by_cases hJ : (thompsonJ (P : Subgroup G) 0).Normal
  · exact Or.inl hJ
  right
  by_cases hdeg : twoRank (P : Subgroup G) ≤ j
  · exact residual_centralizes_and_normal_of_rank_le P j hdeg
  obtain ⟨A, hA, hAQ, hDE, hdisp⟩ :=
    SourceStructure.exists_escaping_with_center_and_displacement P j
      (Nat.lt_of_not_ge hdeg) hJ hchar hr
  let E := omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) ⊤ j)
  let _ : E.Normal := core_center_normal P j
  let _ : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian _
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have himage := (SourceStructure.residual_image_eq_iff_two_group_quotient hL).mpr houter
  have hCE : pResidual 2 G ≤ centralizer (E : Set G) :=
    residual_centralizes_of_noFF hL hno himage E A hAQ hdisp
  have hCD : pResidual 2 G ≤
      centralizer (higherThompsonCenter (P : Subgroup G) j : Set G) :=
    hCE.trans (centralizer_le hDE)
  exact ⟨hCD, higherThompsonCenter_normal_of_residual_centralizes P j hCD⟩

end CFSG.Quasithin.ChapterE.NoFFAlternative
