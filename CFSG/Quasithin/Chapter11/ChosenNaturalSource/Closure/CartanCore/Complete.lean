module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Complete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Frattini
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.NilpotentFullNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.ExceptionalCorank.Assembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.FixedComplete

/-!
# The original Cartan conclusions from preceding chosen-natural geometry

Clause 11.5.6(4) has an independent proof using only quasisimple quotient
components. Hence the already proved SL₃ closure argument can be applied
without assuming (3). In odd degree 11.1.2 gives K=L₁, so its abelianness
conclusion contradicts the independent 11.5.3(3) input. In even degree the
Suzuki argument proves (3); the symplectic branch uses the fixed-cover
Sylow-normalizer argument. This closes every original component, including
the nilpotent SL₂(5) extensions with arbitrary primary exponents.

The preceding geometry below contains only flag/action markings and the
11.1--11.4 conclusions. In particular no component action, Borel movement,
closure decomposition or field actor is an input. The independent
11.5.3(3) implication remains a separate argument. Its producer is
qt-d-1222-natural-closure-nonabelian. The final discharge of preceding
geometry stays with qt-d-1222-natural-closure and its existing flag,
relative-component and shadow-component producers.

The use of the established SL₃ branch changes the order of the book's
argument, not its statement. There is no circular appeal to (3): the
Frattini theorem used here is cartan_frattini_action_of_marked.
Source: Aschbacher--Smith 11.5.4--6, pp.780--781, with the independent
SL₃ closure argument of 11.5.7, pp.781--782, supplied by the completed
qt-d-1222-natural-closure-sl3 task.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open LocalGeometry LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Actual preceding source geometry. All core bounds here are the earlier
11.4.1 bounds; none is a conclusion about the chosen closure or the Y action. -/
structure CartanPrecedingGeometry where
  marking : Nonabelian.MarkedFlag E
  flag : E.ClosureFlag
  naturalSeed : ∀ hK : E.K = E.L₁, Nonempty (flag.NaturalSeed hK)
  cartan : IsCartan T L E.X
  cartan_le : E.X ≤ E.G₁
  cartan_normalizes_radical : E.X ≤ normalizer (E.R₁ : Set G)
  point_torus : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁
  local_center : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥
  local_three_rank : 1 ≤ primeRank 3 E.L₁
  local_model : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2
    (2 ^ E.input.field.degree)
  sylow_normalizer : normalizer (T : Set G) ≤ E.M
  component : Source.NormalComponentIn E.G₁ E.K
  refinement : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree
  no_triangle : ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X
  generation : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁
  point_control : centralizer (E.V₁ : Set G) ≤ E.M → E.G₁ ≤ E.M
  component_centralizes_point : E.K ≤ centralizer (E.V₁ : Set G)
  strict_escape : E.L₁ < E.K → ¬ E.K ≤ E.M
  strict_core : E.L₁ < E.K → ⁅E.R₁,E.X⁆ ≤ (E.K ⊔ (T : Subgroup G)).pCoreIn 2
  strict_radical : E.L₁ < E.K →
    E.R₁ ≤ (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)).map
      (E.K ⊔ (T : Subgroup G) : Subgroup G).subtype ∧
    (twoFittingCore (E.K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
      (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2

namespace CartanPrecedingGeometry
variable {E} (s : E.CartanPrecedingGeometry)
include s

/-- Every strict alternative has q=4, with all original alternatives retained. -/
theorem strict_degree_even (h : E.L₁ < E.K) : Even E.input.field.degree := by
  cases s.refinement with
  | equal he => exact (h.ne (by simpa using he)).elim
  | sl2 _ hn _ _ _ => rw [hn]; decide
  | psl2 _ hn _ _ _ _ _ => rw [hn]; decide
  | triangle _ hn _ => rw [hn]; decide

/-- The independent Frattini action, before making any assertion about
nonquasisimple C-components. -/
theorem frattini_action (P : Subgroup G) (hP : P ≤ T) (hPX : P = ⁅P,E.X⁆)
    (hphi : (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2) :
    ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2 :=
  E.cartan_frattini_action_of_marked s.flag.point_nonzero s.flag.sylow_normalizes_point
    s.cartan_le s.marking.action.coordinates s.cartan s.cartan_normalizes_radical
    s.point_torus s.local_center s.sylow_normalizer s.local_three_rank
    s.strict_degree_even P hP hPX hphi

/-- Source 11.5.6(5) from the unchanged preceding strict-component bound. -/
theorem core_commutator :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤ (E.K ⊔ (T : Subgroup G)).pCoreIn 2 :=
  E.core_commutator_le
    ((s.cartan.1.trans inf_le_left).trans
      (le_sup_left.trans (L ⊔ (T : Subgroup G)).le_normalizer)) s.strict_core

/-- The centralizer escape in 11.5.4, using the independently supplied
11.5.3(3) implication exactly in its K=L₁ branch. -/
theorem point_centralizer_escape
    (hnonabelian : E.K = E.L₁ → ¬ IsMulCommutative E.W) :
    ¬ centralizer (E.V₁ : Set G) ≤ E.M :=
  E.point_centralizer_not_le_M s.flag.point_nonzero
    (Preliminary.seed_ti D E.input) s.point_control s.component_centralizes_point
    s.strict_escape hnonabelian

/-- The source selects H; the original Geometry's arbitrary H is not assumed
to satisfy any outside or residual condition. -/
theorem exists_selected_H
    (hnonabelian : E.K = E.L₁ → ¬ IsMulCommutative E.W) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) E.M ∧ H ≤ E.G₁ ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (E.V₁ : Set G) ∧
      ((pResidual 2 H).map H.subtype ≤ E.K ∨
        ⁅E.K,(pResidual 2 H).map H.subtype⁆ ≤ E.K.pCoreIn 2) := by
  exact E.exists_residual_selected_H s.flag.point_nonzero s.flag.sylow_normalizes_point
    (s.point_centralizer_escape hnonabelian) s.component_centralizes_point s.generation

/-- The remaining odd-degree SL₃ configuration is impossible using the
already proved linear closure argument and the independent clause (4).
Only the original 11.5.3(3) implication is retained from the nonabelian owner. -/
theorem no_odd_linear
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (b : InvariantFlag (.sl3 m))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace (b.space 0))
    (hthree : E.threeSpace = (Coordinates.sl3 m).binarySubspace (b.space 2))
    (hodd : Odd E.input.field.degree)
    (hnonabelian : E.K = E.L₁ → ¬ IsMulCommutative E.W) : False := by
  have hK : E.K = E.L₁ := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd)
      (s.strict_degree_even (lt_of_le_of_ne (le_conjugateSpanBy E.L₁ E.G₁) (Ne.symm hne)))
  obtain ⟨H,hH,hHG,hpointH,hselect⟩ := s.exists_selected_H hnonabelian
  let E' : Geometry D := { E with H := H }
  let f' : E'.ClosureFlag := {
    point_nonzero := s.flag.point_nonzero
    point_le_seed := s.flag.point_le_seed
    point_ne_seed := s.flag.point_ne_seed
    sylow_normalizes_point := s.flag.sylow_normalizes_point
    local_normalizes_seed := s.flag.local_normalizes_seed
    seed_irreducible := s.flag.seed_irreducible }
  have hsum (hK' : E'.K = E'.L₁) : ∃ r : ℕ,
      Nonempty (ActionEquiv (Linear.Block.Multiplicity.action E' f' hK')
        (repeated (linearNatural E'.input.field 2) r)) := by
    let n := (s.naturalSeed hK').some
    let n' : f'.NaturalSeed hK' := {
      groupEquiv := n.groupEquiv
      linearEquiv := n.linearEquiv
      intertwines := n.intertwines }
    exact f'.globalClosure_natural_sum n'
  have hab : IsMulCommutative E'.W := Linear.isMulCommutative_of_source E' m b
    hpoint hthree f' s.cartan s.cartan_le s.component s.refinement s.no_triangle
    s.generation s.frattini_action s.core_commutator
    hsum hH hHG hpointH hselect s.sylow_normalizer
  exact hnonabelian hK hab

/-- Source 11.5.6(3), with no component-action or field-detection premise.
Both surviving marked natural families and both field parities are covered. -/
theorem component_commutator
    (hnonabelian : E.K = E.L₁ → ¬ IsMulCommutative E.W)
    (I : Subgroup G) (hI : Source.ComponentIn E.Y I) :
    ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2 := by
  rcases s.marking with ⟨a,b,hpoint,hplane,hthree⟩
  cases a with
  | sl3 m =>
      by_cases he : Even E.input.field.degree
      · exact (E.cartan_actions_of_even_marked s.flag.point_nonzero
          s.flag.sylow_normalizes_point s.cartan_le (.sl3 m) s.cartan
          s.cartan_normalizes_radical s.point_torus s.local_center s.sylow_normalizer he).1 I hI
      · exact (s.no_odd_linear m b hpoint hthree (Nat.not_even_iff_odd.mp he)
          hnonabelian).elim
  | sp4 m =>
      exact E.symplectic_component_commutator_of_marked s.flag.point_nonzero
        s.flag.sylow_normalizes_point s.cartan_le m s.cartan s.cartan_normalizes_radical
        s.point_torus s.local_center s.sylow_normalizer s.local_three_rank
        s.strict_degree_even hI

/-- All six clauses of 11.5.6, on the literal Y, residuals and quotient maps.
The last premise is O²(H₁)≤K, not O₂(H₁)≤K. -/
theorem source_cartan
    (hnonabelian : E.K = E.L₁ → ¬ IsMulCommutative E.W) :
    Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1) ∧
    (primeRank 3 E.Y ≤ 1 ∧ (Even E.input.field.degree → ¬ 3 ∣ Nat.card E.Y)) ∧
    (∀ I : Subgroup G, Source.ComponentIn E.Y I → ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) ∧
    (∀ P : Subgroup G, P ≤ T → P = ⁅P,E.X⁆ →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2) ∧
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤ (E.K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    (∀ H₁ : Subgroup G,
      H₁ ∈ Chapter1.HOutside G ((E.L₁ ⊔ (T : Subgroup G) : Subgroup G) : Set G)
        (E.M : Set G) → H₁ ≤ E.G₁ → (pResidual 2 H₁).map H₁.subtype ≤ E.K →
      ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ E.R₁ →
        ChapterE.subgroupCorank A (A ⊓ H₁.pCoreIn 2) ≤ 1) := by
  have hc := E.cartan_coprime_of_local_action s.flag.point_nonzero s.cartan_le s.cartan.odd
    (fun _ hp hd => (s.marking.action.coordinates.cartan_primeRank s.cartan hp hd).ge)
    s.point_torus s.local_center
  refine ⟨hc, ⟨E.three_rank_Y_le_one s.flag.point_nonzero hc s.strict_degree_even
    s.local_center s.local_three_rank, E.three_not_dvd_Y_of_even hc⟩,
    s.component_commutator hnonabelian, s.frattini_action, s.core_commutator, ?_⟩
  intro H₁ hH hHG hres A hA hAR
  let : IsElementaryAbelian 2 A := hA
  exact E.elementary_corank_le_one_of_source_geometry H₁ hH hHG hres
    s.local_model s.refinement (fun _ => s.no_triangle) s.strict_radical A hAR

/-- The chosen H₁ and every conclusion of 11.5.5. The final clause is a
marking of the actual closure action, constructed from the seed marking. -/
theorem selected_local_closure
    (hnonabelian : E.K = E.L₁ → ¬ IsMulCommutative E.W) :
    ∃ H₁ : Subgroup G,
      H₁ ∈ Chapter1.HOutside G ((E.L₁ ⊔ (T : Subgroup G) : Subgroup G) : Set G)
        (E.M : Set G) ∧
      ∃ (hH : H₁ ≤ E.G₁) (hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H₁),
        E.localClosure H₁ ≤ H₁.pCoreIn 2 ∧
        E.tilde (E.localClosure H₁) ≤
          (center ((E.tilde H₁).pCoreIn 2)).map ((E.tilde H₁).pCoreIn 2).subtype ∧
        (frattini (E.localClosure H₁)).map (E.localClosure H₁).subtype ≤ E.V₁ ∧
        (∀ hK : E.K = E.L₁, ∃ n : ℕ, Nonempty (ActionEquiv
          (s.flag.quotientAction H₁ hH hLH hK)
          (repeated (linearNatural E.input.field 2) n))) := by
  obtain ⟨H₁,hH,hHG⟩ := E.exists_local_overgroup s.flag.point_nonzero
    s.flag.sylow_normalizes_point
    (s.point_centralizer_escape hnonabelian)
  have hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H₁ := hH.1.2
  have hc := E.localClosure_core_and_frattini s.flag.point_nonzero
    s.flag.point_le_seed s.flag.point_ne_seed s.flag.sylow_normalizes_point
    s.flag.local_normalizes_seed s.flag.seed_irreducible H₁ hHG hLH
  exact ⟨H₁,hH,hHG,hLH,hc.1,
    E.localClosure_central_quotient s.flag.point_nonzero s.flag.point_le_seed
      s.flag.point_ne_seed s.flag.sylow_normalizes_point s.flag.local_normalizes_seed
      s.flag.seed_irreducible H₁ hHG hLH, hc.2.2.1,
    fun hK => s.flag.localClosure_natural_sum H₁ hHG hLH (s.naturalSeed hK).some⟩

end CartanPrecedingGeometry
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
