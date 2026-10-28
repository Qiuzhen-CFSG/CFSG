module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Assembly.Distance
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Assembly.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.SelectedSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Source
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.NonbinaryApplication

/-!
# The three nonbinary natural rows from preceding source implications

The component and shadow theorem constructs the selected outside H, proves
K(V,z)=K(V,V₁), removes both orientations of the field-four triangle, and
eliminates G₂ with its literal R₁-Sylow witness. The original marked flag
then supplies the classical closure setup. The global parameter is computed
on the same V. To obtain 11.2.5 without an extra SL₃ plane-centralizer premise,
assume the closure abelian: the amalgam gives K=L₁, and the intersection-rank
bound supplies that centralizer containment. The distance-two closure proof
now contradicts 11.5.3. Its own later H-reselection remains inside N_G(V₁),
with O²(H) centralizing V₁, rather than being attributed to the shadow step.

The final application uses LiteralComparison's full-cover recovery on the
original D.space fixed-space quotient. It retains full SL₃, rank-two Sp₄,
the concrete G₂ action, hmany, FF and the unchanged-seed source branch.
No projective actor is substituted for the full SL₃ marking.

This is a conditional assembly, not unconditional 11.0.1. The local input
specification has no fixed-space vanishing, component equality, generation
one, closure conclusion or contradiction field. Its existence remains with
qt-d-1222-natural-local-geometry and qt-d-1222-natural-shadow-reduction;
normalized 7.0.1 retains its earlier producer and Chapter12 assembly owner.
The universally quantified 11.2.2 and 11.3.2 inputs cover the reselected
component as well as the original one, so neither triangle orientation is lost.

The source-specific closure argument now proves distance two internally;
neither an external distance witness nor C.1.32 recognition is needed.
The odd-extension Fitting-index input is still used by the existing corank
proof. The triangle producer's canonical radical theorem bypassed, and did
not prove, that stronger index assertion. The closure owner must prove the
needed bound or replace this corank route; a completed triangle task does
not discharge it. The prime-PSL₂ index is proved internally here. This
conditional three-branch implication belongs to qt-d-1222-nonbinary-natural;
under the 27 October task split, qt-d-1222-modules and qt-d-1222-source
retain final discharge of all preceding geometry and source implications.

Source: Aschbacher--Smith, refs/quasithin.pdf, 11.1.2, 11.2.5,
11.4.1--11.5.8 and 12.2.2, printed pp.761--764,770,775--784,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V}

private theorem degree_two_of_triangle (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (K X : Subgroup G)
    (ht : Components.FieldFourTriangle T L (f.Li 0) (f.Li 1) K X) :
    S.field.degree = 2 := by
  obtain ⟨_, K₀, _, _, _, _, _, _, _, ho⟩ := ht
  have ho' : Components.TriangleOrientation (K₀ ⊔ f.Li 1) L :=
    ho.elim (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)
  have hc := Triangle.Reselection.Classification.orientation_order ho'
  have hb : Nat.card (L ⧸ pCore 2 L) ≤ 251596800 := by
    rcases hc with h | h <;> omega
  cases c with
  | sl3 m =>
    rw [Nat.card_congr m.groupEquiv.toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear, S.field.card_eq] at hb
    have hn : S.field.degree ≤ 3 := by
      by_contra hn
      have hp : 16 ≤ 2 ^ S.field.degree :=
        Nat.pow_le_pow_right (show 0 < 2 by decide) (show 4 ≤ S.field.degree by omega)
      have hh : 16^3 * (16^3-1) * (16^2-1) ≤
          (2^S.field.degree)^3 * ((2^S.field.degree)^3-1) *
            ((2^S.field.degree)^2-1) := by gcongr
      omega
    rw [Triangle.Reselection.Classification.FieldFourOrder,
      Nat.card_congr m.groupEquiv.toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear, S.field.card_eq] at hc
    have := S.nonbinary
    interval_cases S.field.degree <;> norm_num at hc
  | sp4 m =>
    rw [Nat.card_congr m.groupEquiv.toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp, S.field.card_eq] at hb
    have hn : S.field.degree ≤ 2 := by
      by_contra hn
      have hp : 8 ≤ 2 ^ S.field.degree :=
        Nat.pow_le_pow_right (show 0 < 2 by decide) (show 3 ≤ S.field.degree by omega)
      have hh : 8^4 * (8^2-1) * (8^4-1) ≤
          (2^S.field.degree)^4 * ((2^S.field.degree)^2-1) *
            ((2^S.field.degree)^4-1) := by gcongr
      omega
    have := S.nonbinary
    omega
  | g2 m =>
    rw [Nat.card_congr m.groupEquiv.toEquiv, Atlas.G2.card_Model, S.field.card_eq] at hb
    have hn : S.field.degree ≤ 2 := by
      by_contra hn
      have hp : 8 ≤ 2 ^ S.field.degree :=
        Nat.pow_le_pow_right (show 0 < 2 by decide) (show 3 ≤ S.field.degree by omega)
      have hh : 8^6 * (8^6-1) * (8^2-1) ≤
          (2^S.field.degree)^6 * ((2^S.field.degree)^6-1) *
            ((2^S.field.degree)^2-1) := by gcongr
      omega
    have := S.nonbinary
    omega

/-- Earlier local hypotheses on one original flag. This specification has no
existence assertion and contains no shadow endgame or closure conclusion. -/
structure NonbinaryNaturalLocalInputs (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G) (z : G) where
  earlier : Comparison.EarlierGeometry (ofFlag S f X z ⊥)
  sylow_normalizer : normalizer (T : Set G) ≤ normalizer (L : Set G)
  linear_fixed : Chapter11.Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
    V ⊓ centralizer (L : Set G) = ⊥
  radical_centralizes_point : f.Vi 0 ≤ centralizer (f.Ri 0 : Set G)
  cartan_point : f.Vi 0 = ⁅zpowers z, X⁆
  cartan : IsCartan T L X
  cartan_normalizes_point : X ≤ normalizer (f.Vi 0 : Set G)
  cartan_normalizes_radical : X ≤ normalizer (f.Ri 0 : Set G)
  component_centralizes_omega : (ofFlag S f X z ⊥).K ≤ centralizer
    (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G)
  refinement : Components.RefinementAlternative T L (f.Li 0) (f.Li 1)
    (ofFlag S f X z ⊥).K X 0 S.field.degree
  radical_normalizer : Chapter11.Source.RadicalNormalizerAlternative
    (T : Subgroup G) V (f.Vi 0) (f.Ri 0) (normalizer (L : Set G)) L S.field.degree
  odd_kernel : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V)
  maximal_unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
    L ≤ N → N = normalizer (L : Set G)
  three_centralizer : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G)
  fixed_line : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)
  second_component : Chapter11.Source.UniqueNoncentralComponent
    (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1)
  flag_action : (ofFlag S f X z ⊥).ClosureFlag
  natural_seed : ∀ he : (ofFlag S f X z ⊥).K = (ofFlag S f X z ⊥).L₁,
    Nonempty (flag_action.NaturalSeed he)
  point_torus : X ⊓ centralizer (f.Vi 0 : Set G) ≤ f.Li 0
  local_center : center (f.Li 0 ⧸ pCore 2 (f.Li 0)) = ⊥
  local_three_rank : 1 ≤ primeRank 3 (f.Li 0)
  local_model : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree)
  point_split : L ⊓ normalizer (f.Vi 0 : Set G) = (f.Li 0 ⊔ L.pCoreIn 2) ⊔ X
  first_component : Chapter11.Source.ComponentIn
    (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G)) (f.Li 0)
  plane_sylow : Sylow 2 (f.Li 1)
  plane_fixed : f.Vi 0 = f.Vi 1 ⊓ centralizer
    ((plane_sylow : Subgroup (f.Li 1)).map (f.Li 1).subtype : Set G)
  plane_radical : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G)
  linear_movement : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
    ⁅V,f.Ri 1⁆ ≤ f.Vi 1
  /-- Still required by the closure corank route, not supplied by the canonical
  shadow radical theorem. Only its odd-extension branch is requested. -/
  fitting_index : ∀ p : ℕ, S.field.degree = 2 → (p = 5 ∨ (p.Prime ∧ 11 ≤ p)) →
    Chapter11.Source.IsSL (Chapter11.Source.TwoOddQuotient (ofFlag S f X z ⊥).K) 2 p →
    (twoFittingCore ((ofFlag S f X z ⊥).K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
      (solvableRadical ((ofFlag S f X z ⊥).K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2

open Closure in
private theorem radicalCorank_of_preceding (E : Closure.Geometry D)
    (s : E.CartanPrecedingGeometry) (hlt : E.L₁ < E.K) :
    Amalgam.OddGeometry.RadicalCorank E := by
  let J : Subgroup G := E.K ⊔ (T : Subgroup G)
  have hJG : J ≤ E.G₁ := sup_le E.K_le_G₁ s.flag.sylow_normalizes_point
  have hJK : J ≤ normalizer (E.K : Set G) := hJG.trans E.G₁_normalizes_K
  let : (E.K.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJK
  have hsup : E.K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show E.K ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hp := isPGroup_quotient_of_sup_eq_top (E.K.subgroupOf J)
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype hsup
  have hr : (pResidual 2 J).map J.subtype ≤ E.K := by
    have hle : pResidual 2 J ≤ E.K.subgroupOf J := sInf_le ⟨inferInstance, hp⟩
    simpa only [map_subgroupOf_eq_of_le (show E.K ≤ J from le_sup_left)] using
      (show (pResidual 2 J).map J.subtype ≤ (E.K.subgroupOf J).map J.subtype from
        map_mono hle)
  have hpointJ : E.V₁ ≤ J := E.V₁_le.trans (D.le_sylow.trans le_sup_right)
  have hpCore : E.V₁ ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (@IsElementaryAbelian.isPGroup 2 _ _ (D.centralQuotientPreimage_elementary E.point))
      hpointJ hJG
  have hJH : J ∈ Chapter1.H G := by
    intro hz
    exact D.centralQuotientPreimage_ne_bot E.point s.flag.point_nonzero
      (bot_unique (hz ▸ hpCore))
  have hout : ¬ J ≤ E.M := fun h => s.strict_escape hlt (le_sup_left.trans h)
  have hH : J ∈ Chapter1.HOutside G
      ((E.L₁ ⊔ (T : Subgroup G) : Subgroup G) : Set G) (E.M : Set G) :=
    ⟨⟨hJH, sup_le_sup_right (le_conjugateSpanBy E.L₁ E.G₁) _⟩, hout⟩
  intro A hA hAR
  let : IsElementaryAbelian 2 A := hA
  exact E.elementary_corank_le_one_of_source_geometry J hH hJG hr
    s.local_model s.refinement (fun _ => s.no_triangle) s.strict_radical A hAR

open Closure in
private theorem component_eq_of_abelian {E : Closure.Geometry D}
    (s : E.CartanPrecedingGeometry) (e : EndgameAt E)
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hLi : Chapter11.Source.ComponentIn E.M₁ E.L₁)
    (hs : @ChapterE.globalS G _ V D.elementary = (E.input.field.degree : ℕ∞))
    (hab : IsMulCommutative E.W) : E.K = E.L₁ := by
  obtain ⟨a,f,hp,hpl,ht⟩ := s.marking
  cases a with
  | sl3 m =>
    let F₀ : Nonabelian.MarkedFlag E := ⟨.sl3 m,f,hp,hpl,ht⟩
    exact Amalgam.linear_eq_of_abelian E m f ⟨hp.symm,hpl.symm,ht.symm⟩
      ((le_conjugateSpanBy E.L₁ E.G₁).trans s.component_centralizes_point)
      hsplit s.cartan (s.point_torus.trans le_sup_left) hLi s.component s.local_model
      e.refinement e.fixed_trivial (radicalCorank_of_preceding E s)
      (Nonabelian.PointModels.pointResidual_eq F₀ e.fixed_trivial e.point_mem e.point_ne_one)
      e.comparison (F₀.point_orbit e.fixed_trivial e.point_mem e.point_ne_one e.transitive)
      e.transitive hs hab
  | sp4 a =>
    let m : Symplectic.MarkedFlag E := ⟨a,f,hp,hpl,ht⟩
    let F₀ : Nonabelian.MarkedFlag E := ⟨.sp4 a,f,hp,hpl,ht⟩
    exact Amalgam.symplectic_eq_of_abelian E m (Sp4.alignment m.action)⁻¹
      (by simpa only [inv_inv] using m.point_coordinates) m.plane_membership m.three_membership
      ((le_conjugateSpanBy E.L₁ E.G₁).trans s.component_centralizes_point)
      hsplit s.cartan (s.point_torus.trans le_sup_left) hLi s.component s.local_model
      e.refinement e.fixed_trivial (radicalCorank_of_preceding E s)
      (Nonabelian.PointModels.pointResidual_eq F₀ e.fixed_trivial e.point_mem e.point_ne_one)
      e.comparison (F₀.point_orbit e.fixed_trivial e.point_mem e.point_ne_one e.transitive)
      e.transitive hs hab

/-- The remaining shortness witness on the literal product L O₂(N_G(V₁)).
This does not assert that an arbitrary positive even distance equals two. -/
@[expose] def NonbinaryNaturalDistanceTwo (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) : Prop :=
  Normalizers.PointBlocks.NonbinaryMSPair
    S.field L ((normalizer (f.Vi 0 : Set G)).pCoreIn 2) →
    ∃ d : ChapterC.BinaryMS.MS93.CharacteristicReduction
      (L.subgroupOf (L ⊔ (normalizer (f.Vi 0 : Set G)).pCoreIn 2))
      (((normalizer (f.Vi 0 : Set G)).pCoreIn 2).subgroupOf
        (L ⊔ (normalizer (f.Vi 0 : Set G)).pCoreIn 2)),
      ∃ graph : ChapterC.BinaryMS.MS93.Geometry d.radical, graph.b d.radical = 2

variable (S : D.NonbinaryNaturalInput)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {c : Coordinates D S.field} (f : InvariantFlag c) (X : Subgroup G) (z : G)
    (a : NonbinaryNaturalLocalInputs S f X z)
    (h701 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent)
    (h1132 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput) (c_J : Coordinates D_J S_J.field)
      (f_J : InvariantFlag c_J) JH,
      Hypothesis1131At D_J S_J (c_J.binarySubspace (f_J.space 0)) JH →
      Proposition1132At D_J S_J (c_J.binarySubspace (f_J.space 0)) JH)
    (h1122 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput),
      Nonempty (ActionEquiv D_J.centralQuotientAction (binaryG2 S_J.field)) →
      ChapterE.indexedWeakClosure W (T : Subgroup G) 0 ≤
          (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
        @ChapterE.globalS G _ W D_J.elementary = (2 * S_J.field.degree : ℕ) ∧
        (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W)

include hmany a h701 h1132 h1122 in
/-- Assemble all three original markings from explicit earlier inputs. The
selected endgame, weak-closure obstruction and all terminal closure premises
are constructed in the proof. In particular the symplectic critical distance
is proved internally, without an external shortness or recognition premise. -/
theorem nonbinary_impossible_of_preceding_geometry_of_many : False := by
  obtain ⟨_, J, e, hrad, hcomm⟩ := ofFlag_source_endgame S f X z ⊥ a.earlier
    a.sylow_normalizer a.linear_fixed a.radical_centralizes_point a.cartan_point
    a.cartan_normalizes_point a.cartan_normalizes_radical a.component_centralizes_omega
    h701 h1132 h1122 a.refinement a.radical_normalizer a.odd_kernel
    a.maximal_unique a.three_centralizer a.fixed_line a.second_component
  let E := ofFlag S f X z J
  let flag : E.ClosureFlag := {
    point_nonzero := a.flag_action.point_nonzero
    point_le_seed := a.flag_action.point_le_seed
    point_ne_seed := a.flag_action.point_ne_seed
    sylow_normalizes_point := a.flag_action.sylow_normalizes_point
    local_normalizes_seed := a.flag_action.local_normalizes_seed
    seed_irreducible := a.flag_action.seed_irreducible }
  have htriangle : ¬ Components.FieldFourTriangle T L E.L₁ E.L₂ E.K X := by
    intro ht
    have hd := degree_two_of_triangle S f E.K X ht
    exact Triangle.Reselection.no_fieldFourTriangle_of_preceding_sources D S f hd E.K X
      e.line_component a.component_centralizes_omega h701
      (fun _ _ D_J hJ => D_J.source325_of_many hJ hmany) h1132 h1122 ht
  have hindex (hlt : E.L₁ < E.K) :
      (twoFittingCore (E.K ⊔ (T : Subgroup G) : Subgroup G)).relIndex
        (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)) ≤ 2 := by
    cases e.refinement with
    | equal he => exact (hlt.ne he).elim
    | sl2Prime _ hn p hp hm => exact a.fitting_index p hn hp hm
    | psl2Prime _ _ p hp hl hm _ =>
      let : Fact p.Prime := ⟨hp⟩
      let : Group.IsPerfect E.K := Radical.relative_component_perfect e.line_component.1
      exact (Radical.fitting_index_one_of_psl2 T E.K
        ((f.invariant 0).trans E.G₁_normalizes_K) (by omega) hm).le.trans (by decide)
  let s : E.CartanPrecedingGeometry := {
    marking := e.marked_flag.some
    flag := flag
    naturalSeed := fun he => by
      obtain ⟨n⟩ := a.natural_seed he
      exact ⟨⟨n.groupEquiv,n.linearEquiv,n.intertwines⟩⟩
    cartan := a.cartan
    cartan_le := a.cartan_normalizes_point
    cartan_normalizes_radical := a.cartan_normalizes_radical
    point_torus := a.point_torus
    local_center := a.local_center
    local_three_rank := a.local_three_rank
    local_model := a.local_model
    sylow_normalizer := a.sylow_normalizer
    component := e.line_component
    refinement := a.refinement
    no_triangle := htriangle
    generation := by
      intro g hg
      obtain ⟨k,hk,y,hy,m,hm,rfl⟩ := e.line_product g hg
      exact mul_mem (mul_mem ((show E.K ≤ (E.K ⊔ E.Y) ⊔ E.M₁ from
        le_sup_left.trans le_sup_left) hk)
        ((show E.Y ≤ (E.K ⊔ E.Y) ⊔ E.M₁ from le_sup_right.trans le_sup_left) hy))
        ((show E.M₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁ from le_sup_right) hm)
    point_control := by
      intro hC
      change (ofFlag S f X z ⊥).G₁ ≤ (ofFlag S f X z ⊥).M
      rw [a.earlier.normalizer_split e.fixed_trivial]
      exact sup_le hC inf_le_left
    component_centralizes_point := a.earlier.line_component_centralizes
    strict_escape := Triangle.Reselection.proper_flag_component_escapes D S f E.K
      a.earlier.line_component (Triangle.Reselection.flag_residual_mem_local D S f 0)
    strict_core := fun _ => hcomm
    strict_radical := fun hlt => ⟨hrad,hindex hlt⟩ }
  have hp := WeakClosure.Parameters.source_parameters D S f a.maximal_unique
    a.three_centralizer a.fixed_line
  have hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞) := by
    rw [hp.2.2.1.2, ← hp.1, e.local_parameter]
    rfl
  have hweak : Chapter11.Source.WeakClosureObstruction (T : Subgroup G) V (f.Vi 0) J := by
    by_cases hab : IsMulCommutative E.W
    · have hK := component_eq_of_abelian s e a.point_split a.first_component hs hab
      let F₀ := e.marked_flag.some
      have hr := (Closure.Nonabelian.PointModels.intersection_and_rank F₀ e.fixed_trivial
        e.point_mem e.point_ne_one e.transitive e.comparison (Preliminary.seed_ti D S) hK).2
      have hplane := Closure.Nonabelian.plane_centralizer_le F₀ e.fixed_trivial
        (WeakClosure.seed_normalizer_le D S)
        (by rwa [Closure.Nonabelian.corank_line F₀ e.fixed_trivial])
      exact WeakClosure.source_weakClosureObstruction D S f a.maximal_unique
        a.three_centralizer a.fixed_line a.second_component J e.outside.1.1.2 e.outside.1.2
        (fun _ => hplane) a.plane_sylow a.plane_fixed a.plane_radical a.linear_movement
    · apply Or.inr
      have he : Chapter11.Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V = E.W :=
        (conjugateSpanBy_eq_iSup_conj V E.G₁).symm
      change ¬ IsMulCommutative (Chapter11.Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V)
      rwa [he]
  exact Closure.impossible_of_endgame_of_source_distance E s e hweak a.point_split
    a.first_component hs a.second_component

include hmany a h701 h1132 h1122 in
/-- Compatibility with the earlier contract that supplied distance two.
The preceding-geometry theorem now discharges that step internally. -/
theorem nonbinary_impossible_of_source_inputs_of_many
    (_hdistance : NonbinaryNaturalDistanceTwo S f) : False :=
  nonbinary_impossible_of_preceding_geometry_of_many S hmany f X z a h701 h1132 h1122

/-- Existence contract for the independent local and distance producers. The
Fitting-index field remains explicit in `NonbinaryNaturalLocalInputs`. There
is no nonbinary-exclusion or terminal closure premise in this contract. -/
@[expose] def NonbinaryNaturalLocalSources (D : ChosenModule T L V) : Prop :=
  ∀ S : D.NonbinaryNaturalInput, ∃ (c : Coordinates D S.field) (f : InvariantFlag c)
    (X : Subgroup G) (z : G), Nonempty (NonbinaryNaturalLocalInputs S f X z) ∧
      NonbinaryNaturalDistanceTwo S f

include hmany h701 h1132 h1122 in
/-- Eliminate precisely the three nonbinary source rows on D.space's literal
fixed-space quotient. Full-cover recovery supplies the original L/O₂(L)
marking; the local inputs and earlier classification implications are then
applied to that same chosen module. Their existence is still explicit. -/
theorem nonbinaryRow_impossible_of_local_sources_of_many
    {P : Type*} [Group P] {ρ : Representation (ZMod 2) P D.space} {K : Subgroup P}
    (cmp : D.LiteralComparison ρ K)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (horbits : componentOrbit V (normalizer (L : Set G)) = V ∨
      (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    (section_ : MovedSection ρ K) (hf : Function.Injective (section_.action.comp K.subtype))
    (F : BinaryField) (hF : 1 < F.degree)
    (row : LiteralComparison.NonbinaryRow section_ F)
    (hlocal : NonbinaryNaturalLocalSources D) : False := by
  obtain ⟨S⟩ := cmp.nonbinaryInput_of_source_branch h hmany horbits hff section_ hf F hF row
  obtain ⟨c,f,X,z,⟨a⟩,hd⟩ := hlocal S
  exact nonbinary_impossible_of_source_inputs_of_many S hmany f X z a h701 h1132 h1122 hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
