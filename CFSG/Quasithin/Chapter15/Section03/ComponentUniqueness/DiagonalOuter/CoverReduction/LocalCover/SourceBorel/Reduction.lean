module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Rank
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Containment
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry

/-!
# From the source Borel and cyclic actor to compatible root-plane data

Rank two gives normality of L inside I, and characteristic two of M ∩ I
puts L outside M. Source 15.3.33(1) places the invariant Borel in M ∩ I;
15.3.11(4),(6) then give its action on Y₊ and identify θ(B) with Y_L.
Projective rigidity, together with perfectness of L and its central
two-kernel, gives C_S(Y_L)=C_S(L). A trivial module commutator would put
L in N_G(V)=M, so the cyclic actor calculation applies nontrivially.

The chosen moving plane lies in S ∩ L and is B-invariant. Its image cannot
vanish in the central kernel because it equals its commutator with Y_L.
The intrinsic root test therefore gives `RootInPlane` on the same projective
marking. Both original planes and both actual interchanges are retained.

This is a conditional assembly: constructing `BorelStep` and the uniform
cyclic-plane theorem remains required. No theorem here establishes the source
Borel construction from `Earlier` and `Setup` alone, or asserts 15.3.38.
In particular, O²(B) is not identified with θ(B); odd torus primes other
than three prevent that shortcut.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed pp.1135--1136, using pp.1121--1125.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
variable {G : Type*} [Group G] [Finite G]

variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

theorem Setup.normal (h : Setup d I L) (e : Earlier d) : (L.subgroupOf I).Normal :=
  rank_two_component_normal_in h.component_le h.component (e.odd I h.outside)
    (e.rank I h.outside) h.component_rank

theorem Setup.outside_component (h : Setup d I L) (e : Earlier d) : ¬ L ≤ d.M := by
  intro hLM
  apply component_not_le_characteristicTwo h.component
    (e.intersection_characteristic_two I h.outside)
  intro x hx
  exact hLM hx

theorem Setup.normalizes_component (h : Setup d I L) (e : Earlier d) :
    I ≤ normalizer (L : Set G) :=
  (normal_subgroupOf_iff_le_normalizer h.component_le).mp (h.normal e)

theorem Setup.core_central (h : Setup d I L) (e : Earlier d) : pCore 2 L ≤ center L :=
  (center_eq_twoCore_in h.component_le h.component (e.odd I h.outside)).ge

omit [Finite G] in
theorem Setup.perfect (h : Setup d I L) : Group.IsPerfect L := by
  let := h.component.2
  exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective

theorem module_le_sylow (d : CharacteristicTwo.LocalData G) : d.V ≤ d.S :=
  d.action.le_planeStabilizer d.T d.sylow_le (localModule_le d.T d.sylow_le) 1

theorem residual_normalized (h : Setup d I L) (e : Earlier d) :
    d.S ≤ normalizer (componentPart d.Yplus L : Set G) := by
  change d.S ≤ normalizer (Stellmacher.twoResidualAmbient (d.Yplus ⊓ L) : Set G)
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  apply (le_normalizer_inf
    (RankTwo.planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice)
    ((le_sup_right.trans h.outside.1.2).trans (h.normalizes_component e))).trans
  exact normalizer_le_normalizer_characteristic_image (d.Yplus ⊓ L) (pResidual 2 (d.Yplus ⊓ L : Subgroup G))

/-- Source 15.3.33(1) is applied to the actual Borel. -/
theorem BorelStep.le_intersection {q : ℕ} {c : ProjectiveMarking L q}
    (b : BorelStep d I L c) (h : Setup d I L) (e : Earlier d) :
    borel d.S L ≤ d.M ⊓ I := by
  let := e.solvable
  exact lemma_15_3_33_1 h.outside e.sylow e.exclusion e.odd
    (inf_le_left.trans h.component_le) b.invariant b.characteristic_two

/-- The normalizer clause of 15.3.11 makes the Borel act on Y₊. -/
theorem BorelStep.normalizes_yplus {q : ℕ} {c : ProjectiveMarking L q}
    (b : BorelStep d I L c) (h : Setup d I L) (e : Earlier d) :
    borel d.S L ≤ normalizer (d.Yplus : Set G) :=
  ((b.le_intersection h e).trans (e.normalizer_eq I h.outside).ge).trans inf_le_right

/-- The theta clause of 15.3.11 identifies the component residual with θ(B).
An order-three element of B lies in Y₊ and then in O²(Y₊ ∩ L). -/
theorem BorelStep.theta_eq {q : ℕ} {c : ProjectiveMarking L q}
    (b : BorelStep d I L c) (h : Setup d I L) (e : Earlier d) :
    theta (borel d.S L) = componentPart d.Yplus L := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨hx, hx3⟩
    have hxY : x ∈ d.Yplus := e.theta_eq I h.outside ▸
      subset_closure ⟨b.le_intersection h e hx, hx3⟩
    have hxL : x ∈ L := hx.1
    change x ∈ Stellmacher.twoResidualAmbient (d.Yplus ⊓ L)
    rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    refine ⟨⟨x, hxY, hxL⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
    have ho : orderOf (⟨x, hxY, hxL⟩ : (d.Yplus ⊓ L : Subgroup G)) = 3 :=
      (orderOf_injective (d.Yplus ⊓ L).subtype (d.Yplus ⊓ L).subtype_injective _).symm.trans hx3
    exact ho ▸ (show Nat.Coprime 2 3 by decide)
  · exact b.residual_generated.ge.trans (theta_mono b.residual_le)

/-- The centralizer of the theta subgroup is transported through the fixed
quotient marking. Perfectness removes the central two-kernel. -/
theorem BorelStep.sylow_centralizer {q : ℕ} {c : ProjectiveMarking L q}
    (b : BorelStep d I L c) (h : Setup d I L) (e : Earlier d) (m : MatrixTests c) :
    d.S ⊓ centralizer (componentPart d.Yplus L : Set G) =
      d.S ⊓ centralizer (L : Set G) := by
  let := h.perfect
  apply le_antisymm
  · rintro s ⟨hs, hc⟩
    refine ⟨hs, ?_⟩
    let s' : normalizer (L : Set G) :=
      ⟨s, h.normalizes_component e (h.outside.1.2 (mem_sup_right hs))⟩
    have ha : markedAction c s' = 1 := by
      apply m.rigid b.P
      intro x hx
      rw [← b.theta_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rw [markedAction_apply]
      congr 1
      apply Subtype.ext
      change s * (a : G) * s⁻¹ = a
      have haA : (a : G) ∈ componentPart d.Yplus L := b.theta_eq h e ▸ ha
      exact mul_inv_eq_iff_eq_mul.mpr (hc a haA).symm
    have hc' := (markedAction_eq_one_iff c s').mp ha
    rwa [sectionCentralizer_eq_centralizer_of_perfect (h.core_central e)] at hc'
  · exact inf_le_inf_left _ (centralizer_le ((map_subtype_le _).trans inf_le_right))

/-- Trivial action would put the outside component in N_G(V)=M. -/
theorem nontrivial_module_commutator (h : Setup d I L) (e : Earlier d)
    (hc : d.S ⊓ centralizer (componentPart d.Yplus L : Set G) =
      d.S ⊓ centralizer (L : Set G)) : ⁅d.V, componentPart d.Yplus L⁆ ≠ ⊥ := by
  intro hz
  have hV : d.V ≤ centralizer (L : Set G) :=
    ((le_inf (module_le_sylow d) (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
      hc.le).trans inf_le_right
  apply h.outside_component e
  rw [← e.module_normalizer]
  exact (le_centralizer_iff.mp hV).trans (Subgroup.centralizer_le_normalizer _)

omit [Finite G] in
theorem projectiveMap_ker {q : ℕ} (c : ProjectiveMarking L q) :
    (projectiveMap c).ker = pCore 2 L := by
  ext x
  change c.equivalence (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  rw [map_eq_one_iff c.equivalence c.equivalence.injective]
  exact QuotientGroup.eq_one_iff _

omit [Finite G] in
/-- A nontrivial moved subgroup cannot disappear in the central two-kernel. -/
theorem moved_image_ne_bot {q : ℕ} (c : ProjectiveMarking L q)
    {W A : Subgroup G} (hWL : W ≤ L) (hAL : A ≤ L)
    (hcore : pCore 2 L ≤ center L) (hm : ⁅W, A⁆ = W) (hne : W ≠ ⊥) :
    (W.subgroupOf L).map (projectiveMap c) ≠ ⊥ := by
  intro hz
  have hk := (Subgroup.map_eq_bot_iff _).mp hz
  rw [projectiveMap_ker] at hk
  have hWC : W ≤ centralizer (A : Set G) := by
    intro w hw a ha
    have hwZ := hcore (hk (show (⟨w, hWL hw⟩ : L) ∈ W.subgroupOf L from hw))
    exact congrArg Subtype.val (mem_center_iff.mp hwZ (⟨a, hAL ha⟩ : L))
  exact hne (hm.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hWC))

omit [Finite G] in
/-- Normalization passes to the images under the actual quotient map. -/
theorem normalizes_projective_image {q : ℕ} (c : ProjectiveMarking L q)
    {B W : Subgroup G} (hn : B ≤ normalizer (W : Set G)) :
    (B.subgroupOf L).map (projectiveMap c) ≤
      normalizer ((W.subgroupOf L).map (projectiveMap c) : Set PSL(3,c.F)) := by
  apply (map_mono ?_).trans ((W.subgroupOf L).le_normalizer_map (projectiveMap c))
  apply le_normalizer_iff.mpr
  intro b hb w hw
  exact (mem_normalizer_iff.mp (hn hb) (w : G)).mp hw

/-- The normal commutator plane contains an inner conjugate of the standard
root. Neither the marking nor the original diagonal actor is changed. -/
theorem BorelStep.root_of_moved_plane {q : ℕ} {c : ProjectiveMarking L q}
    (b : BorelStep d I L c) (h : Setup d I L) (e : Earlier d) (m : MatrixTests c)
    {W : Subgroup G} (hWS : W ≤ d.S ⊓ L)
    (hBW : borel d.S L ≤ normalizer (W : Set G))
    (hm : ⁅W, componentPart d.Yplus L⁆ = W) (hne : W ≠ ⊥) : RootInPlane c W := by
  apply m.root b.P ((W.subgroupOf L).map (projectiveMap c))
  · rw [← b.sylow_image]
    exact map_mono (by intro w hw; exact (hWS hw).1)
  · rw [← b.borel_image]
    exact normalizes_projective_image c hBW
  · exact moved_image_ne_bot c (hWS.trans inf_le_right)
      ((map_subtype_le _).trans inf_le_right) (h.core_central e) hm hne

/-- Final assembly from the two independent intermediate constructions.
Their constructors remain required before this yields the source Borel output. -/
theorem orientedBorelData_of_steps {n : ℕ} {c : ProjectiveMarking L (2 ^ n)}
    (h : Setup d I L) (e : Earlier d) (m : MatrixTests c)
    (b : BorelStep d I L c) (p : CyclicPlaneChoice d (componentPart d.Yplus L)) :
    Nonempty (OrientedBorelData d.M d.Yplus d.S L d.V₁ d.V₂ c) := by
  have hVL : ⁅d.V, componentPart d.Yplus L⁆ ≤ L :=
    (commutator_mono le_rfl ((map_subtype_le _).trans inf_le_right)).trans
      (le_normalizer_iff_commutator_le_right.mp
        (((module_le_sylow d).trans (le_sup_right.trans h.outside.1.2)).trans
          (h.normalizes_component e)))
  have hW₂L : p.W₂ ≤ L := p.commutator ▸ hVL
  have hplanes : p.W₁ ≤ d.S ∧ p.W₂ ≤ d.S ∧ Nat.card p.W₂ = 4 ∧
      d.S ≤ normalizer (p.W₂ : Set G) := by
    rcases p.planes with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]
      exact ⟨(d.action.plane_le 1).trans (module_le_sylow d),
        (d.action.plane_le _).trans (module_le_sylow d), d.action.card_plane _,
        RankTwo.planeStabilizer_normalizes_planes d.action d.T d.sylow_le 1 _⟩
    · rw [h₁, h₂]
      exact ⟨(d.action.plane_le _).trans (module_le_sylow d),
        (d.action.plane_le 1).trans (module_le_sylow d), d.action.card_plane 1,
        RankTwo.planeStabilizer_normalizes_planes d.action d.T d.sylow_le 1 1⟩
  have hWS := le_inf hplanes.2.1 hW₂L
  have hBA : borel d.S L ≤ normalizer (componentPart d.Yplus L : Set G) := by
    rw [← b.theta_eq h e]
    exact (borel d.S L).le_normalizer.trans (normalizer_le_normalizer_theta _)
  have hBV := ((b.le_intersection h e).trans inf_le_left).trans d.action.normalizes
  have hBW : borel d.S L ≤ normalizer (p.W₂ : Set G) := by
    rw [← p.commutator]
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hBV hx),
      mem_normalizer_iff_map_conj_eq.mp (hBA hx)]
  have hc := b.sylow_centralizer h e m
  have hne : p.W₂ ≠ ⊥ := p.commutator ▸ nontrivial_module_commutator h e hc
  refine ⟨{
    W₁ := p.W₁, W₂ := p.W₂, planes := p.planes
    first_le_sylow := hplanes.1
    second_le_component_sylow := hWS
    second_card := hplanes.2.2.1
    second_invariant := hplanes.2.2.2
    t := p.t, t_mem := d.sylow_le p.t_mem
    sylow_invariant := p.sylow_invariant
    first_interchange := p.first_interchange
    second_interchange := p.second_interchange
    component_centralizes := p.centralizes
    component_moves := p.moves
    sylow_centralizer := hc
    component_core := b.theta_eq h e ▸ b.theta_core
    component_quotient := b.theta_eq h e ▸ b.theta_quotient
    root := b.root_of_moved_plane h e m hWS hBW p.moves hne }⟩

/-- Apply a uniform cyclic-plane theorem to this component residual.
All of its local hypotheses are discharged here; its construction is independent
of the Borel calculation and of the projective root calculation. -/
theorem orientedBorelData_of_borel_and_plane_theorem
    {n : ℕ} {c : ProjectiveMarking L (2 ^ n)}
    (h : Setup d I L) (e : Earlier d) (m : MatrixTests c) (b : BorelStep d I L c)
    (planes : ∀ A : Subgroup G, A ≤ d.M → IsPPerfect 2 A →
      d.S ≤ normalizer (A : Set G) → Nat.card (A ⧸ pCore 2 A) = 3 →
      ⁅d.V, A⁆ ≠ ⊥ → Nonempty (CyclicPlaneChoice d A)) :
    Nonempty (OrientedBorelData d.M d.Yplus d.S L d.V₁ d.V₂ c) := by
  have hAM : componentPart d.Yplus L ≤ d.M :=
    b.residual_le.trans ((b.le_intersection h e).trans inf_le_left)
  obtain ⟨p⟩ := planes (componentPart d.Yplus L) hAM
    (ComponentIntersection.intersectionResidual_isPPerfect d.Yplus L)
    (residual_normalized h e) (b.theta_eq h e ▸ b.theta_quotient)
    (nontrivial_module_commutator h e (b.sylow_centralizer h e m))
  exact orientedBorelData_of_steps h e m b p

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
