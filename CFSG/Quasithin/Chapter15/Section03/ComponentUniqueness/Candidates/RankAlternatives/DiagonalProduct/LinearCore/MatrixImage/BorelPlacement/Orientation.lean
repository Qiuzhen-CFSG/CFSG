module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.BorelPlacement
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.BorelConstruction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.CyclicPlanes
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelInvariantRoot
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.CubicBorelFixer

/-!
# Product-free assembly of the two original Borel planes

The actual Sylow normalizer has characteristic two by the projective Borel
calculation, so 15.3.33(1) places it in M. Its theta subgroup is precisely
A = O²(Y₊ ∩ L): the forward inclusion uses 15.3.11(6), and the reverse
uses the genuine exponent-three two-core quotient in `Earlier`.

Theta rigidity gives C_S(A) = C_S(L), which makes [V,A] nontrivial.
The proved cyclic-plane theorem orients the original planes and supplies
their actual interchange. The moving plane is Borel-invariant, and its
nonzero projective image contains a root by the intrinsic root calculation.

The two `MatrixTests` are discharged by intrinsic theorems here. The final
constructor still has two mathematical obligations: actual Sylow invariance,
and the theta-core and quotient calculations. It requires neither
Y₊ = A⟨y⟩ nor the stronger normalizer equality N_I(B) = M ∩ I from `BorelStep`.

Source: Aschbacher--Smith, 15.3.11--12, 15.3.33 and 15.3.36--38,
printed pp.1123--1125 and 1134--1136.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction

variable {G : Type*} [Group G]

/-- An outer marked actor lies outside the component, without a product assumption. -/
theorem ProjectiveMarking.Diagonal.not_mem {L : Subgroup G} {q : ℕ}
    {c : ProjectiveMarking L q} {y : G} (hy : c.Diagonal y) : y ∉ L := by
  intro hyL
  obtain ⟨_, a, ha, hr⟩ := hy
  have he := LocalCover.markedAction_eq_of_realizes c
    (inclusion L.le_normalizer ⟨y, hyL⟩) hr
  rw [LocalCover.markedAction_on_component] at he
  exact ha ⟨_, he⟩

namespace LocalCover.SourceBorel
variable [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

omit [Finite G] in
/-- The intrinsic rigidity and root tests are theorems for every even exponent. -/
theorem matrixTests_of_even_card {n : ℕ} (hn : 0 < n) (heven : Even n)
    (c : ProjectiveMarking L (2 ^ n)) : MatrixTests c := by
  constructor
  · intro P α hfix
    apply Matrix.PSL3.LinearThree.CubicBorel.eq_one_of_fixes_sylowNormalizer_cubics
      hn heven c.card P α
    intro x hx hx3
    exact hfix x (subset_closure ⟨hx, hx3⟩)
  · exact Matrix.PSL3.LinearThree.BorelStructure.exists_root_le_of_borel_invariant c.F hn c.card

omit [Finite G] in
/-- Build the contrary-branch setup from its selected component and outer actor. -/
theorem setup_of_marked_actor (hI : I ∈ d.Hplus) (hLI : L ≤ I)
    (hL : IsComponent I (L.subgroupOf I))
    (hrL : primeRank 3 L = 2) (hrY : primeRank 3 d.Yplus = 2)
    {q : ℕ} (c : ProjectiveMarking L q) {y : G}
    (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y) : Setup d I L :=
  ⟨hI, hLI, hL, hrL, hrY, fun h => hdiag.not_mem (h hy)⟩

/-- The Borel theta identity uses the residual's definitional containment in Y₊. -/
theorem theta_borel_of_invariance (h : Setup d I L) (e : Earlier d)
    (hstable : d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G))
    (hBM : borel d.S L ≤ d.M ⊓ I) :
    theta (borel d.S L) = componentPart d.Yplus L := by
  have hAY : componentPart d.Yplus L ≤ d.Yplus :=
    (map_subtype_le _).trans inf_le_left
  have hAB : componentPart d.Yplus L ≤ borel d.S L :=
    le_inf ((map_subtype_le _).trans inf_le_right)
      ((hAY.trans le_sup_left).trans hstable)
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨hx, hx3⟩
    exact Candidates.LinearCore.MatrixImage.order_three_mem_componentPart
      (e.theta_eq I h.outside ▸ subset_closure ⟨hBM hx, hx3⟩) hx.1 hx3
  · exact (component_residual_generated e).ge.trans (theta_mono hAB)

/-- Direct assembly of the needed Borel planes. The stronger Borel normalizer
clause and the ambient product are absent; all cyclic-plane premises are discharged. -/
theorem orientedBorelData_of_sylow_and_theta
    (h : Setup d I L) (e : Earlier d) {n : ℕ} (hn : 0 < n)
    (c : ProjectiveMarking L (2 ^ n)) (m : MatrixTests c)
    (hstable : d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G))
    (hcore : (theta (borel d.S L)).pCoreIn 2 = d.S ⊓ L)
    (hquot : Nat.card (theta (borel d.S L) ⧸ pCore 2 (theta (borel d.S L))) = 3) :
    Nonempty (OrientedBorelData d.M d.Yplus d.S L d.V₁ d.V₂ c) := by
  obtain ⟨P, hP, hpre⟩ := h.projective_sylow e c
  have hB := borel_eq_projectivePreimage c P hpre
  have hchar : generalizedFitting (borel d.S L) = pCore 2 (borel d.S L) := by
    rw [hB]
    apply Matrix.PSL3.LinearThree.BorelStructure.sylowNormalizer_preimage_image_characteristicTwo
      c.F hn c.card (projectiveMap c) (projectiveMap_surjective c) _ P L.subtype L.subtype_injective
    rw [projectiveMap_ker]
    exact pCore_isPGroup
  have hinv : d.Yplus ⊔ d.S ≤ normalizer (borel d.S L : Set G) :=
    le_normalizer_inf (h.outside.1.2.trans (h.normalizes_component e))
      (hstable.trans (normalizer ((d.S ⊓ L : Subgroup G) : Set G)).le_normalizer)
  have hBM : borel d.S L ≤ d.M ⊓ I := by
    let := e.solvable
    exact lemma_15_3_33_1 h.outside e.sylow e.exclusion e.odd
      (inf_le_left.trans h.component_le) hinv hchar
  have htheta := theta_borel_of_invariance h e hstable hBM
  have hAB : componentPart d.Yplus L ≤ borel d.S L := htheta ▸ theta_le _
  have himage : ((borel d.S L).subgroupOf L).map (projectiveMap c) =
      normalizer (P : Set PSL(3,c.F)) := by
    rw [hB, projectivePreimage_image]
  have htimage : ((componentPart d.Yplus L).subgroupOf L).map (projectiveMap c) =
      theta (normalizer (P : Set PSL(3,c.F))) := by
    rw [← htheta, theta_projective_image c (B := borel d.S L) inf_le_left, himage]
  have hc : d.S ⊓ centralizer (componentPart d.Yplus L : Set G) =
      d.S ⊓ centralizer (L : Set G) := by
    let := h.perfect
    apply le_antisymm
    · rintro s ⟨hs, hsa⟩
      refine ⟨hs, ?_⟩
      let s' : normalizer (L : Set G) :=
        ⟨s, h.normalizes_component e (h.outside.1.2 (mem_sup_right hs))⟩
      have ha : markedAction c s' = 1 := by
        apply m.rigid P
        intro x hx
        rw [← htimage] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        rw [markedAction_apply]
        congr 1
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (hsa a ha).symm
      have hc' := (markedAction_eq_one_iff c s').mp ha
      rwa [sectionCentralizer_eq_centralizer_of_perfect (h.core_central e)] at hc'
    · exact inf_le_inf_left _ (centralizer_le ((map_subtype_le _).trans inf_le_right))
  have hnon := nontrivial_module_commutator h e hc
  obtain ⟨p⟩ := cyclicPlaneChoice_of_card_quotient_three d (componentPart d.Yplus L)
    (hAB.trans (hBM.trans inf_le_left))
    (ComponentIntersection.intersectionResidual_isPPerfect d.Yplus L)
    (residual_normalized h e) (htheta ▸ hquot) hnon
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
    rw [← htheta]
    exact (borel d.S L).le_normalizer.trans (normalizer_le_normalizer_theta _)
  have hBV := (hBM.trans inf_le_left).trans d.action.normalizes
  have hBW : borel d.S L ≤ normalizer (p.W₂ : Set G) := by
    rw [← p.commutator]
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hBV hx),
      mem_normalizer_iff_map_conj_eq.mp (hBA hx)]
  have hne : p.W₂ ≠ ⊥ := p.commutator ▸ hnon
  have hroot : RootInPlane c p.W₂ := by
    apply m.root P ((p.W₂.subgroupOf L).map (projectiveMap c))
    · rw [← hP]
      exact map_mono (by intro w hw; exact (hWS hw).1)
    · rw [← himage]
      exact normalizes_projective_image c hBW
    · exact moved_image_ne_bot c hW₂L ((map_subtype_le _).trans inf_le_right)
        (h.core_central e) p.moves hne
  exact ⟨{
    W₁ := p.W₁, W₂ := p.W₂, planes := p.planes
    first_le_sylow := hplanes.1, second_le_component_sylow := hWS
    second_card := hplanes.2.2.1, second_invariant := hplanes.2.2.2
    t := p.t, t_mem := d.sylow_le p.t_mem, sylow_invariant := p.sylow_invariant
    first_interchange := p.first_interchange, second_interchange := p.second_interchange
    component_centralizes := p.centralizes, component_moves := p.moves
    sylow_centralizer := hc, component_core := htheta ▸ hcore
    component_quotient := htheta ▸ hquot, root := hroot }⟩

/-- The marked source branch yields both original oriented planes once the
actual Sylow invariance and theta-core/quotient calculations have been supplied.
The actor proves the contrary-branch premise; both matrix tests are discharged. -/
theorem orientedBorelData_of_marked_local
    (hI : I ∈ d.Hplus) (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hrL : primeRank 3 L = 2) (hrY : primeRank 3 d.Yplus = 2) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y)
    (hstable : d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G))
    (hcore : (theta (borel d.S L)).pCoreIn 2 = d.S ⊓ L)
    (hquot : Nat.card (theta (borel d.S L) ⧸ pCore 2 (theta (borel d.S L))) = 3) :
    Nonempty (OrientedBorelData d.M d.Yplus d.S L d.V₁ d.V₂ c) :=
  orientedBorelData_of_sylow_and_theta
    (setup_of_marked_actor hI hLI hL hrL hrY c hy hdiag) e hn c
    (matrixTests_of_even_card hn heven c) hstable hcore hquot

end LocalCover.SourceBorel
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction
