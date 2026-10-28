module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.FixedLayer
public import Theory.GroupTheory.PResidual.PrimeToIntersection
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PGroup.OmegaCenterDetection

/-!
# The characteristic-centralizer step for the binary-three exception

When L₀ fixes Ω₁Z(T), source uniqueness controls its centralizer. If this
omega-center lies in Ω₁Z(C_T(v)), the latter centralizer is therefore inside
M. The identity O^{3′}(M)=L₀ transports the cubic residual of its intersection
with L₀ to its full ambient centralizer. Taking the solvable residual of
this characteristic subgroup removes the solvable point-stabilizer factor.
Identifying the result with L makes every normalizer of C_T(v) normalize L.

This supplies the normalizer implication in the positive-fixed-layer case
of original 10.2.8--9. The module-specific omega-center and intersection
identities remain explicit. Source: Aschbacher--Smith, pp.749--750, using
10.1.3 on p.742. Every residual below retains its actual ambient inclusion.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Selection
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

omit D in
/-- The perfect part of the embedded cubic residual. The solvable residual
is necessary: a point stabilizer can contribute an A₄ factor to O^{3′}. -/
def cubicPerfectCore (X : Subgroup G) : Subgroup G :=
  (solvableResidual ((primeToResidual 3 X).map X.subtype)).map
    ((primeToResidual 3 X).map X.subtype).subtype

/-- Source uniqueness controls the Sylow omega-center when L₀ fixes it. -/
theorem sylow_omega_centralizer_le
    (hZ : localOrbit T L ≤ centralizer (omegaCenterIn (T : Subgroup G) : Set G)) :
    centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ D.maximalLocal := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro he
    apply D.module_ne_bot
    exact le_bot_iff.mp (((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans
      (D.fullModule_le_sylow hu)).trans he.le)
  have hZne : omegaCenterIn (T : Subgroup G) ≠ ⊥ := by
    intro he
    apply hTne
    apply eq_bot_of_normalized_of_omega_center_disjoint (T : Subgroup G)
      (T : Subgroup G) T.isPGroup' le_rfl (T : Subgroup G).le_normalizer
    rw [← omegaCenterIn_eq_omegaOneAmbient,he,bot_inf_eq]
  have hTZ : (T : Subgroup G) ≤ centralizer (omegaCenterIn (T : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (fun z hz => (mem_omegaCenterIn_iff _ _).mp hz |>.2.1)
  exact (Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness hu).2.2
      (IsElementaryAbelian.isPGroup 2 _) hZne
      ((sup_le hZ hTZ).trans (Subgroup.centralizer_le_normalizer _)))

/-- Inside M, intersection with L₀ preserves the perfect part of the
embedded cubic residual. -/
theorem cubicPerfectCore_eq_of_intersection
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    {X : Subgroup G} (hXM : X ≤ D.maximalLocal)
    (hr : cubicPerfectCore (localOrbit T L ⊓ X) = L) :
    cubicPerfectCore X = L := by
  have he := embedded_primeToResidual_intersection 3 D.maximalLocal X
  rw [source_nonnormal_cubic_residual D hn hd,inf_eq_right.mpr hXM] at he
  change (solvableResidual ((primeToResidual 3 X).map X.subtype)).map
    ((primeToResidual 3 X).map X.subtype).subtype = L
  rw [← he]
  exact hr

/-- The literal residual in the omega-center centralizer forces the
normalizer of the original point Sylow into M. -/
theorem point_normalizer_le_of_omega_residual
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hhalf : HalfSylowUnique D)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (hZ : localOrbit T L ≤ centralizer (omegaCenterIn (T : Subgroup G) : Set G))
    (v : G)
    (hZle : omegaCenterIn (T : Subgroup G) ≤
      omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G)))
    (hr : cubicPerfectCore (localOrbit T L ⊓ centralizer
      (omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) = L) :
    normalizer ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G) ≤ D.maximalLocal := by
  let Z := omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
  let X := centralizer (Z : Set G)
  have hXM : X ≤ D.maximalLocal := (centralizer_le hZle).trans
    (sylow_omega_centralizer_le D hZ)
  have hres := cubicPerfectCore_eq_of_intersection D hn hd hXM hr
  have hNX : normalizer (Z : Set G) ≤ normalizer (L : Set G) := by
    rw [← hres]
    unfold cubicPerfectCore
    exact (normalizer_le_normalizer_centralizer Z).trans
      ((normalizer_le_normalizer_characteristic_image X (primeToResidual 3 X)).trans
        (normalizer_le_normalizer_characteristic_image _ (solvableResidual _)))
  exact (normalizer_le_normalizer_omegaCenterIn _).trans
    (hNX.trans (component_normalizer_le_of_halfSylowUnique D hn hhalf))

end CFSG.Quasithin.Chapter10.PointControl.Selection
