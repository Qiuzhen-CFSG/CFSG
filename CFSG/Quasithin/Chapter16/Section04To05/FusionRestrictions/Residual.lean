module

public import CFSG.Quasithin.Chapter16.Section04To05.Terminal
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The residuals in Notation 16.5.5

Here L_r is the embedded two-residual O²(C_L(r)). The modification X_r
is its three-residual exactly when the entire component L is isomorphic
to PSL₃(2ⁿ) for a positive even n. The isomorphism predicate uses actual
matrix groups; it is preserved by transport, as are both residuals.

Mutual containment in the two components and two-perfectness imply that
the modified residuals agree: each lies in the other involution centralizer,
then in its two-residual and, in the exceptional case, its three-residual.
`exists_common_residual` constructs the common subgroup and proves its
independence of the chosen involutions and its centralization by R and T_C.

This is the algebraic part of Notation 16.5.5 and 16.5.6(1)–(2), conditional
on the earlier cross-containments and the local two-perfectness calculation.
It does not assert the model calculation, the normalizing-conjugator clause,
or the two-central symmetry. In particular, two-perfectness of O³(O²(H))
is not a general residual identity and is retained as a genuine input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, pp.1197–1198.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The exceptional case in Notation 16.5.5, for the full component L. -/
def HasEvenLinearThreeType (L : Subgroup G) : Prop :=
  ∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n)

/-- L_r = O²(C_L(r)), embedded in the ambient group. -/
def involutionTwoResidual (L : Subgroup G) (r : G) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer ({r} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({r} : Set G)).subtype

/-- The actual X_r from Notation 16.5.5. -/
noncomputable def modifiedCentralizerResidual (L : Subgroup G) (r : G) : Subgroup G := by
  classical
  exact if HasEvenLinearThreeType L then
    (pResidual 3 (involutionTwoResidual L r)).map (involutionTwoResidual L r).subtype
  else involutionTwoResidual L r

/-- The two-residual lies in its defining centralizer. -/
theorem involutionTwoResidual_le (L : Subgroup G) (r : G) :
    involutionTwoResidual L r ≤ L ⊓ centralizer ({r} : Set G) :=
  map_subtype_le _

/-- Modifying the residual never enlarges it. -/
theorem modifiedCentralizerResidual_le (L : Subgroup G) (r : G) :
    modifiedCentralizerResidual L r ≤ involutionTwoResidual L r := by
  classical
  unfold modifiedCentralizerResidual
  split_ifs
  · exact map_subtype_le _
  · exact le_rfl

/-- Conjugation and other ambient isomorphisms preserve the exceptional case. -/
theorem hasEvenLinearThreeType_map_iff (L : Subgroup G) (e : G ≃* G) :
    HasEvenLinearThreeType (L.map e.toMonoidHom) ↔ HasEvenLinearThreeType L := by
  constructor
  · rintro ⟨n, hn, he, hL⟩
    exact ⟨n, hn, he, hL.of_mulEquiv (e.subgroupMap L)⟩
  · rintro ⟨n, hn, he, hL⟩
    exact ⟨n, hn, he, hL.of_mulEquiv (e.subgroupMap L).symm⟩

/-- Transport of the actual embedded two-residual. -/
theorem involutionTwoResidual_map [Finite G] (L : Subgroup G) (r : G) (e : G ≃* G) :
    (involutionTwoResidual L r).map e.toMonoidHom =
      involutionTwoResidual (L.map e.toMonoidHom) (e r) := by
  unfold involutionTwoResidual
  rw [map_embedded_pResidual, map_inf _ _ _ e.injective,
    map_centralizer_equiv, Set.image_singleton]

/-- Transport of X_r, including its exceptional three-residual branch. -/
theorem modifiedCentralizerResidual_map [Finite G] (L : Subgroup G) (r : G) (e : G ≃* G) :
    (modifiedCentralizerResidual L r).map e.toMonoidHom =
      modifiedCentralizerResidual (L.map e.toMonoidHom) (e r) := by
  classical
  unfold modifiedCentralizerResidual
  by_cases hL : HasEvenLinearThreeType L
  · rw [if_pos hL, if_pos ((hasEvenLinearThreeType_map_iff L e).mpr hL),
      map_embedded_pResidual, involutionTwoResidual_map]
  · rw [if_neg hL, if_neg (fun h => hL ((hasEvenLinearThreeType_map_iff L e).mp h)),
      involutionTwoResidual_map]

private theorem le_embedded_residual_of_perfect {X C : Subgroup G} {p : ℕ}
    (hX : IsPPerfect p X) (hXC : X ≤ C) :
    X ≤ (pResidual p C).map C.subtype := by
  have h := map_pResidual_le p (inclusion hXC)
  rw [(pResidual_eq_top_iff p X).mpr hX] at h
  intro x hx
  exact ⟨inclusion hXC ⟨x, hx⟩, h ⟨⟨x, hx⟩, mem_top _, rfl⟩, rfl⟩

/-- A subgroup perfect at the required primes lies in X_r when it centralizes r. -/
theorem le_modifiedCentralizerResidual {X L : Subgroup G} {r : G}
    (hXL : X ≤ L) (hXr : X ≤ centralizer ({r} : Set G))
    (hX2 : IsPPerfect 2 X) (hX3 : HasEvenLinearThreeType L → IsPPerfect 3 X) :
    X ≤ modifiedCentralizerResidual L r := by
  have htwo : X ≤ involutionTwoResidual L r :=
    le_embedded_residual_of_perfect hX2 (le_inf hXL hXr)
  classical
  unfold modifiedCentralizerResidual
  split_ifs with hL
  · exact le_embedded_residual_of_perfect (hX3 hL) htwo
  · exact htwo

/-- The exceptional modification is automatically three-perfect. -/
theorem modifiedCentralizerResidual_threePerfect [Finite G] {L : Subgroup G} (r : G)
    (hL : HasEvenLinearThreeType L) : IsPPerfect 3 (modifiedCentralizerResidual L r) := by
  classical
  rw [modifiedCentralizerResidual, if_pos hL]
  exact isPPerfect_embedded_pResidual 3 _

/-- Outside the exceptional case, two-perfectness is a general residual fact. -/
theorem modifiedCentralizerResidual_twoPerfect_of_nonexceptional [Finite G]
    {L : Subgroup G} (r : G) (hL : ¬ HasEvenLinearThreeType L) :
    IsPPerfect 2 (modifiedCentralizerResidual L r) := by
  classical
  rw [modifiedCentralizerResidual, if_neg hL]
  exact isPPerfect_embedded_pResidual 2 _

/-- The mutual-containment argument behind the common residual; the exceptional
two-perfectness inputs must be supplied by the local model calculations. -/
theorem common_residual_eq [Finite G] {L M : Subgroup G} {u i : G}
    (hu : u ∈ centralizer (M : Set G)) (hi : i ∈ centralizer (L : Set G))
    (hLuM : modifiedCentralizerResidual L u ≤ M)
    (hMiL : modifiedCentralizerResidual M i ≤ L)
    (hLu2 : IsPPerfect 2 (modifiedCentralizerResidual L u))
    (hMi2 : IsPPerfect 2 (modifiedCentralizerResidual M i))
    (hshape : HasEvenLinearThreeType L ↔ HasEvenLinearThreeType M) :
    modifiedCentralizerResidual L u = modifiedCentralizerResidual M i := by
  apply le_antisymm
  · apply le_modifiedCentralizerResidual hLuM _ hLu2
      (fun h => modifiedCentralizerResidual_threePerfect u (hshape.mpr h))
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hi x
        ((modifiedCentralizerResidual_le L u).trans
          ((involutionTwoResidual_le L u).trans inf_le_left) hx))
  · apply le_modifiedCentralizerResidual hMiL _ hMi2
      (fun h => modifiedCentralizerResidual_threePerfect i (hshape.mp h))
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hu x
        ((modifiedCentralizerResidual_le M i).trans
          ((involutionTwoResidual_le M i).trans inf_le_left) hx))

/-- Construct a single residual for all involutions in both commuting Sylow
subgroups, from cross-containment and two-perfectness. No equality is assumed. -/
theorem exists_common_residual [Finite G] {L M C R : Subgroup G}
    (hC : C ≤ centralizer (L : Set G)) (hR : R ≤ centralizer (M : Set G))
    (hu0 : ∃ u ∈ R, orderOf u = 2) (hi0 : ∃ i ∈ C, orderOf i = 2)
    (hforward : ∀ u ∈ R, orderOf u = 2 → modifiedCentralizerResidual L u ≤ M)
    (hbackward : ∀ i ∈ C, orderOf i = 2 → modifiedCentralizerResidual M i ≤ L)
    (hforward2 : ∀ u ∈ R, orderOf u = 2 → IsPPerfect 2 (modifiedCentralizerResidual L u))
    (hbackward2 : ∀ i ∈ C, orderOf i = 2 → IsPPerfect 2 (modifiedCentralizerResidual M i))
    (hshape : HasEvenLinearThreeType L ↔ HasEvenLinearThreeType M) :
    ∃ X : Subgroup G, X ≤ L ⊓ M ∧ R ⊔ C ≤ centralizer (X : Set G) ∧
      (∀ u ∈ R, orderOf u = 2 → modifiedCentralizerResidual L u = X) ∧
      (∀ i ∈ C, orderOf i = 2 → modifiedCentralizerResidual M i = X) := by
  obtain ⟨u0, huR, hu2⟩ := hu0
  obtain ⟨i0, hiC, hi2⟩ := hi0
  have heq : ∀ u ∈ R, orderOf u = 2 → ∀ i ∈ C, orderOf i = 2 →
      modifiedCentralizerResidual L u = modifiedCentralizerResidual M i := by
    intro u hu hu2 i hi hi2
    exact common_residual_eq (hR hu) (hC hi) (hforward u hu hu2)
      (hbackward i hi hi2) (hforward2 u hu hu2) (hbackward2 i hi hi2) hshape
  let X := modifiedCentralizerResidual L u0
  have hXL : X ≤ L := (modifiedCentralizerResidual_le L u0).trans
    ((involutionTwoResidual_le L u0).trans inf_le_left)
  have hXM : X ≤ M := hforward u0 huR hu2
  refine ⟨X, le_inf hXL hXM, ?_, ?_, ?_⟩
  · apply sup_le
    · exact hR.trans (centralizer_le hXM)
    · exact hC.trans (centralizer_le hXL)
  · intro u hu hu2'
    exact (heq u hu hu2' i0 hiC hi2).trans (heq u0 huR hu2 i0 hiC hi2).symm
  · intro i hi hi2'
    exact (heq u0 huR hu2 i hi hi2').symm

end CFSG.Quasithin.Chapter16.Intersections
