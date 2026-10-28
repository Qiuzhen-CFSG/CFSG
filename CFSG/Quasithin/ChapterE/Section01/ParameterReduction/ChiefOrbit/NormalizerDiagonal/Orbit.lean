module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Preparation
public import Theory.GroupTheory.GeneralizedFitting.ComponentOrbitKernel

/-!
# The residual orbit and its actual product kernel

For a section X/Y in D = J₀S, define K₁ by mapping the intrinsic O²(X) into G,
Y₁ = K₁ ∩ Y, H as the join of the actual T-conjugates of K₁, and H₀ as the
join of the corresponding conjugates of Y₁. Then H₀ is normal in K₁T = HT
and lies in the ambient generation target. Normality is relative to HT.

A chief section which is not a two-group is covered by K₁ modulo Y. Therefore
containing H in the generation target contradicts the escaping section. These
are the literal quotient and residual conventions used by the two remaining
chief-section cases; no direct-product isomorphism is assumed or asserted here.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed pp.213--214.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

def normalizerSeed (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G))
    (X : Subgroup (normalizerGroup T J Ω)) : Subgroup G :=
  ((pResidual 2 X).map X.subtype).map (normalizerGroup T J Ω).subtype

def normalizerSeedKernel (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) (X : Subgroup (normalizerGroup T J Ω)) : Subgroup G :=
  normalizerSeed T J Ω X ⊓ (normalizerKernel n T J Ω).map (normalizerGroup T J Ω).subtype

def normalizerOrbit (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G))
    (X : Subgroup (normalizerGroup T J Ω)) : Subgroup G :=
  componentOrbit (normalizerSeed T J Ω X) (T : Subgroup G)

def normalizerOrbitKernel (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) (X : Subgroup (normalizerGroup T J Ω)) : Subgroup G :=
  componentOrbit (normalizerSeedKernel n T J Ω X) (T : Subgroup G)

def normalizerOrbitGroup (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G))
    (X : Subgroup (normalizerGroup T J Ω)) : Subgroup G :=
  normalizerSeed T J Ω X ⊔ (T : Subgroup G)

theorem normalizerSeed_eq_ambient_residual (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) (X : Subgroup (normalizerGroup T J Ω)) :
    normalizerSeed T J Ω X =
      (pResidual 2 (X.map (normalizerGroup T J Ω).subtype)).map
        (X.map (normalizerGroup T J Ω).subtype).subtype :=
  map_embedded_pResidual 2 X (normalizerGroup T J Ω).subtype

omit [Finite G] in
theorem normalizerSeed_le (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G))
    (X : Subgroup (normalizerGroup T J Ω)) :
    normalizerSeed T J Ω X ≤ X.map (normalizerGroup T J Ω).subtype :=
  map_mono (map_subtype_le _)

omit [Finite G] in
private theorem normal_map_normalized (D : Subgroup G) (X : Subgroup D) [X.Normal] :
    D ≤ normalizer (X.map D.subtype : Set G) := by
  have h := le_normalizer_map D.subtype (H := X)
  rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h

omit [Finite G] in
theorem stabilizer_normalizes_normalizerSeed (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) (X : Subgroup (normalizerGroup T J Ω)) [X.Normal] :
    stabilizer T J ≤ normalizer (normalizerSeed T J Ω X : Set G) :=
  le_sup_right.trans (normal_map_normalized (normalizerGroup T J Ω)
    ((pResidual 2 X).map X.subtype))

theorem normalizerSeedKernel_le_target (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) (X : Subgroup (normalizerGroup T J Ω)) :
    normalizerSeedKernel n T J Ω X ≤ generationTarget n T Ω :=
  inf_le_right.trans (map_le_iff_le_comap.mpr (normalizerKernel_le_target n T J Ω))

theorem normalizerSeed_normalizes_kernel (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) (X : Subgroup (normalizerGroup T J Ω)) :
    normalizerSeed T J Ω X ≤ normalizer (normalizerSeedKernel n T J Ω X : Set G) := by
  exact (le_inf (normalizerSeed T J Ω X).le_normalizer
    ((map_subtype_le _).trans (normal_map_normalized _ _))).trans
      inf_normalizer_le_normalizer_inf

theorem stabilizer_normalizes_normalizerSeedKernel (n : ℕ) (T : Sylow 2 G)
    (J : Subgroup G) (Ω : Set (Subgroup G))
    (X : Subgroup (normalizerGroup T J Ω)) [X.Normal] :
    stabilizer T J ≤ normalizer (normalizerSeedKernel n T J Ω X : Set G) := by
  exact (le_inf (stabilizer_normalizes_normalizerSeed T J Ω X)
    (le_sup_right.trans (normal_map_normalized (normalizerGroup T J Ω)
      (normalizerKernel n T J Ω)))).trans
      inf_normalizer_le_normalizer_inf

theorem normalizerOrbitKernel_le_orbit (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) (X : Subgroup (normalizerGroup T J Ω)) :
    normalizerOrbitKernel n T J Ω X ≤ normalizerOrbit T J Ω X :=
  iSup_mono fun _ => map_mono inf_le_left

omit [Finite G] in
theorem normalizerOrbit_sup (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G))
    (X : Subgroup (normalizerGroup T J Ω)) :
    normalizerOrbit T J Ω X ⊔ (T : Subgroup G) = normalizerOrbitGroup T J Ω X :=
  componentOrbit_sup _ _

omit [Finite G] in
theorem normalizerOrbit_normal (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) (X : Subgroup (normalizerGroup T J Ω)) :
    ((normalizerOrbit T J Ω X).subgroupOf (normalizerOrbitGroup T J Ω X)).Normal :=
  componentOrbit_normal_subgroupOf_sup _ _

theorem normalizerOrbitKernel_normal (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (X : Subgroup (normalizerGroup T J Ω)) [X.Normal]
    (hXJ : X ≤ (localNormalizer T J Ω).subgroupOf (normalizerGroup T J Ω))
    (hJ : IsComponent G J) :
    ((normalizerOrbitKernel n T J Ω X).subgroupOf (normalizerOrbitGroup T J Ω X)).Normal := by
  have hseedJ : normalizerSeed T J Ω X ≤ J :=
    (normalizerSeed_le T J Ω X).trans ((map_le_iff_le_comap.mpr hXJ).trans inf_le_left)
  exact hJ.normal_local_kernel_orbit hseedJ inf_le_left
    (normalizerSeed_normalizes_kernel n T J Ω X)
    (stabilizer_normalizes_normalizerSeedKernel n T J Ω X)

theorem normalizerOrbitKernel_le_target (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (X : Subgroup (normalizerGroup T J Ω)) :
    normalizerOrbitKernel n T J Ω X ≤ generationTarget n T Ω :=
  (componentOrbit_le_sup _ _).trans (sup_le (normalizerSeedKernel_le_target n T J Ω X)
    ((sylow_le_weakClosure_normalizer T hΩ).trans le_sup_right))

theorem escaping_section_covered_by_seed {n : ℕ} (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (X : Subgroup (normalizerGroup T J Ω))
    (hX : ChiefFactor.IsChief X (normalizerKernel n T J Ω))
    (h2 : ¬ IsPGroup 2 (X ⧸ (normalizerKernel n T J Ω).subgroupOf X)) :
    X.map (normalizerGroup T J Ω).subtype =
      normalizerSeed T J Ω X ⊔
        (normalizerKernel n T J Ω).map (normalizerGroup T J Ω).subtype := by
  have he := congrArg (map (normalizerGroup T J Ω).subtype)
    (hX.embedded_pResidual_sup_eq h2)
  exact (Subgroup.map_sup _ _ _).symm.trans he |>.symm

theorem escaping_section_le_of_orbit_le {n : ℕ} (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (X : Subgroup (normalizerGroup T J Ω))
    (hX : ChiefFactor.IsChief X (normalizerKernel n T J Ω))
    (h2 : ¬ IsPGroup 2 (X ⧸ (normalizerKernel n T J Ω).subgroupOf X))
    (hH : normalizerOrbit T J Ω X ≤ generationTarget n T Ω) :
    X.map (normalizerGroup T J Ω).subtype ≤ generationTarget n T Ω := by
  rw [escaping_section_covered_by_seed T J X hX h2]
  exact sup_le ((le_componentOrbit _ _).trans hH)
    (map_le_iff_le_comap.mpr (normalizerKernel_le_target n T J Ω))

end CFSG.Quasithin.ChapterE.ChiefOrbit
