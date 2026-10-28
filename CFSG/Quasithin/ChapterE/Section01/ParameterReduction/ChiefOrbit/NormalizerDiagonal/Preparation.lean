module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalAction
public import Theory.GroupTheory.ChiefFactorDirectPower.Escape
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The escaping chief section in the local normalizer

Write S = N_T(J), W₀ for the weak closure of the literal intersection family,
and J₀ = N_J(W₀). If W ≤ S, then W ≤ W₀ ≤ T. Weak closure of W in T therefore
implies N_G(W₀) ≤ N_G(W), which suffices for the source contradiction without
an equality between the two weak closures.

Otherwise a member A of Ω contained in T escapes S. Work in D = J₀S, where
both J₀ and W₀ are normal and S is Sylow. The normal core of J₀ ∩ M in D is
the largest S-invariant normal subgroup of J₀ contained in M. A chief section
above it escapes M and is not a two-group. Its image is centralized by W₀,
since the commutator lies in the normal core. None of these subgroups is
asserted normal in the original ambient group G.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed pp.213--214.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem weakClosure_le_localWeakClosure (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hW : weakClosure (T : Subgroup G) Ω ≤ stabilizer T J) :
    weakClosure (T : Subgroup G) Ω ≤ localWeakClosure T J Ω := by
  rw [localWeakClosure_eq]
  apply sSup_le
  rintro A ⟨hA, hAT⟩
  have hAW : A ≤ weakClosure (T : Subgroup G) Ω := le_sSup ⟨hA, hAT⟩
  have hAS : A ≤ stabilizer T J := hAW.trans hW
  have hAH : A ≤ localGroup T J := hAS.trans le_sup_right
  apply le_sSup
  exact ⟨⟨A, hA, inf_eq_left.mpr hAH⟩, hAS⟩

theorem localWeakClosure_normalizer_le (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hW : weakClosure (T : Subgroup G) Ω ≤ stabilizer T J) :
    normalizer (localWeakClosure T J Ω : Set G) ≤
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply SubgroupFamily.span_weakly_closed hΩ.conjugationInvariant
  exact (map_mono (weakClosure_le_localWeakClosure T J hW)).trans
    ((mem_normalizer_iff_map_conj_eq.mp hg).le.trans
      ((localWeakClosure_le T J Ω).trans inf_le_left))

theorem localNormalizer_le_of_weakClosure_le {n : ℕ} (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hW : weakClosure (T : Subgroup G) Ω ≤ stabilizer T J) :
    localNormalizer T J Ω ≤ generationTarget n T Ω :=
  (inf_le_right.trans (localWeakClosure_normalizer_le T J hΩ hW)).trans le_sup_right

theorem exists_member_not_le_stabilizer {n : ℕ} (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hnot : ¬ localNormalizer T J Ω ≤ generationTarget n T Ω) :
    ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ ¬ A ≤ stabilizer T J := by
  classical
  by_contra! h
  apply hnot
  apply localNormalizer_le_of_weakClosure_le T J hΩ
  exact sSup_le (fun A hA => h A hA.1 hA.2)

omit [Finite G] in
theorem inf_stabilizer_le_localWeakClosure (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} {A : Subgroup G} (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G)) :
    A ⊓ stabilizer T J ≤ localWeakClosure T J Ω := by
  rw [localWeakClosure_eq]
  have he : A ⊓ localGroup T J = A ⊓ stabilizer T J := by
    rw [← inf_localGroup T J, ← inf_assoc, inf_eq_left.mpr hAT]
  apply le_sSup
  exact ⟨⟨A, hA, he⟩, inf_le_right⟩

theorem stabilizer_le_localNormalizer_normalizer (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    stabilizer T J ≤ normalizer (localNormalizer T J Ω : Set G) := by
  apply le_trans _ inf_normalizer_le_normalizer_inf
  exact le_inf inf_le_right
    ((stabilizer_le_localWeakClosure_normalizer T J hΩ).trans (normalizer _).le_normalizer)

def normalizerGroup (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G)) :
    Subgroup G := localNormalizer T J Ω ⊔ stabilizer T J

omit [Finite G] in
theorem normalizerGroup_le_localGroup (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) : normalizerGroup T J Ω ≤ localGroup T J :=
  sup_le (inf_le_left.trans le_sup_left) le_sup_right

omit [Finite G] in
theorem inf_normalizerGroup (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G)) :
    (T : Subgroup G) ⊓ normalizerGroup T J Ω = stabilizer T J := by
  apply le_antisymm
  · exact (inf_le_inf_left _ (normalizerGroup_le_localGroup T J Ω)).trans
      (inf_localGroup T J).le
  · exact le_inf inf_le_left le_sup_right

theorem localNormalizer_normal (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    ((localNormalizer T J Ω).subgroupOf (normalizerGroup T J Ω)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
  exact sup_le (localNormalizer T J Ω).le_normalizer
    (stabilizer_le_localNormalizer_normalizer T J hΩ)

theorem localWeakClosure_normal (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    ((localWeakClosure T J Ω).subgroupOf (normalizerGroup T J Ω)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    ((localWeakClosure_le T J Ω).trans le_sup_right)).mpr
  exact sup_le inf_le_right (stabilizer_le_localWeakClosure_normalizer T J hΩ)

theorem localWeakClosure_le_pCore_normalizerGroup (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    (localWeakClosure T J Ω).subgroupOf (normalizerGroup T J Ω) ≤
      pCore 2 (normalizerGroup T J Ω) := by
  apply le_sSup
  exact ⟨localWeakClosure_normal T J hΩ,
    (T.isPGroup'.to_le ((localWeakClosure_le T J Ω).trans inf_le_left)).comap_subtype⟩

theorem exists_normalizerSylow (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) (hJ : J.IsSubnormal) :
    ∃ R : Sylow 2 (normalizerGroup T J Ω),
      (R : Subgroup (normalizerGroup T J Ω)) =
        (stabilizer T J).subgroupOf (normalizerGroup T J Ω) := by
  obtain ⟨P, hP⟩ := exists_localSylow T J hJ
  let f := inclusion (normalizerGroup_le_localGroup T J Ω)
  have hf : (P : Subgroup (localGroup T J)) ≤ f.range := by
    intro x hx
    rw [hP] at hx
    exact ⟨⟨x.val, mem_sup_right hx⟩, rfl⟩
  refine ⟨P.comapOfInjective f (inclusion_injective _) hf, ?_⟩
  change (P : Subgroup (localGroup T J)).comap f = _
  rw [hP]
  rfl

omit [Finite G] in
/-- An elementary member escaping the component stabilizer has an actual
nontrivial complement with trivial stabilizer on the component orbit. -/
theorem exists_component_complement (T : Sylow 2 G) (J : Subgroup G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hAS : ¬ A ≤ stabilizer T J) :
    ∃ Z : Subgroup G, Z ≤ A ∧ (A ⊓ stabilizer T J) ⊔ Z = A ∧
      Disjoint Z (normalizer (J : Set G)) ∧ Z ≠ ⊥ := by
  obtain ⟨Z, hZ⟩ := IsElementaryAbelian.exists_isCompl 2 A
    ((stabilizer T J).subgroupOf A)
  have hsup : (A ⊓ stabilizer T J) ⊔ Z.map A.subtype = A := by
    have hm := congrArg (map A.subtype) hZ.sup_eq_top
    simpa only [Subgroup.map_sup, subgroupOf_map_subtype, inf_comm, ← MonoidHom.range_eq_map,
      range_subtype] using hm
  have hdis : Disjoint (Z.map A.subtype) (normalizer (J : Set G)) := by
    apply disjoint_def.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    have hzS : z ∈ (stabilizer T J).subgroupOf A := ⟨hAT z.property, hx⟩
    have hz1 := disjoint_def.mp hZ.disjoint hzS hz
    exact congrArg Subtype.val hz1
  refine ⟨Z.map A.subtype, map_subtype_le Z, hsup, hdis, ?_⟩
  intro he
  apply hAS
  have hle := hsup.symm.le
  rw [he, sup_bot_eq] at hle
  exact hle.trans inf_le_right


end CFSG.Quasithin.ChapterE.ChiefOrbit

namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

def normalizerKernel (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) : Subgroup (normalizerGroup T J Ω) :=
  ((localNormalizer T J Ω).subgroupOf (normalizerGroup T J Ω) ⊓
    (generationTarget n T Ω).subgroupOf (normalizerGroup T J Ω)).normalCore

instance normalizerKernel_normal (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) : (normalizerKernel n T J Ω).Normal :=
  normalCore_normal _

theorem normalizerKernel_le_localNormalizer (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) :
    normalizerKernel n T J Ω ≤
      (localNormalizer T J Ω).subgroupOf (normalizerGroup T J Ω) :=
  normalCore_le _ |>.trans inf_le_left

theorem normalizerKernel_le_target (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) :
    normalizerKernel n T J Ω ≤
      (generationTarget n T Ω).subgroupOf (normalizerGroup T J Ω) :=
  normalCore_le _ |>.trans inf_le_right

theorem normalizerKernel_maximal (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    (Ω : Set (Subgroup G)) (Y : Subgroup (normalizerGroup T J Ω)) [Y.Normal]
    (hYJ : Y ≤ (localNormalizer T J Ω).subgroupOf (normalizerGroup T J Ω))
    (hYM : Y.map (normalizerGroup T J Ω).subtype ≤ generationTarget n T Ω) :
    Y ≤ normalizerKernel n T J Ω :=
  normal_le_normalCore.mpr (le_inf hYJ (map_le_iff_le_comap.mp hYM))

theorem exists_escaping_chiefSection {n : ℕ} (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) (hJ : J.IsSubnormal)
    (hnot : ¬ localNormalizer T J Ω ≤ generationTarget n T Ω) :
    ∃ X : Subgroup (normalizerGroup T J Ω),
      ChiefFactor.IsChief X (normalizerKernel n T J Ω) ∧
      X ≤ (localNormalizer T J Ω).subgroupOf (normalizerGroup T J Ω) ∧
      ¬ X.map (normalizerGroup T J Ω).subtype ≤ generationTarget n T Ω ∧
      ¬ IsPGroup 2 (X ⧸ (normalizerKernel n T J Ω).subgroupOf X) := by
  let D := normalizerGroup T J Ω
  let N := (localNormalizer T J Ω).subgroupOf D
  let M := (generationTarget n T Ω).subgroupOf D
  let _ : N.Normal := localNormalizer_normal T J hΩ
  have hNM : ¬ N ≤ M := by
    intro h
    apply hnot
    have hh := map_mono (f := D.subtype) h
    rw [map_subgroupOf_eq_of_le (show localNormalizer T J Ω ≤ D from le_sup_left)] at hh
    rw [subgroupOf_map_subtype] at hh
    exact hh.trans inf_le_left
  obtain ⟨X, hchief, hXN, hXM⟩ := ChiefFactor.exists_chief_not_le N M hNM
  let _ := hchief.normal_upper
  obtain ⟨R, hR⟩ := exists_normalizerSylow T J Ω hJ
  have hRM : (R : Subgroup D) ≤ M := by
    rw [hR]
    intro x hx
    exact (sylow_le_weakClosure_normalizer T hΩ).trans le_sup_right hx.1
  refine ⟨X, hchief, hXN, ?_, ?_⟩
  · exact fun h => hXM (map_le_iff_le_comap.mp h)
  · exact ChiefFactor.not_isPGroup_of_not_le R X (normalizerKernel n T J Ω) M
      hRM (normalizerKernel_le_target n T J Ω) hXM

theorem commutator_localWeakClosure_le_kernel (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (X : Subgroup (normalizerGroup T J Ω)) [X.Normal]
    (hXJ : X ≤ (localNormalizer T J Ω).subgroupOf (normalizerGroup T J Ω)) :
    ⁅X, (localWeakClosure T J Ω).subgroupOf (normalizerGroup T J Ω)⁆ ≤
      normalizerKernel n T J Ω := by
  let W := (localWeakClosure T J Ω).subgroupOf (normalizerGroup T J Ω)
  let _ : W.Normal := localWeakClosure_normal T J hΩ
  apply normal_le_normalCore.mpr
  refine le_inf ((commutator_le_left X W).trans hXJ) ?_
  apply (commutator_le_right X W).trans
  intro x hx
  exact ((localWeakClosure_le T J Ω).trans inf_le_left |>.trans
    (sylow_le_weakClosure_normalizer T hΩ) |>.trans le_sup_right) hx

theorem quotient_localWeakClosure_centralizes (n : ℕ) (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (X : Subgroup (normalizerGroup T J Ω)) [X.Normal]
    (hXJ : X ≤ (localNormalizer T J Ω).subgroupOf (normalizerGroup T J Ω)) :
    ((localWeakClosure T J Ω).subgroupOf (normalizerGroup T J Ω)).map
        (QuotientGroup.mk' (normalizerKernel n T J Ω)) ≤
      centralizer (X.map (QuotientGroup.mk' (normalizerKernel n T J Ω)) :
        Set ((normalizerGroup T J Ω) ⧸ normalizerKernel n T J Ω)) := by
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [← map_commutator]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  exact commutator_localWeakClosure_le_kernel n T J hΩ X hXJ

end CFSG.Quasithin.ChapterE.ChiefOrbit
