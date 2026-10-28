module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction.Family
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction.ComponentRank
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction.OddConfinement
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction.WeakClosure
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The nonbinary G₂ lower obstruction

For an actual derived-model equivalence at q = 2^f, f > 1, perfectness first
identifies the derived carrier with the full octonion model. Sylow conjugacy
then aligns the model with T intersect L. The highest-root conjugacy family
is elementary, has a member in T, and has nontrivial weak closure with proper
normalizer. Its normalizer is precisely the embedded short parabolic joined
with T, including all outer two-actions permitted by G = LT.

Scalar saturation of two-core displacements excludes the E₁ branch and makes
the literal E₂ radical-quotient image have rank f. Thus every E-member at
rank at most f-1 lies in the proper short overgroup. This constructs the
family and confinement witnesses, and excludes E-generation below f without
assuming any family, geometric witness or failure of generation. SQTK is not
needed for this lower obstruction.

Source: Aschbacher--Smith E.1.1--6 and E.1.14(1), printed pp.209--210 and 214,
the latter citing Asc82a Lemma 4.7. The independent upper bound and the final
minimum calculation remain with the parent G₂ assembly. The actual octonion
model comes from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Theory.GroupTheory
variable {G F : Type*} [Group G] [Field F] [Finite G] [Finite F]

/-- The actual derived-model hypothesis constructs the elementary family and
its proper weak-closure normalizer. The E-member confinement is not assumed
or asserted by this preparatory theorem. -/
theorem exists_aligned_root_family (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (T : Sylow 2 G) {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : L ≃* commutator (Model F)) :
    ∃ a : L ≃* Model F,
      ((T : Subgroup G).subgroupOf L).map a.toMonoidHom = unipotent ∧
      IsElementaryFamily (family L a) ∧
      root L a ∈ family L a ∧ root L a ≤ (T : Subgroup G) ∧
      weakClosure (T : Subgroup G) (family L a) ≠ ⊥ ∧
      normalizer (weakClosure (T : Subgroup G) (family L a) : Set G) ≠ ⊤ ∧
      (T : Subgroup G) ≤ normalizer
        (weakClosure (T : Subgroup G) (family L a) : Set G) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨a, ha⟩ := exists_aligned_equiv L T
    (e.trans (DerivedEvenOrder.derivedEquivModel hf hF))
  have hq : 1 < Nat.card F := by
    rw [hF]
    exact Nat.one_lt_pow (by omega) (by decide)
  exact ⟨a, ha, family_elementary L a, root_mem_family L a,
    root_le_of_aligned L T a ha, weakClosure_ne_bot L T a ha hq,
    weakClosure_normalizer_ne_top L T a ha hq, le_weakClosure_normalizer L T a⟩

/-- Apply the family construction to the literal generalized Fitting subgroup
in E.1.14. This preparatory conclusion does not need G = LT or SQTK. -/
theorem exists_source_family (T : Sylow 2 G)
    [IsSimpleGroup (generalizedFitting G)] {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f)
    (e : generalizedFitting G ≃* commutator (Model F)) :
    ∃ (Ω : Set (Subgroup G)) (M : Subgroup G),
      IsElementaryFamily Ω ∧ M ≠ ⊤ ∧
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M ∧
      (T : Subgroup G) ≤ M ∧ weakClosure (T : Subgroup G) Ω ≠ ⊥ := by
  obtain ⟨a, _, hΩ, _, _, hW, hM, hT⟩ :=
    exists_aligned_root_family (generalizedFitting G) T hf hF e
  exact ⟨family (generalizedFitting G) a, _, hΩ, hM, le_rfl, hT, hW⟩

/-- Combine both genuine E.1.5 branches with their own intrinsic quotient
ranks. Normality of the model copy includes every ambient outer two-extension. -/
theorem member_le_shortOvergroup [CharP F 2]
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G) (e : L ≃* Model F)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    {A K : Subgroup G} (hA : A ∈ family L e)
    (hK : IsEMemberAt (f - 1) (T : Subgroup G) A K) :
    K ≤ shortOvergroup L (T : Subgroup G) e := by
  obtain ⟨hm, ho | hc⟩ := hK
  · exact odd_member_le_shortOvergroup L T e hf hF hA hm ho.1
  · exact ComponentRank.confinement L (T : Subgroup G) e hA hm hc.1
      (by omega) hF hc.2

/-- The complete lower-obstruction witness for the G₂ case of E.1.14(1).
The family is the full G-orbit of an aligned highest-root group, and M is
the embedded short parabolic joined with T. Both are constructed from the
actual derived-model equivalence; no confinement or geometry premise remains. -/
theorem exists_lower_obstruction (T : Sylow 2 G)
    [IsSimpleGroup (generalizedFitting G)]
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : generalizedFitting G ≃* commutator (Model F)) :
    ∃ (Ω : Set (Subgroup G)) (M : Subgroup G),
      IsElementaryFamily Ω ∧ M ≠ ⊤ ∧
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M ∧
      ∀ A : Subgroup G, A ∈ Ω → A ≤ (T : Subgroup G) →
        ∀ K : Subgroup G, IsEMemberAt (f - 1) (T : Subgroup G) A K → K ≤ M := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨a, ha, hΩ, _, _, _, hM, _⟩ :=
    exists_aligned_root_family (generalizedFitting G) T hf hF e
  obtain ⟨_, hnorm⟩ := weakClosure_geometry (generalizedFitting G) T hLT a ha hf hF
  refine ⟨family (generalizedFitting G) a,
    shortOvergroup (generalizedFitting G) (T : Subgroup G) a,
    hΩ, ?_, hnorm.le, ?_⟩
  · rwa [← hnorm]
  · intro A hA _ K hK
    exact member_le_shortOvergroup (generalizedFitting G) T a hf hF hA hK

/-- The constructed obstruction excludes every smaller generation bound for
the whole source ambient group. The upper-bound owner can now determine the
minimum using the independent generation theorem. -/
theorem not_isEGenerated_below (T : Sylow 2 G)
    [IsSimpleGroup (generalizedFitting G)]
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : generalizedFitting G ≃* commutator (Model F))
    {i : ℕ} (hi : i < f) : ¬ IsEGenerated i G := by
  obtain ⟨Ω, M, hΩ, hM, hnorm, hmembers⟩ := exists_lower_obstruction T hLT hf hF e
  intro hgen
  obtain ⟨A, hA, hAT, K, hK, hKM⟩ :=
    ((hgen T).mono (show i ≤ f - 1 by omega)).exists_member_not_le Ω hΩ M hM hnorm
  exact hKM (hmembers A hA hAT K hK)

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction
