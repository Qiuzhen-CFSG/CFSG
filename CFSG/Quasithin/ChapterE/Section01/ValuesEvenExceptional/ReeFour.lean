module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.Ambient
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.BinaryUpper
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.PositiveUpper
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction

/-!
# The derived Ree-four value in E.1.14(1)

The actual derived Ree model gives even ambient order for every parameter.
At positive parameters the source group G = F*(G)T is proved isomorphic to
the full Ree model. Its two marked local factors give E-generation at the
field exponent 2*m+1. The conjugacy family of full long-root groups has a
proper weak-closure normalizer containing every E-member at rank 2*m.
Monotonicity excludes every smaller bound, giving the exact source minimum.

At m = 0, both the Tits derived group and its full Ree extension are retained.
Their actual solvable Sylow overgroups prove rank-one generation; even order
then gives the positive value one. The result uses only finiteness, simplicity
of F*(G), G = F*(G)T and the actual derived-model equivalence. No additional
SQTK hypothesis is needed. `generation_inputs` supplies the concrete parity,
upper and lower inputs to the parent exceptional-value assembly, and
`generationParameter_eq` completes their minimum calculation here.

Source: Aschbacher–Smith E.1.14(1), printed p.214 (PDF p.225) of
`refs/quasithin.pdf`, citing Aschbacher, GF(2)-representations of finite
groups (1982), Lemma 4.7. The quotient ranks and the local tau convention
are those of E.1.2 and E.1.5, not the older definition in that article.
-/

public section

namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour

open Subgroup Theory.GroupTheory ReeF4

variable {G : Type*} [Group G] [Finite G]

/-- An upper bound on the genuine positive-parameter model applies to the
whole source group, using the proved elimination of its outer extension. -/
theorem isEGenerated_of_positive_model_bound (T : Sylow 2 G)
    (L : Subgroup G) (hL : L = generalizedFitting G)
    (hgen : L ⊔ (T : Subgroup G) = ⊤) {m : ℕ} (hm : 0 < m)
    (e : L ≃* commutator (Model m)) {i : ℕ}
    (hupper : IsEGenerated i (Model m)) : IsEGenerated i G :=
  hupper.map_equiv (positiveAmbientEquiv T L hL hgen hm e).symm

/-- A model lower bound also survives passage to the whole source group. -/
theorem not_isEGenerated_of_positive_model_bound (T : Sylow 2 G)
    (L : Subgroup G) (hL : L = generalizedFitting G)
    (hgen : L ⊔ (T : Subgroup G) = ⊤) {m : ℕ} (hm : 0 < m)
    (e : L ≃* commutator (Model m)) {i : ℕ}
    (hlower : ¬ IsEGenerated i (Model m)) : ¬ IsEGenerated i G := by
  intro h
  exact hlower (h.map_equiv (positiveAmbientEquiv T L hL hgen hm e))

/-- Once upper generation is proved for an ambient group containing the
binary derived model, its parameter is one, rather than an unattained zero. -/
theorem binary_generationParameter_eq_one_of_upper (L : Subgroup G)
    (e : L ≃* commutator (Model 0)) (hupper : IsEGenerated 1 G) :
    generationParameter G = 1 := by
  have heven := even_card_of_subgroup_derived_equiv L e
  have hpos := (generationParameter_spec (Nat.not_odd_iff_even.mpr heven)
    ⟨1, by omega, hupper⟩).1
  have hle := generationParameter_le (by omega : 0 < 1) hupper
  omega

/-- The derived Ree upper bound for the whole source group, at every parameter.
The binary branch includes the Tits group and its full Ree extension. -/
theorem isEGenerated_of_derived_socle (T : Sylow 2 G)
    (L : Subgroup G) (hL : L = generalizedFitting G)
    (hgen : L ⊔ (T : Subgroup G) = ⊤) {m : ℕ}
    (e : L ≃* commutator (Model m)) : IsEGenerated (2 * m + 1) G := by
  by_cases hm : m = 0
  · subst m
    exact binary_isEGenerated_one L hL e
  · exact positive_isEGenerated T L hL hgen (Nat.pos_of_ne_zero hm) e

/-- The binary parameter is one in both ambient cases. Its upper bound is
proved from the actual solvable parabolics, and even order ensures positivity. -/
theorem binary_generationParameter_eq_one (L : Subgroup G)
    (hL : L = generalizedFitting G) (e : L ≃* commutator (Model 0)) :
    generationParameter G = 1 :=
  binary_generationParameter_eq_one_of_upper L e (binary_isEGenerated_one L hL e)

/-- The complete Ree inputs for E.1.14(1) in G = F*(G)T. At positive m the
family and proper subgroup are constructed from the actual long-root geometry,
with both E1 and E2 confinement premises discharged. At m = 0 parity and the
upper bound suffice. No generation or confinement premise remains. -/
theorem generation_inputs (T : Sylow 2 G) (L : Subgroup G) [IsSimpleGroup L]
    (hL : L = generalizedFitting G) (hgen : L ⊔ (T : Subgroup G) = ⊤) {m : ℕ}
    (e : L ≃* commutator (Model m)) :
    ¬ Odd (Nat.card G) ∧ IsEGenerated (2 * m + 1) G ∧
      (0 < m → ∃ (Ω : Set (Subgroup G)) (M : Subgroup G),
        IsElementaryFamily Ω ∧ M ≠ ⊤ ∧
        normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M ∧
        ∀ A : Subgroup G, A ∈ Ω → A ≤ (T : Subgroup G) →
          ∀ K : Subgroup G, IsEMemberAt (2 * m) (T : Subgroup G) A K → K ≤ M) :=
  ⟨Nat.not_odd_iff_even.mpr (even_card_of_subgroup_derived_equiv L e),
    isEGenerated_of_derived_socle T L hL hgen e,
    fun hm => LowerObstruction.exists_source_obstruction T L hL hgen hm e⟩

/-- E.1.14(1) for the genuine derived Ree carrier at every parameter m ≥ 0.
The equality concerns the original ambient group, including both binary cases,
and attains the source's least positive generation bound. -/
theorem generationParameter_eq (T : Sylow 2 G) (L : Subgroup G) [IsSimpleGroup L]
    (hL : L = generalizedFitting G) (hgen : L ⊔ (T : Subgroup G) = ⊤) {m : ℕ}
    (e : L ≃* commutator (Model m)) : generationParameter G = 2 * m + 1 := by
  obtain ⟨heven, hupper, hlower⟩ := generation_inputs T L hL hgen e
  have hpos : 0 < 2 * m + 1 := by omega
  have hspec := generationParameter_spec heven ⟨2 * m + 1, hpos, hupper⟩
  apply Nat.le_antisymm (generationParameter_le hpos hupper)
  by_cases hm : m = 0
  · omega
  · by_contra h
    obtain ⟨Ω, M, hΩ, hM, hnorm, hmembers⟩ := hlower (Nat.pos_of_ne_zero hm)
    obtain ⟨A, hA, hAT, K, hK, hKM⟩ :=
      ((hspec.2 T).mono (show generationParameter G ≤ 2 * m by omega)).exists_member_not_le
        Ω hΩ M hM hnorm
    exact hKM (hmembers A hA hAT K hK)

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour
