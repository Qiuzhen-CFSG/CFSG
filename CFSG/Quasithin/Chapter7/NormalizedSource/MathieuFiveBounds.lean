module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM23CodeBounds
public import Theory.Representation.Mathieu.SmallModules.Models
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneThompson

/-!
# The initial codimension bound for large Mathieu code and cocode

If a nontrivial elementary actor has fixed codimension at most four, all its
nonidentity elements have the same fixed space, since involutions move at least
four dimensions. The actor is therefore quadratic and has rank at most two.
Consequently an (F-1)-offender moves at least five dimensions. Actual group and
linear markings transport this calculation to both M23 and M24 rows.

The native odd-prime spectrum gives displacement at least six. These two
bounds control the actual local Cartan parameter and higher Thompson subgroup
in the companion chosen-orbit application of E.6.27. This proves the initial
bound r ≥ 5; the stronger cocode estimates in 8.1.2 require the additional
distinguished-vector centralizer argument.

Source: Aschbacher--Smith, Table7.2.1 and7.4.1, printed pp.698,700;
H.14.4,H.15.2,H.15.7 andH.16, pp.397--405.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE ChapterB Sporadic.Mathieu MathieuCode

private theorem nearOffender_five_of_involution_quadratic
    {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (ρ : Representation (ZMod 2) A E)
    (hinv : ∀ a : A, orderOf a = 2 → 4 ≤ fixedCodim ρ (zpowers a))
    (hquad : ∀ B : Subgroup A, IsElementaryTwo B → IsQuadratic ρ B → rank B ≤ 2)
    (B : Subgroup A) (hB : IsElementaryTwo B)
    (hnear : fixedCodim ρ B ≤ rank B + 1) : 5 ≤ fixedCodim ρ B := by
  let := hB.2
  by_contra hlt
  have hsmall : fixedCodim ρ B ≤ 4 := by omega
  have hsame : ∀ a ∈ B, a ≠ 1 → fixedCodim ρ B = fixedCodim ρ (zpowers a) := by
    intro a ha ha1
    have ho : orderOf a = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
    have hm := fixedCodim_mono ρ (zpowers_le.mpr ha)
    have hl := hinv a ho
    omega
  have hr := hquad B hB (isQuadratic_of_common_fixedCodim ρ hsame)
  obtain ⟨a,ha,ha1⟩ := B.bot_or_exists_ne_one.resolve_left hB.1
  have ho : orderOf a = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hl := (hinv a ho).trans (fixedCodim_mono ρ (zpowers_le.mpr ha))
  omega

private theorem m24_cocode_involution_ge_four (a : M24) (ha : orderOf a = 2) :
    4 ≤ fixedCodim cocodeRepresentation (zpowers a) := by
  rcases M24InvolutionCentralizers.involution_classes a ha with hz | ht
  · rw [CocodeOctad.Involutions.fixedCodim_of_isConj_z a hz]
  · rw [CocodeOctad.Involutions.fixedCodim_of_isConj_t a ht]
    decide

private theorem m24_nearOffender_five_code (A : Subgroup M24) (hA : IsElementaryTwo A)
    (hnear : fixedCodim codeRepresentation A ≤ rank A + 1) :
    5 ≤ fixedCodim codeRepresentation A := by
  apply nearOffender_five_of_involution_quadratic codeRepresentation _ _ A hA hnear
  · intro a ha
    rw [code_cocode_fixedCodim_zpowers]
    exact m24_cocode_involution_ge_four a ha
  · intro B hB hq
    let := hB.2
    exact (Nat.log_mono_right (QuadraticActors.m24_code_card_le_four B hq)).trans
      (by decide : Nat.log 2 4 ≤ 2)

private theorem m24_nearOffender_five_cocode (A : Subgroup M24) (hA : IsElementaryTwo A)
    (hnear : fixedCodim cocodeRepresentation A ≤ rank A + 1) :
    5 ≤ fixedCodim cocodeRepresentation A := by
  apply nearOffender_five_of_involution_quadratic cocodeRepresentation
    m24_cocode_involution_ge_four _ A hA hnear
  intro B hB hq
  let := hB.2
  exact (Nat.log_mono_right (QuadraticActors.m24_cocode_card_le_four B hq)).trans
    (by decide : Nat.log 2 4 ≤ 2)

variable {X E : Type*} [Group X] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) X E)

private theorem marked_nearOffender_five
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) M24 W)
    (hσ : ∀ B : Subgroup M24, IsElementaryTwo B →
      fixedCodim σ B ≤ rank B + 1 → 5 ≤ fixedCodim σ B)
    (f : X →* M24) (hf : Function.Injective f) (e : E ≃ₗ[ZMod 2] W)
    (he : ∀ a v, e (ρ a v) = σ (f a) (e v))
    (B : Subgroup X) (hB : IsElementaryTwo B) (hnear : fixedCodim ρ B ≤ rank B + 1) :
    5 ≤ fixedCodim ρ B := by
  let := hB.2
  have hBm : IsElementaryTwo (B.map f) :=
    ⟨fun hz => hB.1 ((B.map_eq_bot_iff_of_injective hf).mp hz),IsElementaryAbelian.map f⟩
  have heq := fixedCodim_map_equivariant ρ σ f e he B
  rw [heq,←rank_map_injective f hf B] at hnear
  exact heq.symm ▸ hσ _ hBm hnear

/-- In any actually marked M23/M24 code or cocode, an (F-1)-offender
moves at least five dimensions. No source escaping-space bound is assumed. -/
theorem largeMathieu_nearOffender_fixedCodim_ge_five
    (hm : IsM23Code ρ ∨ IsM23Cocode ρ ∨ MathieuSmall.IsM24ToddOrDual ρ)
    (B : Subgroup X) (hB : IsElementaryTwo B) (hnear : fixedCodim ρ B ≤ rank B + 1) :
    5 ≤ fixedCodim ρ B := by
  rcases hm with ⟨e,E,he⟩ | ⟨e,E,he⟩ | ⟨e,hc | hd⟩
  · exact marked_nearOffender_five ρ codeRepresentation m24_nearOffender_five_code
      (pointEmbedding.comp e.toMonoidHom) (pointEmbedding_injective.comp e.injective) E he B hB hnear
  · exact marked_nearOffender_five ρ cocodeRepresentation m24_nearOffender_five_cocode
      (pointEmbedding.comp e.toMonoidHom) (pointEmbedding_injective.comp e.injective) E he B hB hnear
  · obtain ⟨E⟩ := hc
    exact marked_nearOffender_five ρ cocodeRepresentation m24_nearOffender_five_cocode
      e.toMonoidHom e.injective E.toLinearEquiv
      (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v) B hB hnear
  · obtain ⟨E⟩ := hd
    exact marked_nearOffender_five ρ codeRepresentation m24_nearOffender_five_code
      e.toMonoidHom e.injective E.toLinearEquiv
      (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v) B hB hnear

/-- Every odd prime actor in these same literal markings moves at least six
binary dimensions, with cyclic duality preserving the code distinction. -/
theorem largeMathieu_odd_fixedCodim_ge_six
    (hm : IsM23Code ρ ∨ IsM23Cocode ρ ∨ MathieuSmall.IsM24ToddOrDual ρ)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (a : X) (ha : orderOf a = p) :
    6 ≤ fixedCodim ρ (zpowers a) := by
  rcases hm with hc | ⟨e,E,he⟩ | ⟨e,hc | hd⟩
  · exact m23Code_marked_odd_fixedCodim ρ hc hp ho a ha
  · rw [fixedCodim_map_equivariant ρ m23CocodeRepresentation e.toMonoidHom E he,
      MonoidHom.map_zpowers]
    exact m23_cocode_fixedCodim_ge_six _ hp ho
      ((Nat.card_zpowers (e a)).trans ((e.orderOf_eq a).trans ha))
  · obtain ⟨E⟩ := hc
    rw [fixedCodim_map_equivariant ρ cocodeRepresentation e.toMonoidHom E.toLinearEquiv
      (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v),MonoidHom.map_zpowers]
    exact cocode_fixedCodim_ge_six _ hp ho
      ((Nat.card_zpowers (e a)).trans ((e.orderOf_eq a).trans ha))
  · obtain ⟨E⟩ := hd
    rw [fixedCodim_map_equivariant ρ codeRepresentation e.toMonoidHom E.toLinearEquiv
      (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v),MonoidHom.map_zpowers,
      code_cocode_fixedCodim_zpowers]
    exact cocode_fixedCodim_ge_six _ hp ho
      ((Nat.card_zpowers (e a)).trans ((e.orderOf_eq a).trans ha))

/-- The original higher Thompson subgroup centralizes the module whenever
its whole local actor fixes a subspace of corank below five. -/
theorem largeMathieu_thompson_centralizes_of_small_corank
    {G : Type*} [Group G] [Finite G] (W A U : Subgroup G)
    [IsElementaryAbelian 2 W] (hWA : W ≤ A)
    (hAN : A ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (hAU : A ≤ centralizer (U : Set G))
    (hm : IsM23Code (automizerRepresentation W) ∨
      IsM23Cocode (automizerRepresentation W) ∨
      MathieuSmall.IsM24ToddOrDual (automizerRepresentation W))
    (hsmall : subgroupCorank W U < 5) :
    thompsonJ A 1 ≤ centralizer (W : Set G) := by
  apply sSup_le
  intro B hB
  by_contra hn
  let := hB.2.1
  have hBN := hB.1.trans hAN
  have hBI : IsElementaryTwo (inducedAutomizer W B) :=
    ⟨fun hb => hn ((inducedAutomizer_eq_bot_iff hBN).mp hb),
      inducedAutomizer_elementary W B hBN⟩
  have hlow := largeMathieu_nearOffender_fixedCodim_ge_five (automizerRepresentation W) hm _ hBI
    (thompson_family_fixedCodim_le W A hWA hAN B hB)
  rw [fixedCodim_inducedAutomizer W B hBN] at hlow
  have hUB : U ≤ W ⊓ centralizer (B : Set G) :=
    le_inf hUW (le_centralizer_iff.mp (hB.1.trans hAU))
  have hadd := offender_corank_add hUB inf_le_left
  omega
end CFSG.Quasithin.Chapter7.NormalizedSource
