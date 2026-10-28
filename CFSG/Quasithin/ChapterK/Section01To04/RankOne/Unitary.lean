module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Outer
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Standard
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Normalizer

/-!
# The natural unitary branch of K.3.3

The full SU₃ model supplies the rank-s actor Ω₁(T ∩ L), its quadratic action,
fixed dimension 4s, and ratio two. The actual ambient coefficient action
and linear-involution containment are proved from this model. The outer
calculation then excludes all other
elementary actors of ratio at most two, including the endpoint s=2. Consequently
both global infima equal two and the threshold family in T is a singleton.

`unitary_case` gives this conclusion for any genuine Hermitian form, transporting
the group and its column action together to standard coordinates. It retains
no extra normalizer premises. Natural-module recognition from the source
central-quotient family is independently owned.

Source: Aschbacher–Smith, K.3.3, printed p.456 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne
open BenderSuzuki.MatrixGroups Representation.BinaryOffender
open scoped ENNReal
variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The source omega calculation is unconditional once the genuine natural
module is identified. Arbitrary Hermitian forms are transported with their action. -/
theorem SourceHypotheses.unitary_omega (h : SourceHypotheses ρ L)
    (M : UnitaryModel J ρ L) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s)) (T : Sylow 2 G) :
    Module.finrank (ZMod 2) V = 6 * s ∧
    IsElementaryTwo (omegaOneAmbient ((T : Subgroup G) ⊓ L)) ∧
    rank (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = s ∧
    Module.finrank (ZMod 2) (fixedSpace ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L))) = 4 * s ∧
    IsQuadratic ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) ∧
    actionRatio ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = 2 := by
  let : L.Normal := h.layer_normal
  obtain ⟨N⟩ := M.exists_standard (by omega : 0 < s) hcard hconj
  have hX := N.omega_calculation rfl hs hcard hconj T
  exact ⟨M.finrank_eq hcard, hX.1, hX.2,
    N.omega_fixed_finrank rfl hs hcard hconj T,
    N.omega_quadratic rfl hs hcard hconj T, N.omega_ratio rfl hs hcard hconj T⟩

/-- The entire ratio and uniqueness conclusion, conditional only on the actual
semilinear normalizer data in addition to the specified natural-module model. -/
theorem SourceHypotheses.unitary_case_of_semilinear_control (h : SourceHypotheses ρ L)
    (M : UnitaryModel J ρ L) (C : UnitarySemilinearControl M)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s)) (T : Sylow 2 G) :
    quadraticRatio ρ = 2 ∧ cubicRatio ρ = 2 ∧
    Module.finrank (ZMod 2) V = 6 * s ∧
    IsElementaryTwo (omegaOneAmbient ((T : Subgroup G) ⊓ L)) ∧
    rank (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = s ∧
    Module.finrank (ZMod 2) (fixedSpace ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L))) = 4 * s ∧
    IsQuadratic ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) ∧
    actionRatio ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = 2 ∧
    (∀ A : Subgroup G, A ≤ T →
      ((IsElementaryTwo A ∧ actionRatio ρ A ≤ 2) ↔
        A = omegaOneAmbient ((T : Subgroup G) ⊓ L))) := by
  let : L.Normal := h.layer_normal
  have houter : ∀ A : Subgroup G, IsElementaryTwo A → actionRatio ρ A ≤ 2 → A ≤ L :=
    fun _ hA hr => C.elementary_le_layer hJ hs hcard hconj hA hr
  have hrat := M.ratios_of_outer_exclusion hJ hs hcard hconj houter
  have hX := M.omega_calculation hJ hs hcard hconj T
  exact ⟨hrat.1, hrat.2, M.finrank_eq hcard, hX.1, hX.2,
    M.omega_fixed_finrank hJ hs hcard hconj T, M.omega_quadratic hJ hs hcard hconj T,
    M.omega_ratio hJ hs hcard hconj T,
    fun _ hAT => M.threshold_iff_of_outer_exclusion hJ hs hcard hconj houter T hAT⟩

/-- K.3.3's complete ratio and uniqueness calculation from an actual natural
SU₃ identification. The normalizer premises are discharged, the possible cubic
center is retained, and the literal actor is Ω₁(T ∩ L). This also covers s=2. -/
theorem SourceHypotheses.unitary_case (h : SourceHypotheses ρ L)
    (M : UnitaryModel J ρ L) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s)) (T : Sylow 2 G) :
    quadraticRatio ρ = 2 ∧ cubicRatio ρ = 2 ∧
    Module.finrank (ZMod 2) V = 6 * s ∧
    IsElementaryTwo (omegaOneAmbient ((T : Subgroup G) ⊓ L)) ∧
    rank (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = s ∧
    Module.finrank (ZMod 2) (fixedSpace ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L))) = 4 * s ∧
    IsQuadratic ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) ∧
    actionRatio ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = 2 ∧
    (∀ A : Subgroup G, A ≤ T →
      ((IsElementaryTwo A ∧ actionRatio ρ A ≤ 2) ↔
        A = omegaOneAmbient ((T : Subgroup G) ⊓ L))) := by
  obtain ⟨N⟩ := M.exists_standard (by omega : 0 < s) hcard hconj
  obtain ⟨C, _⟩ := N.exists_semilinearControl h rfl hs hcard hconj
  exact h.unitary_case_of_semilinear_control N C rfl hs hcard hconj T

end CFSG.Quasithin.ChapterK.RankOne
