module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Model
public import Theory.Representation.SU3.NaturalMatrix

/-!
# The inner SU₃ actors in K.3.3

Hermitian root coordinates give codimension 2s for every nontrivial elementary
subgroup of the marked layer. Transport uses the actual group equivalence,
binary coordinates and layer inclusion. The literal Ω₁(T ∩ L) is quadratic,
has fixed dimension 4s and ratio two. Among elementary actors in T ∩ L it is
the unique actor of ratio at most two. Ambient outer actors are treated separately.

Source: Aschbacher–Smith, K.3.3, printed p.456 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne
open BenderSuzuki.MatrixGroups Subgroup Representation Representation.BinaryOffender
open scoped ENNReal
variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

namespace UnitaryModel
variable (M : UnitaryModel J ρ L)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
  (hcard : Nat.card F = (2 ^ s) ^ 2)
  (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s))
include M hJ hs hcard hconj

/-- Exact codimension for every nontrivial elementary actor in the actual layer. -/
theorem elementary_fixedCodim {A : Subgroup G}
    (hA : IsElementaryTwo A) (hAL : A ≤ L) : fixedCodim ρ A = 2 * s := by
  let B := A.subgroupOf L
  let C := B.map M.groupEquiv.toMonoidHom
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAL
  have hC : IsElementaryTwo C := by
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro hz
    have hB : B = ⊥ := (map_eq_bot_iff_of_injective B M.groupEquiv.injective).mp hz
    change A.subgroupOf L = ⊥ at hB
    apply hA.1
    rw [← map_subgroupOf_eq_of_le hAL, hB, Subgroup.map_bot]
  have he := fixedCodim_map_equivariant (ρ.comp L.subtype) (SU3.NaturalMatrix.natural J)
    M.groupEquiv.toMonoidHom M.coordinates M.intertwines B
  have hf := fixedSpace_comp_map ρ L.subtype B
  rw [map_subgroupOf_eq_of_le hAL] at hf
  change fixedCodim (ρ.comp L.subtype) B = fixedCodim (SU3.NaturalMatrix.natural J) C at he
  rw [fixedCodim, hf] at he
  exact he.trans (SU3.NaturalMatrix.elementary_fixedCodim J hJ hs hcard
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hcard hconj) hC)

omit hJ hs hcard hconj [Finite F] in
/-- Quadraticity transports through the literal layer inclusion. -/
theorem quadratic_of_model {A : Subgroup L}
    (hq : IsQuadratic (SU3.NaturalMatrix.natural J) (A.map M.groupEquiv.toMonoidHom)) :
    IsQuadratic ρ (A.map L.subtype) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  apply M.coordinates.injective
  have he (g : L) (w : V) : M.coordinates (ρ (g : G) w) =
      SU3.NaturalMatrix.natural J (M.groupEquiv g) (M.coordinates w) := M.intertwines g w
  change M.coordinates (ρ (a : G) (ρ (b : G) v - v)) = M.coordinates (ρ (b : G) v - v)
  rw [he, map_sub, he, map_sub]
  have hh := hq (M.groupEquiv a) ⟨a, ha, rfl⟩ (M.groupEquiv b) ⟨b, hb, rfl⟩ (M.coordinates v)
  rw [map_sub] at hh
  exact hh

/-- Quadraticity of the ambient image of each layer Sylow omega. -/
theorem sylowImage_omega_quadratic [Finite G] (P : Sylow 2 L) :
    IsQuadratic ρ (omegaOneAmbient ((P : Subgroup L).map L.subtype)) := by
  let Q : Sylow 2 J.specialSubgroup :=
    P.mapSurjective (f := M.groupEquiv.toMonoidHom) M.groupEquiv.surjective
  rw [← map_omegaOneAmbient_injective L.subtype L.subtype_injective]
  apply M.quadratic_of_model
  rw [map_omegaOneAmbient_injective M.groupEquiv.toMonoidHom M.groupEquiv.injective]
  exact SU3.NaturalMatrix.sylow_omega_quadratic J hJ hs hcard
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hcard hconj) Q

variable [Finite G] [L.Normal]

/-- Quadraticity of the source actor, with the specified Sylow subgroup unchanged. -/
theorem omega_quadratic (T : Sylow 2 G) :
    IsQuadratic ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) := by
  obtain ⟨P, hP⟩ := T.exists_sylow_map_eq_inf_of_normal L
  rw [← hP]
  exact M.sylowImage_omega_quadratic hJ hs hcard hconj P

/-- The source common fixed space has binary dimension 4s. -/
theorem omega_fixed_finrank [FiniteDimensional (ZMod 2) V] (T : Sylow 2 G) :
    Module.finrank (ZMod 2) (fixedSpace ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L))) = 4 * s := by
  have hc := M.elementary_fixedCodim hJ hs hcard hconj
    (M.omega_calculation hJ hs hcard hconj T).1 ((omegaOneAmbient_le _).trans inf_le_right)
  have he := fixedCodim_add_finrank ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L))
  rw [hc, M.finrank_eq hcard] at he
  omega

/-- Every elementary actor in the marked layer has rank at most s. -/
theorem elementary_rank_le {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : A ≤ L) :
    rank A ≤ s := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨T, hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hle : A ≤ omegaOneAmbient ((T : Subgroup G) ⊓ L) := by
    rw [← omegaOneAmbient_eq_self A]
    exact omegaOneAmbient_mono (le_inf hAT hAL)
  have hc := card_le_of_le hle
  have hX := M.omega_calculation hJ hs hcard hconj T
  rw [hA.card_eq_two_pow_rank, hX.1.card_eq_two_pow_rank, hX.2] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hc

/-- Every nontrivial elementary actor in L has ratio at least two. -/
theorem inner_actionRatio_ge_two {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : A ≤ L) :
    2 ≤ actionRatio ρ A := by
  have hr := M.elementary_rank_le hJ hs hcard hconj hA hAL
  have h0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)
  rw [actionRatio, ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl (by simp))]
  rw [M.elementary_fixedCodim hJ hs hcard hconj hA hAL]
  exact_mod_cast Nat.mul_le_mul_left 2 hr

/-- The source actor attains two; it is not an FF-offender of threshold one. -/
theorem omega_ratio (T : Sylow 2 G) :
    actionRatio ρ (omegaOneAmbient ((T : Subgroup G) ⊓ L)) = 2 := by
  have hc := M.omega_calculation hJ hs hcard hconj T
  have hL := (omegaOneAmbient_le ((T : Subgroup G) ⊓ L)).trans inf_le_right
  apply le_antisymm
  · apply (actionRatio_le_nat_iff ρ hc.1 2).mpr
    rw [M.elementary_fixedCodim hJ hs hcard hconj hc.1 hL, hc.2]
  · exact M.inner_actionRatio_ge_two hJ hs hcard hconj hc.1 hL

/-- Inside T ∩ L, the omega subgroup is the unique elementary actor of ratio at most two. -/
theorem inner_threshold_iff (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ T) (hAL : A ≤ L) :
    (IsElementaryTwo A ∧ actionRatio ρ A ≤ 2) ↔
      A = omegaOneAmbient ((T : Subgroup G) ⊓ L) := by
  constructor
  · rintro ⟨hA, hratio⟩
    have hbound := (actionRatio_le_nat_iff ρ hA 2).mp hratio
    rw [M.elementary_fixedCodim hJ hs hcard hconj hA hAL] at hbound
    have hle : A ≤ omegaOneAmbient ((T : Subgroup G) ⊓ L) := by
      let : IsElementaryAbelian 2 A := hA.2
      rw [← omegaOneAmbient_eq_self A]
      exact omegaOneAmbient_mono (le_inf hAT hAL)
    apply eq_of_le_of_card_ge hle
    have hX := M.omega_calculation hJ hs hcard hconj T
    rw [hA.card_eq_two_pow_rank, hX.1.card_eq_two_pow_rank, hX.2]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · rintro rfl
    exact ⟨(M.omega_calculation hJ hs hcard hconj T).1,
      (M.omega_ratio hJ hs hcard hconj T).le⟩

/-- The two infima follow once outer elementary actors of ratio at most two are excluded. -/
theorem ratios_of_outer_exclusion
    (houter : ∀ A : Subgroup G, IsElementaryTwo A → actionRatio ρ A ≤ 2 → A ≤ L) :
    quadraticRatio ρ = 2 ∧ cubicRatio ρ = 2 := by
  have hlow : 2 ≤ cubicRatio ρ := by
    apply le_iInf
    intro A
    apply le_iInf
    intro hA
    by_cases hle : actionRatio ρ A ≤ 2
    · exact M.inner_actionRatio_ge_two hJ hs hcard hconj hA.1 (houter A hA.1 hle)
    · exact le_of_not_ge hle
  let T : Sylow 2 G := Classical.choice inferInstance
  have hupp : quadraticRatio ρ ≤ 2 := by
    apply iInf_le_of_le (omegaOneAmbient ((T : Subgroup G) ⊓ L))
    apply iInf_le_of_le ⟨(M.omega_calculation hJ hs hcard hconj T).1,
      M.omega_quadratic hJ hs hcard hconj T⟩
    exact (M.omega_ratio hJ hs hcard hconj T).le
  have hc := cubicRatio_le_quadraticRatio ρ
  exact ⟨le_antisymm hupp (hlow.trans hc), le_antisymm (hc.trans hupp) hlow⟩

/-- The outer exclusion upgrades inner uniqueness to the original ambient Sylow subgroup. -/
theorem threshold_iff_of_outer_exclusion
    (houter : ∀ A : Subgroup G, IsElementaryTwo A → actionRatio ρ A ≤ 2 → A ≤ L)
    (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ T) :
    (IsElementaryTwo A ∧ actionRatio ρ A ≤ 2) ↔
      A = omegaOneAmbient ((T : Subgroup G) ⊓ L) := by
  constructor
  · intro hA
    exact (M.inner_threshold_iff hJ hs hcard hconj T hAT (houter A hA.1 hA.2)).mp hA
  · rintro rfl
    exact ⟨(M.omega_calculation hJ hs hcard hconj T).1,
      (M.omega_ratio hJ hs hcard hconj T).le⟩

end UnitaryModel
end CFSG.Quasithin.ChapterK.RankOne
