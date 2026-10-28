module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Setup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.SpecificGroups.SU3.BorelTorus.BorelResiduals
public import Theory.SpecificGroups.SU3.BorelTorus.BorelResiduals.Quotients

/-!
# Marked unitary Borel models

The established Chapter F geometry makes the standard root range Sylow and
identifies its normalizer with the full root–torus join. Transport of the
Hermitian form, followed by Sylow conjugacy, identifies any specified Sylow
and its normalizer simultaneously. The two-core is always taken inside
that normalizer. The projective comparison uses the actual SU → PSU map.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954; Chapter F.1.3.
-/

@[expose] public section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus
open CFSG.Quasithin.ChapterF.Source.Unitary
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree

/-- The embedded two-core of any specified Sylow normalizer. -/
theorem sylowNormalizer_twoCore {G : Type*} [Group G] (S : Sylow 2 G) :
    (normalizer (S : Set G)).pCoreIn 2 = (S : Subgroup G) :=
  CFSG.Quasithin.ChapterF.Source.twoCore_sylow_normalizer S

private theorem align_sylow {G H : Type*} [Group G] [Group H] [Finite H]
    (e₀ : G ≃* H) (S : Sylow 2 G) (R : Sylow 2 H) :
    ∃ e : G ≃* H, (S : Subgroup G).map e.toMonoidHom = (R : Subgroup H) ∧
      (normalizer (S : Set G)).map e.toMonoidHom = normalizer (R : Set H) := by
  let : Finite G := Finite.of_injective e₀ e₀.injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H
    (S.mapSurjective (f := e₀.toMonoidHom) e₀.surjective) R
  let e := e₀.trans (MulAut.conj g)
  have hS : (S : Subgroup G).map e.toMonoidHom = (R : Subgroup H) := by
    rw [show e.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e₀.toMonoidHom from rfl,
      ← Subgroup.map_map]
    exact congrArg Sylow.toSubgroup hg
  refine ⟨e, hS, ?_⟩
  change (normalizer ((S : Subgroup G) : Set G)).map e.toMonoidHom = _
  rw [map_equiv_normalizer_eq, hS]
  rfl

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable (n : ℕ) (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
variable (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
include n hn hcard hconj

/-- The standard special root is Sylow, with precisely the full Borel normalizer. -/
theorem special_standard_sylow
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ S : Sylow 2 J.specialSubgroup,
      (S : Subgroup J.specialSubgroup) = specialRoot J hJ ∧
      normalizer (S : Set J.specialSubgroup) = specialBorel J hJ := by
  obtain ⟨_, _, S, hS, _, _, _, hN, _⟩ :=
    standard_su_borel_data J n hn hcard hconj hJ
  refine ⟨S, hS, ?_⟩
  change normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup) = _
  rw [hS]
  exact hN

/-- The projective root is the genuine image Sylow, not its scalar preimage. -/
theorem projective_standard_sylow
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = projectiveRoot J hJ ∧
      normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = projectiveBorel J hJ := by
  obtain ⟨S, hS, _⟩ := special_standard_sylow J n hn hcard hconj hJ
  let P := S.mapSurjective (suProjection_surjective J)
  have hP : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = projectiveRoot J hJ := by
    change (S : Subgroup J.specialSubgroup).map (suProjection J) = _
    rw [hS]
    exact suRoot_map_projection J hJ
  obtain ⟨_, _, _, _, _, _, hsup, hN, _⟩ :=
    standard_projective_matrix_borel J n hn hcard hconj hJ
  refine ⟨P, hP, ?_⟩
  change normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = _
  rw [hP]
  exact hN.trans hsup.symm

/-- The two-core of the full standard special Borel is its root range. -/
theorem specialBorel_twoCore
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (specialBorel J hJ).pCoreIn 2 = specialRoot J hJ := by
  obtain ⟨S, hS, hN⟩ := special_standard_sylow J n hn hcard hconj hJ
  rw [← hN, sylowNormalizer_twoCore, hS]

/-- The two-core of the full standard projective Borel is its root range. -/
theorem projectiveBorel_twoCore
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (projectiveBorel J hJ).pCoreIn 2 = projectiveRoot J hJ := by
  obtain ⟨S, hS, hN⟩ := projective_standard_sylow J n hn hcard hconj hJ
  rw [← hN, sylowNormalizer_twoCore, hS]

/-- The full projective torus meets the root group trivially. -/
theorem projectiveRoot_disjoint_torus
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Disjoint (projectiveRoot J hJ) (projectiveTorus J hJ) := by
  obtain ⟨_, _, _, _, _, hR, _⟩ :=
    standard_projective_matrix_borel J n hn hcard hconj hJ
  have hodd : Odd (Nat.card (projectiveTorus J hJ)) := by
    have he : Odd (Nat.card Eˣ) := by
      rw [Nat.card_units, ← suTorus_card J hJ]
      exact suTorus_odd J hJ n hn hcard
    exact Odd.of_dvd_nat he (card_range_dvd (hermitianTorusPSU J hJ))
  apply disjoint_of_coprime_natCard
  change Nat.Coprime (Nat.card (hermitianUnipotentPSU J hJ).range) _
  rw [hR]
  exact (hodd.coprime_two_left.pow_left n).pow_left 3

/-- A genuine group equivalence simultaneously carries the specified special
Sylow to the standard root and its normalizer to the full standard Borel. -/
theorem su_borel_model (S : Sylow 2 J.specialSubgroup) :
    ∃ e : J.specialSubgroup ≃* (FormTransport.standardForm J).specialSubgroup,
      (S : Subgroup J.specialSubgroup).map e.toMonoidHom =
        specialRoot (FormTransport.standardForm J) rfl ∧
      (normalizer (S : Set J.specialSubgroup)).map e.toMonoidHom =
        specialBorel (FormTransport.standardForm J) rfl := by
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  obtain ⟨R, hR, hN⟩ :=
    special_standard_sylow (FormTransport.standardForm J) n hn hcard hconj rfl
  obtain ⟨e, he, heN⟩ := align_sylow (FormTransport.specialEquiv J C hC) S R
  exact ⟨e, he.trans hR, heN.trans hN⟩

/-- The corresponding genuine projective model, marking the specified Sylow. -/
theorem psu_borel_model (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ e : ProjectiveSpecialUnitaryMatrixGroup J ≃*
        ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J),
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom =
        projectiveRoot (FormTransport.standardForm J) rfl ∧
      (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))).map e.toMonoidHom =
        projectiveBorel (FormTransport.standardForm J) rfl := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)) :=
    Finite.of_surjective _ (suProjection_surjective _)
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  obtain ⟨R, hR, hN⟩ :=
    projective_standard_sylow (FormTransport.standardForm J) n hn hcard hconj rfl
  obtain ⟨e, he, heN⟩ := align_sylow (FormTransport.projectiveEquiv J C hC) S R
  exact ⟨e, he.trans hR, heN.trans hN⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
