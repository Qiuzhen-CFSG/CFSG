module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryNatural
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryDefs
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# The field residual as a local C-component

For n > 2, the half-degree natural marking identifies the quotient of
O²(N_L(U)) by its two-core with a nonabelian simple SL₂. The residual is
two-perfect, so this quotient makes it a C-component. The arranged Sylow
normalizes it, and its join with that Sylow has a nonzero two-core because
it contains the nonzero field-fixed space U in the normal module B.

Source: Aschbacher–Smith, 6.1.14(5), printed p.671.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {L M B U S : Subgroup G} {n : ℕ}

/-- The field residual is a genuine local C-component at the arranged Sylow. -/
theorem field_residual_mem_local
    [IsElementaryAbelian 2 B]
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hBS : B ≤ S) (hSL : S ≤ normalizer (L : Set G))
    (hSB : S ≤ normalizer (B : Set G)) (hSU : S ≤ normalizer (U : Set G))
    (hSyl : Chapter1.IsSylowIn 2 S (normalizer (U : Set G))) :
    fieldLocalResidual L U ∈ Chapter1.L G S ∧
      S ≤ normalizer (fieldLocalResidual L U : Set G) := by
  let R := fieldLocalResidual L U
  have hRN : R ≤ normalizer (U : Set G) := (map_subtype_le _).trans inf_le_right
  have hSR : S ≤ normalizer (R : Set G) :=
    ((le_inf hSL (hSU.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image
          (L ⊓ normalizer (U : Set G)) (pResidual 2 (L ⊓ normalizer (U : Set G) : Subgroup G)))
  have hRj : R ≤ R ⊔ S := le_sup_left
  have hnormal : (R.subgroupOf (R ⊔ S)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hRj).mpr (sup_le R.le_normalizer hSR)
  obtain ⟨m, hnm, _, hnat⟩ := field_fixedSpace_natural hn hnatural hfield hUne
  obtain ⟨F, _, _, _, hF, e, _⟩ := hnat
  have hsize : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ m from pow_lt_pow_right₀ (by decide) (by omega))
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hsize
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_perfect hsize
  have hz : center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    rcases (inferInstance : (center (Matrix.SpecialLinearGroup (Fin 2) F)).Normal).eq_bot_or_eq_top with he | he
    · exact he
    · let := center_eq_top_iff.mp he
      exact (Group.IsPerfect.not_isSolvable (Matrix.SpecialLinearGroup (Fin 2) F) inferInstance).elim
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv e.symm
  have hp : IsPPerfect 2 R := isPPerfect_embedded_pResidual 2 _
  have htop : (⊤ : Subgroup R).IsCComponent :=
    isCComponent_top_of_isPPerfect_of_quasisimple_quotient (pCore 2 R) pCore_isPGroup hp
  have hc : (R.subgroupOf (R ⊔ S)).IsCComponent := by
    have hh := htop.map_equiv (subgroupOfEquivOfLe hRj).symm
    rw [map_top_of_surjective _ (subgroupOfEquivOfLe hRj).symm.surjective] at hh
    have hh' := hh.map_subtype hnormal.isSubnormal
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh'
  have hLB : L ≤ normalizer (B : Set G) := by
    obtain ⟨_, _, _, _, _, hmodel⟩ := hnatural
    exact hmodel.normalizes
  have hBj : B ≤ (R ⊔ S).pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 B) (hBS.trans le_sup_right)
    (sup_le (((map_subtype_le _).trans inf_le_left).trans hLB) hSB)
  have hUB : U ≤ B := by obtain ⟨_, _, _, he, _⟩ := hfield; exact he.le.trans inf_le_left
  refine ⟨⟨hc, hSyl.restrict le_sup_right (sup_le hRN hSU), ?_⟩, hSR⟩
  intro hz
  exact hUne (bot_unique (hUB.trans (hBj.trans hz.le)))
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

