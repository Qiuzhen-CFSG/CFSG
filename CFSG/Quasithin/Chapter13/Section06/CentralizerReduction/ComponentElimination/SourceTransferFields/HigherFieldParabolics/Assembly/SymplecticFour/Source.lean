module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.LocalGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction

/-!
# The complete marked `Sp₄(2^m)` branch of source 13.6.19

The literal plus-component model is aligned with the actual Sylow
intersection. The point and plane residual images generate the matrix group,
so one of their source preimages moves `z`. The marked-action and local
geometry modules then provide normalization, the intrinsic core comparison,
local-family membership, quasisimplicity and minimal-parabolicity. The full
C.1.26 source input forces the selected residual to be short, while the
marked action proves it is not short (and hence not a block).

All quotient and residual statements below use the actual preimages in `G`.
The model is an equivalence for `K⁺`; no identification of `K` with `Sp F`
is used. The universal B.5/A.3.6 and C.1.26 inputs, together with the
earlier ambient conclusions, remain explicit.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
13.6.14, 13.6.16(2) and 13.6.19, printed pp.929--931.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour
open ComponentSelection
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
open Theory.SpecificGroups.SymplecticFour
open LocalGeometry
open MarkedAction

universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (Uv z v)]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)

include hF hm

/-- Construct the moving source residual and all model-specific premises
needed by C.1.26 for an actual `K⁺ ≃ Sp(F)` model. -/
theorem source_parabolic
    (source : ChapterB.SourceInduction.AdequateClassificationInput.{u,u}
      CFSG.KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK CFSG.KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v)
    (hnK : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e₀ : plusImage K L T z v hL hz K ≃* Sp F) :
    ∃ e : plusImage K L T z v hL hz K ≃* Sp F,
      ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) = unipotent ∧
      ∃ P ∈ ({pointPreimage K L T z v hL hz e,
        planePreimage K L T z v hL hz e} : Set (Subgroup G)),
        P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧ Tv T v ⊓ K ≤ P ∧
        Tv T v ≤ normalizer (P : Set G) ∧
        Tv T v ≤ normalizer (residualIn P : Set G) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        residualIn P ∈ Chapter1.LIn (Gv v) (Tv T v) ∧
        ¬ ChapterC.IsShort (residualIn P) ∧
        ¬ ChapterC.IsBlock (residualIn P) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F)) ∧
        IsQuasisimple (residualIn P ⧸ pCore 2 (residualIn P)) ∧
        IsSQTK CFSG.KnownSimple.IsKnownSimple (residualIn P ⊔ Tv T v : Subgroup G) ∧
        generalizedFitting (residualIn P ⊔ Tv T v : Subgroup G) =
          pCore 2 (residualIn P ⊔ Tv T v : Subgroup G) ∧
        ∀ S : Sylow 2 (residualIn P ⊔ Tv T v : Subgroup G),
          (S : Subgroup (residualIn P ⊔ Tv T v : Subgroup G)).map
            (residualIn P ⊔ Tv T v).subtype = Tv T v →
              ChapterB.IsMinimalParabolicOver S ⊤ := by
  obtain ⟨e, hmark, P, hP, hPK, hmax, hinter, hmove, hplus⟩ :=
    moving_aligned_flag_residual K L T z v hL hz hF hm hK hnK e₀
  obtain ⟨hPK', hnP, hnR, hk, hnonshort⟩ :=
    MarkedAction.source_flag_obstruction K L T z v hL hz source hG hF hm hv hK
      hnK hU hSyl hW e hA36 hmark.le P hP
  obtain ⟨hlocal, hquasi, hpar⟩ :=
    flag_local_structure_of_central_kernel K L T z v hL hz hF hm P e hP hPK' hK
      hnP hSyl hf hk
  have hsqtk := LinearThree.residual_join_sqtk hG T P v hv (hPK'.trans hK.1.1)
  have hfR := LinearThree.residual_join_characteristic_two T P v
    (hPK'.trans hK.1.1) hSyl hf
  exact ⟨e, hmark, P, hP, hPK', hmax, hinter, hnP, hnR, hmove, hlocal,
    (hnonshort hmove).1, (hnonshort hmove).2, hplus, hquasi,
    hsqtk, hfR, hpar⟩

/-- C.1.26 excludes every actual higher-field symplectic model. -/
theorem not_sp4_of_source
    (choices : DistinguishedPairs.{u})
    (c126 : C126Source CFSG.KnownSimple.IsKnownSimple choices)
    (source : ChapterB.SourceInduction.AdequateClassificationInput.{u,u}
      CFSG.KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK CFSG.KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v)
    (hnK : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D) :
    ¬ Nonempty (plusImage K L T z v hL hz K ≃* Sp F) := by
  rintro ⟨e₀⟩
  obtain ⟨e, hmark, P, hP, hPK, hmax, hinter, hnP, hnR, hmove,
    hlocal, hnonshort, hblock, hplus, hquasi, hsqtk, hfR, hpar⟩ :=
    source_parabolic K L T z v hL hz hF hm source hG hA36 hv hK hnK hU hSyl hf hW e₀
  let := hquasi
  have hshort := short_of_C126 choices c126 (Tv T v) (residualIn P)
    hlocal.2 hnR (h16 _ hlocal hnR hmove) hsqtk hfR hpar
  exact hnonshort hshort

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour
