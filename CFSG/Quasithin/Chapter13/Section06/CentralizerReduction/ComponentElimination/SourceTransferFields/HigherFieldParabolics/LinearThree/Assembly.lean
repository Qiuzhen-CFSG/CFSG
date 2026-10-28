module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure

/-!
# The marked higher-field SL₃ branch of 13.6.19

Align the given SL₃ model with the actual Sylow intersection, then use the
complete adequate B.5 classifier to normalize both literal flag preimages.
Their residuals generate the plus image, so one moves z. The source kernel
argument supplies its intrinsic local structure, while the elementary
marked action and affine plus image obstruct shortness. In particular the
selected residual is not a block, as required on printed p.931.

The construction retains the same aligned equivalence and original quotient
maps throughout. It supplies all local inputs of C.1.26, including SQTK and
characteristic two for the residual joined with Tᵥ. The second theorem applies
the higher-field parent's C.1.26 obstruction to exclude the given SL₃ model.
Neither flag invariance, movement, local membership, kernel control nor
non-shortness is assumed.

The universal adequate B.5, A.3.6 and C.1.26 inputs and the earlier ambient
elementary, reduced-family, Sylow, characteristic-two, 13.6.14 and 13.6.16(2)
conclusions remain with qt-13-06-centralizer-reduction and their source owners.
The parent qt-13-06-source-higher-field-parabolics retains the three-family
assembly and discharge of C.1.26. This module completes its SL₃ construction;
it does not assert the entire source theorem without those earlier inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14, 13.6.16 and 13.6.19, printed pp.929–931.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree
open ComponentSelection
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Construct the source maximal parabolic and every local input needed by
C.1.26 from an arbitrary SL₃ model. The alignment and non-block assertion
are conclusions, and the displayed PSL₂ quotient uses the literal plus map. -/
theorem source_parabolic
    (source : ChapterB.SourceInduction.AdequateClassificationInput.{u,u}
      CFSG.KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK CFSG.KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (K L T : Subgroup G) (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e₀ : plusImage K L T z v hL hz K ≃* SL(3, F)) :
    ∃ e : plusImage K L T z v hL hz K ≃* SL(3, F),
      ((Tv T v).subgroupOf K).map
        (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) =
          Matrix.PSL3.LinearThree.unipotentSL F ∧
      ∃ P ∈ ({pointPreimage F K L T z v hL hz e,
        linePreimage F K L T z v hL hz e} : Set (Subgroup G)),
        P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧ Tv T v ⊓ K ≤ P ∧
        Tv T v ≤ normalizer (P : Set G) ∧
        Tv T v ≤ normalizer (residualIn P : Set G) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        residualIn P ∈ Chapter1.LIn (Gv v) (Tv T v) ∧
        ¬ ChapterC.IsShort (residualIn P) ∧ ¬ ChapterC.IsBlock (residualIn P) ∧
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
  obtain ⟨e, hmark⟩ := LocalStructure.exists_aligned_model F
    (lt_trans Nat.zero_lt_one hm) hF K L T z v hL hz hSyl e₀
  obtain ⟨P, hflag, hPK, hmax, hinter, hnP, hnR, hmove, hshort, he⟩ :=
    MarkedAction.source_moving_normalized_nonshort_flag K L T z v hL hz
      source hG hA36 hF hm hv hK hn hU hSyl hW e hmark
  obtain ⟨hlocal, hquasi, hpar⟩ := LocalStructure.source_flag_local_structure
    hG hA36 F hF hm K L T P z v hv hL hz e hflag hK hnP hSyl hf hW
  exact ⟨e, MarkedAction.marked_intersection_eq_unipotent
    (lt_trans Nat.zero_lt_one hm) hF K L T z v hL hz hK e hmark,
    P, hflag, hPK, hmax, hinter, hnP, hnR, hmove, hlocal, hshort,
    fun h => hshort h.short, he, hquasi,
    residual_join_sqtk hG T P v hv (hPK.trans hK.1.1),
    residual_join_characteristic_two T P v (hPK.trans hK.1.1) hSyl hf, hpar⟩

/-- The SL₃ exclusion in 13.6.19, conditional only on the specified universal
sources and earlier ambient conclusions. The constructed residual discharges
every model-specific premise of the parent's literal C.1.26 application. -/
theorem not_linearThree_of_source
    (source : ChapterB.SourceInduction.AdequateClassificationInput.{u,u}
      CFSG.KnownSimple.IsKnownSimple)
    (choices : DistinguishedPairs.{u})
    (hC126 : C126Source CFSG.KnownSimple.IsKnownSimple choices)
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK CFSG.KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (K L T : Subgroup G) (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D) :
    ¬ Nonempty (plusImage K L T z v hL hz K ≃* SL(3, F)) := by
  rintro ⟨e₀⟩
  obtain ⟨e, hmark, P, hflag, hPK, hmax, hinter, hnP, hnR, hmove, hlocal,
    hshort, hblock, he, hquasi, hsqtk, hfR, hpar⟩ :=
    source_parabolic source hG hA36 hF hm K L T z v hv hL hz hK hn hU hSyl hf hW e₀
  let := hquasi
  exact false_of_moving_local_nonshort choices hC126 T (residualIn P) z v
    hlocal hnR hmove h16 hsqtk hfR hpar hshort

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree
