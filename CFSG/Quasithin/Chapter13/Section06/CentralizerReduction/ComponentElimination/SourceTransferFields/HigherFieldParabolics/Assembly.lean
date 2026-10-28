module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.Assembly
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.G2
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.Source

/-!
# Source assembly for the higher-field exclusions

The SL₃, Sp₄ and G₂ branches construct a moving non-block maximal-parabolic
residual in the actual source group and exclude their models by the full
C.1.26 alternatives and 13.6.16(2). Their only remaining premises are the
specified universal earlier theorems and genuine earlier ambient conclusions.

The Sp₄ construction uses a model of the literal plus image, proves the
relative maximality and plus-core quotients of both standard preimages, and
assembles the residual generation, marked-action obstruction and local
geometry into the source-facing `source_parabolic` and `not_sp4_of_source`
theorems. The assembly below constructs such a residual for the disjunction
of all three actual models, then discharges every model-specific C.1.26
premise. Earlier-source discharge remains with qt-13-06-centralizer-reduction;
the parent qt-13-06-source-transfer-field-elimination retains the integration
with 13.6.17–18.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.19,
printed p.931.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly
open ComponentSelection
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable (source : ChapterB.SourceInduction.AdequateClassificationInput.{u,u}
    CFSG.KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK CFSG.KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
        ∀ B : Subgroup D, B.IsCComponent → Chapter1.Section02.A36Conclusion B)
variable {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
variable [IsElementaryAbelian 2 (Uv z v)]
    (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))

include source hG hA36 hF hm hv hK hn hU hSyl hf hW

/-- The maximal-parabolic construction in 13.6.19 for all three actual
plus-component models. The witness is constructed before invoking C.1.26 or
13.6.16(2); its intrinsic core quotient and its literal plus-core quotient
are kept distinct. -/
theorem source_parabolic
    (hmodel : Nonempty (plusImage K L T z v hL hz K ≃* SL(3, F)) ∨
      Nonempty (plusImage K L T z v hL hz K ≃* Theory.SpecificGroups.SymplecticFour.Sp F) ∨
      Nonempty (plusImage K L T z v hL hz K ≃* Atlas.G2.Model F)) :
    ∃ P : Subgroup G,
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
  rcases hmodel with he | he | he
  · obtain ⟨e⟩ := he
    obtain ⟨e', hmark, P, hflag, hP⟩ := LinearThree.source_parabolic
      source hG hA36 hF hm K L T z v hv hL hz hK hn hU hSyl hf hW e
    exact ⟨P, hP⟩
  · obtain ⟨e⟩ := he
    obtain ⟨e', hmark, P, hflag, hP⟩ := SymplecticFour.source_parabolic
      K L T z v hL hz hF hm source hG hA36 hv hK hn hU hSyl hf hW e
    exact ⟨P, hP⟩
  · obtain ⟨e⟩ := he
    obtain ⟨g, i, hP⟩ := G2.source_parabolic
      K L T z v hL hz e hG hA36 hF hm hv hK hn hSyl hf hW
    exact ⟨_, hP⟩

/-- Source 13.6.19 with the genuine universal earlier inputs explicit.
The constructed non-block residual discharges all C.1.26 applicability
obligations, and 13.6.16(2) excludes both characteristic alternatives. -/
theorem not_higher_field_of_source
    (choices : DistinguishedPairs.{u})
    (hC126 : C126Source CFSG.KnownSimple.IsKnownSimple choices)
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
        CharacteristicNormalizerObstruction (Tv T v) D) :
    ¬ (Nonempty (plusImage K L T z v hL hz K ≃* SL(3, F)) ∨
      Nonempty (plusImage K L T z v hL hz K ≃* Theory.SpecificGroups.SymplecticFour.Sp F) ∨
      Nonempty (plusImage K L T z v hL hz K ≃* Atlas.G2.Model F)) := by
  intro hmodel
  obtain ⟨P, hPK, hmax, hinter, hnP, hnR, hmove, hlocal, hnonshort, hblock,
    hplus, hquasi, hsqtk, hfR, hpar⟩ := source_parabolic K L T z v hL hz
      source hG hA36 hF hm hv hK hn hU hSyl hf hW hmodel
  let := hquasi
  exact false_of_moving_local_nonshort choices hC126 T (residualIn P) z v
    hlocal hnR hmove h16 hsqtk hfR hpar hnonshort

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly
