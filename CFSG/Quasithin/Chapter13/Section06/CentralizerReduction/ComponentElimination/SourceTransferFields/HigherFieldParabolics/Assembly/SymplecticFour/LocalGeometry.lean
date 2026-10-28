module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ResidualGeneration
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.Consequences

/-!
# Conditional local geometry for the literal Sp₄ parabolic preimages

An actual K⁺ ≃ Sp₄(F) model can be conjugated so that the image of the genuine
Sylow intersection Tᵥ ∩ K equals the standard unipotent subgroup. The two
intrinsic matrix parabolic residuals generate Sp₄, so their literal preimages
in K have generating plus images. The Y_z condition and Tᵥ-invariance of K
then select a residual moving z; no moving witness is assumed.

For either flag preimage, Tᵥ-normalization and centrality of the literal
intrinsic-to-plus core-comparison kernel imply membership in L(Gᵥ,Tᵥ), a
quasisimple intrinsic core quotient, and minimal parabolicity over every Sylow
subgroup whose ambient image is Tᵥ. Local SQTK and characteristic two are
derived from the ambient source hypotheses. The final consumer applies
universal C.1.26 and the strict characteristic-normalizer assertion of
13.6.16(2) to the constructed moving residual.

This is the conditional geometry branch of 13.6.19. Normalization and kernel
centrality are supplied by qt-13-06-sp4-source-marked-obstruction; the parent
qt-13-06-source-higher-field-parabolics discharges these inputs and combines
shortness with the marked-action obstruction. Earlier-source discharge stays
with qt-13-06-centralizer-reduction. No identification K ≃ Sp₄ is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
`refs/quasithin.pdf`, 13.6.14, 13.6.16(2), and 13.6.19, printed pp.929–931;
B.6.1, printed p.112, and C.1.26, printed p.132.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.LocalGeometry
open ComponentSelection Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable {F : Type*} [Field F] [Finite F]
variable {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
include hF hm

/-- Align the actual Sylow intersection, using its image under K → K⁺ → Sp₄.
The resulting marking is equality with the standard Sylow, not just containment. -/
theorem exists_aligned_model (hK : K ∈ Yz L T z v)
    (e : plusImage K L T z v hL hz K ≃* Sp F) :
    ∃ e' : plusImage K L T z v hL hz K ≃* Sp F,
      ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e') = unipotent := by
  have hs := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hK.1.2.2.1 le_sup_left hK.1.2.1.subnormal
  obtain ⟨S, hS⟩ := hs
  have heS : (S : Subgroup K) = (Tv T v).subgroupOf K := by
    have hh := congrArg (comap K.subtype) hS
    simpa only [comap_map_eq_self_of_injective K.subtype_injective,
      comap_inf, comap_subtype, subgroupOf_self, inf_top_eq] using hh
  let f := modelMap K L T z v hL hz e
  let S' := S.mapSurjective (f := f) (modelMap_surjective K L T z v hL hz e)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp F) S' (unipotentSylow hF (by omega))
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  change ((Tv T v).subgroupOf K).map ((MulAut.conj g).toMonoidHom.comp f) = _
  rw [← map_map, ← heS]
  have hh := congrArg (fun A : Sylow 2 (Sp F) => (A : Subgroup (Sp F))) hg
  exact hh

variable [CharP F 2]

/-- Intrinsic Sp₄ residual generation passes through the literal plus map. -/
theorem plus_generation
    (e : plusImage K L T z v hL hz K ≃* Sp F) :
    plusImage K L T z v hL hz K ≤
      plusImage K L T z v hL hz (residualIn (pointPreimage K L T z v hL hz e)) ⊔
        plusImage K L T z v hL hz (residualIn (planePreimage K L T z v hL hz e)) :=
  LinearThree.plus_generation_of_model_residuals K L T z v hL hz e
    pointParabolic planeParabolic (parabolicResiduals_sup_eq_top hF hm)

/-- One of the two genuine maximal parabolic preimages has a moving residual. -/
theorem moving_flag_residual (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Sp F) :
    ∃ P ∈ ({pointPreimage K L T z v hL hz e,
      planePreimage K L T z v hL hz e} : Set (Subgroup G)),
      P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) := by
  obtain ⟨P, hP, hPK, hmove⟩ := moving_residual_of_plus_generation K L T
    (pointPreimage K L T z v hL hz e) (planePreimage K L T z v hL hz e)
    z v hL hz (pointPreimage_le K L T z v hL hz e)
    (planePreimage_le K L T z v hL hz e) (plus_generation K L T z v hL hz hF hm e)
    (LinearThree.moves_of_invariant_Yz K L T z v hK hn)
  refine ⟨P, hP, hPK, ?_, hmove⟩
  rcases hP with hP | hP
  · subst P
    exact pointPreimage_maximal K L T z v hL hz e
  · have he : P = planePreimage K L T z v hL hz e := Set.mem_singleton_iff.mp hP
    subst P
    exact planePreimage_maximal K L T z v hL hz e

/-- Each of the two preimages has the literal PSL₂ plus-core quotient. -/
theorem flag_plus_core_equiv (P : Subgroup G)
    (e : plusImage K L T z v hL hz K ≃* Sp F)
    (hflag : P ∈ ({pointPreimage K L T z v hL hz e,
      planePreimage K L T z v hL hz e} : Set (Subgroup G))) :
    Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
      pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F)) := by
  rcases hflag with h | h
  · subst P
    exact ⟨pointPlusCoreEquiv K L T z v hL hz e hF hm⟩
  · have he : P = planePreimage K L T z v hL hz e := Set.mem_singleton_iff.mp h
    subst P
    exact ⟨planePlusCoreEquiv K L T z v hL hz e hF hm⟩

/-- The marked model gives the complete geometric selection used in 13.6.19. -/
theorem moving_marked_flag_residual (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* Sp F)
    (hmark : ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) ≤ unipotent) :
    ∃ P ∈ ({pointPreimage K L T z v hL hz e,
      planePreimage K L T z v hL hz e} : Set (Subgroup G)),
      P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧ Tv T v ⊓ K ≤ P ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F)) := by
  obtain ⟨P, hP, hPK, hmax, hmove⟩ := moving_flag_residual K L T z v hL hz hF hm hK hn e
  have hi := marked_intersection_le K L T z v hL hz e hmark
  refine ⟨P, hP, hPK, hmax, ?_, hmove, flag_plus_core_equiv K L T z v hL hz hF hm P e hP⟩
  rcases hP with hP | hP
  · subst P
    exact hi.1
  · exact (Set.mem_singleton_iff.mp hP) ▸ hi.2

/-- An arbitrary actual plus model supplies an aligned, moving flag selection. -/
theorem moving_aligned_flag_residual (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e₀ : plusImage K L T z v hL hz K ≃* Sp F) :
    ∃ e : plusImage K L T z v hL hz K ≃* Sp F,
      ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) = unipotent ∧
      ∃ P ∈ ({pointPreimage K L T z v hL hz e,
        planePreimage K L T z v hL hz e} : Set (Subgroup G)),
        P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧ Tv T v ⊓ K ≤ P ∧
          ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
          Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
            pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F)) := by
  obtain ⟨e, he⟩ := exists_aligned_model K L T z v hL hz hF hm hK e₀
  exact ⟨e, he, moving_marked_flag_residual K L T z v hL hz hF hm hK hn e he.le⟩

open LinearThree.LocalStructure

/-- The two explicit conditional inputs imply the actual local-family,
intrinsic quasisimplicity, and B.6.1 minimal-parabolic conclusions. -/
theorem flag_local_structure_of_central_kernel (P : Subgroup G)
    (e : plusImage K L T z v hL hz K ≃* Sp F)
    (hflag : P ∈ ({pointPreimage K L T z v hL hz e,
      planePreimage K L T z v hL hz e} : Set (Subgroup G)))
    (hPK : P ≤ K) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (P : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hk : (coreComparison K L T (residualIn P) z v hL hz
      ((map_subtype_le _).trans hPK)).ker ≤ center (residualIn P ⧸ pCore 2 (residualIn P))) :
    residualIn P ∈ Chapter1.LIn (Gv v) (Tv T v) ∧
      IsQuasisimple (residualIn P ⧸ pCore 2 (residualIn P)) ∧
      ∀ S : Sylow 2 (residualIn P ⊔ Tv T v : Subgroup G),
        (S : Subgroup (residualIn P ⊔ Tv T v : Subgroup G)).map
          (residualIn P ⊔ Tv T v).subtype = Tv T v → ChapterB.IsMinimalParabolicOver S ⊤ := by
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = (2 : ℕ) ^ 2 by decide).le.trans
      (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hm)
  obtain ⟨eqr⟩ := flag_plus_core_equiv K L T z v hL hz hF hm P e hflag
  exact ⟨residual_mem_LIn_of_central_kernel F hcard K L T P z v hL hz hPK hK.1.1
    hn hSylow hf eqr hk,
    residual_core_quasisimple F hcard K L T P z v hL hz hPK eqr hk,
    residual_minimal_of_central_kernel F K L T P z v hL hz hPK hn eqr hk⟩

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp

/-- C.1.26 and the genuine 13.6.16(2) characteristic-normalizer obstruction
force any moving constructed flag residual to be short. Local SQTK and F*=O₂
are derived from the ambient simple QTKE, involution, and Sylow hypotheses. -/
theorem short_flag_residual_of_central_kernel {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (hG : IsSimpleQTKE 𝒦 G) (P : Subgroup G) (hv : orderOf v = 2)
    (e : plusImage K L T z v hL hz K ≃* Sp F)
    (hflag : P ∈ ({pointPreimage K L T z v hL hz e,
      planePreimage K L T z v hL hz e} : Set (Subgroup G)))
    (hPK : P ≤ K) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (P : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hk : (coreComparison K L T (residualIn P) z v hL hz
      ((map_subtype_le _).trans hPK)).ker ≤ center (residualIn P ⧸ pCore 2 (residualIn P)))
    (hmove : ¬ residualIn P ≤ centralizer ({z} : Set G))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D) :
    ChapterC.IsShort (residualIn P) := by
  obtain ⟨hlocal, hquasi, hpar⟩ := flag_local_structure_of_central_kernel
    K L T z v hL hz hF hm P e hflag hPK hK hn hSylow hf hk
  let := hquasi
  have hnR := LinearThree.residualIn_normalized (Tv T v) P hn
  exact short_of_C126 choices source (Tv T v) (residualIn P) hlocal.2 hnR
    (h16 _ hlocal hnR hmove)
    (LinearThree.residual_join_sqtk hG T P v hv (hPK.trans hK.1.1))
    (LinearThree.residual_join_characteristic_two T P v (hPK.trans hK.1.1) hSylow hf) hpar

/-- Apply the conditional geometry to the residual selected by generation.
The two normalizations and the two literal central kernels are the independent
marked-action inputs. Every movement, local-family, and minimal-parabolic
conclusion is constructed here. -/
theorem moving_short_flag_residual {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (hG : IsSimpleQTKE 𝒦 G) (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v) (hnK : Tv T v ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (e : plusImage K L T z v hL hz K ≃* Sp F)
    (hmark : ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) ≤ unipotent)
    (hn : ∀ P ∈ ({pointPreimage K L T z v hL hz e,
      planePreimage K L T z v hL hz e} : Set (Subgroup G)),
      Tv T v ≤ normalizer (P : Set G))
    (hk : ∀ P ∈ ({pointPreimage K L T z v hL hz e,
      planePreimage K L T z v hL hz e} : Set (Subgroup G)), ∀ hPK : P ≤ K,
      (coreComparison K L T (residualIn P) z v hL hz
        ((map_subtype_le _).trans hPK)).ker ≤ center (residualIn P ⧸ pCore 2 (residualIn P)))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D) :
    ∃ P ∈ ({pointPreimage K L T z v hL hz e,
      planePreimage K L T z v hL hz e} : Set (Subgroup G)),
      P ≤ K ∧ IsCoatom (P.subgroupOf K) ∧ Tv T v ⊓ K ≤ P ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F)) ∧
        Tv T v ≤ normalizer (residualIn P : Set G) ∧
        residualIn P ∈ Chapter1.LIn (Gv v) (Tv T v) ∧
        IsQuasisimple (residualIn P ⧸ pCore 2 (residualIn P)) ∧
        (∀ S : Sylow 2 (residualIn P ⊔ Tv T v : Subgroup G),
          (S : Subgroup (residualIn P ⊔ Tv T v : Subgroup G)).map
            (residualIn P ⊔ Tv T v).subtype = Tv T v → ChapterB.IsMinimalParabolicOver S ⊤) ∧
        ChapterC.IsShort (residualIn P) := by
  obtain ⟨P, hP, hPK, hmax, hinter, hmove, he⟩ :=
    moving_marked_flag_residual K L T z v hL hz hF hm hK hnK e hmark
  obtain ⟨hlocal, hquasi, hpar⟩ := flag_local_structure_of_central_kernel
    K L T z v hL hz hF hm P e hP hPK hK (hn P hP) hSylow hf (hk P hP hPK)
  refine ⟨P, hP, hPK, hmax, hinter, hmove, he,
    LinearThree.residualIn_normalized _ _ (hn P hP), hlocal, hquasi, hpar, ?_⟩
  exact short_flag_residual_of_central_kernel K L T z v hL hz hF hm choices source
    hG P hv e hP hPK hK (hn P hP) hSylow hf (hk P hP hPK) hmove h16

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.LocalGeometry
