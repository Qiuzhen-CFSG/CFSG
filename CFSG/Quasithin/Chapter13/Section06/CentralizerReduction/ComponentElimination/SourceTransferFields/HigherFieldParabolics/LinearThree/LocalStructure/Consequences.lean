module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.CoreComparison
public import Theory.SpecificGroups.SL2.CentralCoreParabolic

/-!
# Local-family and C.1.26 consumers of the precise core comparison

For either published flag preimage, centrality of the intrinsic-to-plus core
comparison kernel yields a quasisimple intrinsic quotient and a minimal
parabolic over every Sylow subgroup mapping to the actual Tᵥ. The local-family
proof also uses F*(Gᵥ)=O₂(Gᵥ) and the actual Sylow condition in Gᵥ.

The final consumer applies the existing short_of_C126, retaining the literal
residual, Sylow inclusion, full SQTK hypothesis and 13.6.16(2) obstruction.
Kernel centrality is a source obligation, not a two-group-kernel assumption.
Parabolic invariance is supplied by the independent marked-action argument.
The centralizer-reduction owner discharges the earlier universal sources.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.16 and 13.6.19, printed pp.930–931; B.6.1 and C.1.26.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure
open ComponentSelection
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
universe u
variable {G : Type u} [Group G] [Finite G]

theorem residual_minimal_of_central_kernel
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (K L T P : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hP : P ≤ K)
    (hn : Tv T v ≤ normalizer (P : Set G))
    (e : (plusImage K L T z v hL hz (residualIn P) ⧸
      pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F))
    (hk : (coreComparison K L T (residualIn P) z v hL hz
      ((map_subtype_le _).trans hP)).ker ≤ center (residualIn P ⧸ pCore 2 (residualIn P)))
    (S : Sylow 2 (residualIn P ⊔ Tv T v : Subgroup G))
    (hS : (S : Subgroup (residualIn P ⊔ Tv T v : Subgroup G)).map
      (residualIn P ⊔ Tv T v).subtype = Tv T v) :
    ChapterB.IsMinimalParabolicOver S ⊤ := by
  let R := residualIn P
  let H := R ⊔ Tv T v
  let B := R.subgroupOf H
  let : B.Normal :=
    (normal_subgroupOf_iff_le_normalizer (show R ≤ H from le_sup_left)).mpr
      (sup_le R.le_normalizer (residualIn_normalized _ _ hn))
  let : Group.IsPerfect R := Group.IsPerfect.map P.subtype
  let er : B ≃* R := subgroupOfEquivOfLe (show R ≤ H from le_sup_left)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := er.symm.toMonoidHom) er.symm.surjective
  let eqc := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  let c := coreComparison K L T R z v hL hz ((map_subtype_le _).trans hP)
  let em := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let f := em.toMonoidHom.comp (c.comp eqc.toMonoidHom)
  have hf : Function.Surjective f := em.surjective.comp
    ((coreComparison_surjective K L T R z v hL hz ((map_subtype_le _).trans hP)).comp eqc.surjective)
  have hkc : f.ker ≤ center (B ⧸ pCore 2 B) := by
    intro x hx
    have hc : eqc x ∈ c.ker := em.injective
      ((show f x = 1 from hx).trans (map_one em).symm)
    have hh := (centerCongr eqc.symm ⟨eqc x, hk hc⟩).property
    change eqc.symm (eqc x) ∈ center (B ⧸ pCore 2 B) at hh
    simpa only [eqc.symm_apply_apply] using hh
  apply Matrix.SpecialLinearGroup.minimal_over_normal_rankOne_core F B S ?_ f hf hkc
  apply map_injective H.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show R ≤ H from le_sup_left), hS,
    ← MonoidHom.range_eq_map, range_subtype]

theorem flag_local_structure_of_central_kernel
    (F : Type*) [Field F] [Finite F] [CharP F 2] (hcard : 4 ≤ Nat.card F)
    (K L T P : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hflag : P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)))
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
  have he : Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
      pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2, F)) := by
    rcases hflag with h | h
    · subst P
      exact ⟨pointPreimagePlusCoreEquiv F hcard K L T z v hL hz e⟩
    · have hh : P = linePreimage F K L T z v hL hz e := Set.mem_singleton_iff.mp h
      subst P
      exact ⟨linePreimagePlusCoreEquiv F hcard K L T z v hL hz e⟩
  obtain ⟨eqr⟩ := he
  exact ⟨residual_mem_LIn_of_central_kernel F hcard K L T P z v hL hz hPK hK.1.1
    hn hSylow hf eqr hk,
    residual_core_quasisimple F hcard K L T P z v hL hz hPK eqr hk,
    residual_minimal_of_central_kernel F K L T P z v hL hz hPK hn eqr hk⟩

theorem short_flag_residual_of_central_kernel {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (hG : IsSimpleQTKE 𝒦 G)
    (F : Type*) [Field F] [Finite F] [CharP F 2] (hcard : 4 ≤ Nat.card F)
    (K L T P : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hflag : P ∈ ({pointPreimage F K L T z v hL hz e,
      linePreimage F K L T z v hL hz e} : Set (Subgroup G)))
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
  obtain ⟨hlocal, hquasi, hpar⟩ := flag_local_structure_of_central_kernel F hcard
    K L T P z v hL hz e hflag hPK hK hn hSylow hf hk
  let := hquasi
  have hnR := residualIn_normalized (Tv T v) P hn
  exact short_of_C126 choices source (Tv T v) (residualIn P) hlocal.2 hnR
    (h16 _ hlocal hnR hmove)
    (residual_join_sqtk hG T P v hv (hPK.trans hK.1.1))
    (residual_join_characteristic_two T P v (hPK.trans hK.1.1) hSylow hf) hpar

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure

end
