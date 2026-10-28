module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Factors
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.ReducedSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.Action
public import Theory.Representation.SL2NaturalOffenders.NormalSection
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ThompsonImage
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceBaumann
/-!
# Literal rank-one source placement from the natural component

The normal self-centralizing residual acts naturally on the original moving
section. Every best offender therefore lies in that residual. The original
Thompson image and the proved E.2.3 Baumann equality place the original
Baumann image in K+, giving the Borel normalizations and local placement.
No universal factor-decomposition or Baumann theorem remains as a premise.
Source: Aschbacher--Smith 13.6.18, printed p.931, and E.2.3, pp.216--217.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open Matrix.SpecialLinearGroup.RankOneResidual
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
open ComponentSelection ChapterB.QuasisimpleSource
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem componentRepresentation_eq_wkRestriction
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)] :
    componentRepresentation K L T z v hL hz =
      (wkRepresentation K L T z v hL hz).comp (plusImage K L T z v hL hz K).subtype := by
  ext g w
  rfl

noncomputable def localResidualComponentEquiv
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    {n : ℕ} (hb : ChapterC.IsL2EvenBlock K n) :
    pResidual 2 (localMap K L T z v hL hz).range ≃* plusImage K L T z v hL hz K :=
  ((pResidual 2 (localMap K L T z v hL hz).range).equivMapOfInjective
    (localMap K L T z v hL hz).range.subtype
    (localMap K L T z v hL hz).range.subtype_injective).trans
      (MulEquiv.subgroupCongr (localRange_residual_image K L T z v hL hz hK hnorm hb))

theorem local_natural_offender_le_residual
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    (hred : pCore 2 (localMap K L T z v hL hz).range = ⊥) :
    offenderSubgroup ((wkRepresentation K L T z v hL hz).comp
      (localMap K L T z v hL hz).range.subtype) ≤
        pResidual 2 (localMap K L T z v hL hz).range := by
  let R := (localMap K L T z v hL hz).range
  let C := pResidual 2 R
  let α := wkRepresentation K L T z v hL hz
  let ρ := α.comp R.subtype
  let β := componentRepresentation K L T z v hL hz
  let D := movingSpace K L T z v
  let ec := localResidualComponentEquiv K L T z v hL hz hK hnorm hb
  have hact : ∀ (g : C) w, ρ (g : R) w = β (ec g) w := by
    intro g w
    rfl
  have hD : moved ρ C = D := by
    have he := subspaceCommutator_map_embedding ρ α R.subtype
      (LinearMap.id : Additive (WK K L T z v) →ₗ[ZMod 2] Additive (WK K L T z v))
      (fun _ _ => rfl) C ⊤
    simp only [Submodule.map_id] at he
    change moved ρ C = moved α (C.map R.subtype) at he
    rw [localRange_residual_image K L T z v hL hz hK hnorm hb] at he
    exact he.trans (moved_eq_ukSubspace K L T z v hL hz)
  have hinv : (⊤ : Subgroup R) ≤ subspaceStabilizer ρ D := by
    rw [←hD]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by simp)) le_normalizer_of_normal
  let U : Subrepresentation ρ :=
    { toSubmodule := D
      apply_mem_toSubmodule := fun g w hw => (hinv (mem_top g) w).2 hw }
  let Q := β.invariants.comap D.subtype
  let f : U.toSubmodule →ₗ[ZMod 2] (Fin 2 → F) := s.coordinates.toLinearMap.comp Q.mkQ
  have hf : Function.Surjective f := s.coordinates.surjective.comp Q.mkQ_surjective
  have hk0 : f.ker = Q := by
    rw [LinearMap.ker_comp,s.coordinates.ker,Submodule.comap_bot,Submodule.ker_mkQ]
  have hk : f.ker = fixedSpace U.toRepresentation C := by
    rw [hk0]
    ext w
    constructor
    · intro hw g
      apply Subtype.ext
      exact (hact g w).trans (hw (ec g))
    · intro hw g
      obtain ⟨a,rfl⟩ := ec.surjective g
      exact (hact a w).symm.trans (congrArg Subtype.val (hw a))
  have he : ∀ (g : C) w, f (U.toRepresentation (g : R) w) =
      SL2NaturalOffenders.NoStrong.natural (F := F) ((ec.trans s.actor) g) (f w) := by
    intro g w
    have hs := s.equivariant (ec g) w
    have hew : U.toRepresentation (g : R) w =
        (⟨β (ec g) w,s.invariant (ec g) w⟩ : D) := Subtype.ext (hact g w)
    change s.coordinates (Q.mkQ (U.toRepresentation (g : R) w)) = _
    rw [hew]
    exact hs
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have hn := hb.1
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    omega
  exact SL2NaturalOffenders.offenderSubgroup_le_of_normal_natural_section ρ C
    (centralizer_pResidual_le_of_pCore_eq_bot hred) (ec.trans s.actor) hlarge U f hf hk he

theorem local_natural_thompson_image_le
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    (hred : pCore 2 (localMap K L T z v hL hz).range = ⊥)
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (P : Sylow 2 ↥(K ⊔ Tv T v)) :
    (elementaryAbelianMaxJ (⊤ : Subgroup ↥(K ⊔ Tv T v))).map
      (localMap K L T z v hL hz) ≤ plusImage K L T z v hL hz K := by
  let H := K ⊔ Tv T v
  let W := internalWK K L T z v hL hz
  let q := localProjection K L T z v hL hz
  let R := (localMap K L T z v hL hz).range
  let τ := localRepresentation K L T z v hL hz hW
  let ρ := (wkRepresentation K L T z v hL hz).comp R.subtype
  let E : Additive W ≃ₗ[ZMod 2] Additive (WK K L T z v) :=
    { (internalWKEquiv K L T z v hL hz hW).toAdditive with
      map_smul' := ZMod.map_smul (internalWKEquiv K L T z v hL hz hW).toMonoidHom.toAdditive }
  have hE : ∀ g w, E (τ g w) = ρ g (E w) := by
    intro g w
    obtain ⟨a,rfl⟩ := (localMap K L T z v hL hz).rangeRestrict_surjective g
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (localRepresentation_apply K L T z v hL hz hW a w).trans
      (wkRepresentation_apply K L T z v hL hz (inclusion (localActor_le K L T v) a) (E w)).symm
  have hI : offenderSubgroup τ ≤ offenderSubgroup ρ := by
    have hw (B : Subgroup R) : weight τ B = weight ρ B := by
      have hh := fixedSpace_map_equivariant τ ρ (MonoidHom.id R) E hE B
      rw [Subgroup.map_id] at hh
      unfold weight
      rw [←hh,LinearEquiv.finrank_map_eq]
    apply iSup_le
    intro B
    apply iSup_le
    rintro ⟨hB,_⟩
    have hb : IsBestOffender ρ B := ⟨hB.1,fun C hC => by
      rw [←hw C,←hw B]
      exact hB.2 C hC⟩
    exact hb.le_offenderSubgroup ρ
  have hJ := ChapterE.ThompsonAction.global_thompson_image_le_offender P W q
    (localMap K L T z v hL hz).rangeRestrict_surjective
    (localProjection_ker K L T z v hL hz hW)
    ((IsElementaryAbelian.isPGroup 2 W).le_sylow_of_normal P)
  have hi := hJ.trans (hI.trans (local_natural_offender_le_residual K L T z v hL hz
    hK hnorm hF hb s hred))
  have hm := map_mono (f := R.subtype) hi
  rw [Subgroup.map_map,localRange_residual_image K L T z v hL hz hK hnorm hb] at hm
  exact hm

theorem local_natural_baumann_image_le_of_reduced
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
      (movingSpace K L T z v))
    (hq : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction (Tv T v) K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v))
    (P : Sylow 2 (K ⊔ Tv T v : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv T v : Subgroup G)) =
      (Tv T v).subgroupOf (K ⊔ Tv T v))
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (hred : pCore 2 (localMap K L T z v hL hz).range = ⊥) :
    plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) ≤
      plusImage K L T z v hL hz K := by
  have hW := (WK_le_Tv K L T z v hK.1.1 hSylow hzOmega hf).trans
    (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)
  have hnc : ¬ elementaryAbelianMaxJ (P : Subgroup (K ⊔ Tv T v : Subgroup G)) ≤
      centralizer (internalWK K L T z v hL hz : Set (K ⊔ Tv T v : Subgroup G)) := by
    rw [hP, local_thompson_subgroupOf, ← localMap_ker_internal K L T z v hL hz hW,
      localMap_ker]
    intro hc
    apply local_thompson_noncentral K L T z v hL hz hK hnorm hF hb s hzOmega hpush
    intro x hx
    have hxH : x ∈ K ⊔ Tv T v :=
      (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)
        ((show elementaryAbelianMaxJ (Tv T v) ≤ Tv T v from
          sSup_le fun _ hA => hA.1) hx)
    exact hc (show (⟨x, hxH⟩ : (K ⊔ Tv T v : Subgroup G)) ∈
      (elementaryAbelianMaxJ (Tv T v)).subgroupOf (K ⊔ Tv T v) from hx)
  have he := sourceBaumannImplication_knownSimple P (internalWK K L T z v hL hz)
    (localProjection K L T z v hL hz) (localMap K L T z v hL hz).rangeRestrict_surjective
    (localProjection_ker K L T z v hL hz hW)
    (local_sqtk K T v hK.1.1 hq) hmin
    (local_fitting_eq K T v hK.1.1 hSylow hf) hred hnc
  have him := congrArg (fun U : Subgroup (localMap K L T z v hL hz).range =>
    U.map (localMap K L T z v hL hz).range.subtype) he
  simp only [Subgroup.map_map] at him
  change (ChapterB.baumann (P : Subgroup (K ⊔ Tv T v : Subgroup G))).map
      (localMap K L T z v hL hz) =
    (elementaryAbelianMaxJ (P : Subgroup (K ⊔ Tv T v : Subgroup G))).map
      (localMap K L T z v hL hz) at him
  have hJ := local_natural_thompson_image_le K L T z v hL hz hK hnorm hF hb s hred hW P
  have hle := map_mono (f := localMap K L T z v hL hz)
    (elementaryAbelianMaxJ_sylow_le_top P)
  have hBi : ChapterB.baumann ((Tv T v).subgroupOf (K ⊔ Tv T v)) =
      (ChapterB.baumann (Tv T v)).subgroupOf (K ⊔ Tv T v) := by
    apply map_injective (K ⊔ Tv T v).subtype_injective
    rw [map_subgroupOf_eq_of_le (show ChapterB.baumann (Tv T v) ≤ K ⊔ Tv T v from
      inf_le_left.trans le_sup_right)]
    have hh := baumann_map_injective (K ⊔ Tv T v).subtype (K ⊔ Tv T v).subtype_injective
      ((Tv T v).subgroupOf (K ⊔ Tv T v))
    rw [map_subgroupOf_eq_of_le (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)] at hh
    exact hh
  rw [←him,hP,hBi,localMap_image K L T z v hL hz (ChapterB.baumann (Tv T v))
      (inf_le_left.trans le_sup_right)] at hle
  exact hle.trans hJ

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
