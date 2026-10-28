module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.Kernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.Noncentral
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Thompson
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PCoreKernelRange
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# The actual local module and residual in the rank-one case

The local actor is H = KT_v. The ambient characteristic-two hypothesis puts
W_K inside T_v, so restriction makes W_K an internal normal elementary
abelian subgroup of H. Its centralizer quotient is the range of localMap,
not the larger plus quotient. The block's two-perfection identifies O²(H)
with K, and functoriality identifies the image of this residual with K⁺.
Thompson noncentrality supplies a genuine FF-offender for the faithful action.

These facts prepare the application of E.2.3. They do not identify the global
Thompson image with K⁺ or assert that the local module is two-reduced.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.18,
printed p.931; B.2.4 and B.2.11–14, pp.75–78; E.2.3, pp.216–217.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
open ComponentSelection
variable {G : Type*} [Group G]

/-- W_K regarded as a subgroup of the actual local actor. -/
def internalWK (K L T : Subgroup G) (z v : G)
    (_hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (_hz : Tv T v ≤ centralizer ({z} : Set G)) : Subgroup (K ⊔ Tv T v : Subgroup G) :=
  (WK K L T z v).subgroupOf (K ⊔ Tv T v)

instance internalWK_normal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (internalWK K L T z v hL hz).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((localActor_le K L T v).trans (plusActor_normalizes_WK K L T z v hL hz))

/-- Restriction of an elementary abelian module is elementary abelian. -/
instance internalWK_elementary (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)] :
    IsElementaryAbelian 2 (internalWK K L T z v hL hz) :=
by
  refine { toIsMulCommutative := subgroupOf_isMulCommutative _ _, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (A := WK K L T z v) _ x.property

/-- Once the actual module lies in H, the restricted kernel is its internal
centralizer. This is the literal kernel needed for E.2.3. -/
theorem localMap_ker_internal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hW : WK K L T z v ≤ K ⊔ Tv T v) :
    (localMap K L T z v hL hz).ker =
      centralizer (internalWK K L T z v hL hz : Set (K ⊔ Tv T v : Subgroup G)) := by
  rw [localMap_ker]
  ext x
  constructor
  · intro hx w hw
    exact Subtype.ext (hx w hw)
  · intro hx w hw
    exact congrArg Subtype.val (hx ⟨w, hW hw⟩ hw)

/-- The surjective action map has the actual range as codomain. -/
def localProjection (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :=
  (localMap K L T z v hL hz).rangeRestrict

theorem localProjection_ker (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hW : WK K L T z v ≤ K ⊔ Tv T v) :
    (localProjection K L T z v hL hz).ker =
      centralizer (internalWK K L T z v hL hz : Set (K ⊔ Tv T v : Subgroup G)) :=
  (MonoidHom.ker_rangeRestrict _).trans (localMap_ker_internal K L T z v hL hz hW)

/-- This equivalence certifies the centralizer quotient convention, without
claiming that localMap surjects onto Gplus. -/
noncomputable def localCentralizerQuotientEquiv (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hW : WK K L T z v ≤ K ⊔ Tv T v) :
    ((K ⊔ Tv T v : Subgroup G) ⧸ centralizer
      (internalWK K L T z v hL hz : Set (K ⊔ Tv T v : Subgroup G))) ≃*
        (localMap K L T z v hL hz).range :=
  (QuotientGroup.quotientMulEquivOfEq
    (localMap_ker_internal K L T z v hL hz hW).symm).trans
      (QuotientGroup.quotientKerEquivRange (localMap K L T z v hL hz))

/-- The faithful binary action on the internal W_K, with its literal
centralizer kernel and surjective projection onto the actual image. -/
noncomputable def localRepresentation (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hW : WK K L T z v ≤ K ⊔ Tv T v) :
    Representation (ZMod 2) (localMap K L T z v hL hz).range
      (Additive (internalWK K L T z v hL hz)) :=
  Representation.NormalElementaryQuotient.representation (internalWK K L T z v hL hz)
    (localProjection K L T z v hL hz) (localMap K L T z v hL hz).rangeRestrict_surjective
    (localProjection_ker K L T z v hL hz hW)

theorem localRepresentation_faithful (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hW : WK K L T z v ≤ K ⊔ Tv T v) :
    Function.Injective (localRepresentation K L T z v hL hz hW) :=
  Representation.NormalElementaryQuotient.representation_injective _ _ _ _

/-- Evaluation of the local quotient representation is ambient conjugation. -/
theorem localRepresentation_apply (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (x : (K ⊔ Tv T v : Subgroup G)) (w : Additive (internalWK K L T z v hL hz)) :
    ((((localRepresentation K L T z v hL hz hW
      (localProjection K L T z v hL hz x) w).toMul :
        (K ⊔ Tv T v : Subgroup G)) : G)) =
      (x : G) * ((w.toMul : (K ⊔ Tv T v : Subgroup G)) : G) * (x : G)⁻¹ := by
  exact congrArg Subtype.val
    (Representation.NormalElementaryQuotient.representation_apply _ _ _ _ x w)

/-- The internal module is the original W_K, with the same multiplication. -/
def internalWKEquiv (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hW : WK K L T z v ≤ K ⊔ Tv T v) :
    internalWK K L T z v hL hz ≃* WK K L T z v := subgroupOfEquivOfLe hW

/-- Restriction to K agrees with the very component action used by the
NaturalSection input. The comparison keeps the actual quotient maps. -/
theorem localRepresentation_component (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (k : K) (w : Additive (internalWK K L T z v hL hz)) :
    internalWKEquiv K L T z v hL hz hW
      ((localRepresentation K L T z v hL hz hW
        (localProjection K L T z v hL hz (inclusion le_sup_left k)) w).toMul) =
      (componentRepresentation K L T z v hL hz (componentMap K L T z v hL hz k)
        (Additive.ofMul (internalWKEquiv K L T z v hL hz hW w.toMul))).toMul := by
  apply Subtype.ext
  rw [componentRepresentation_mk]
  exact localRepresentation_apply K L T z v hL hz hW (inclusion le_sup_left k) w

/-- Thompson subgroups agree under the actual internal embedding. -/
theorem local_thompson_subgroupOf (K T : Subgroup G) (v : G) :
    elementaryAbelianMaxJ ((Tv T v).subgroupOf (K ⊔ Tv T v)) =
      (elementaryAbelianMaxJ (Tv T v)).subgroupOf (K ⊔ Tv T v) := by
  apply map_injective (K ⊔ Tv T v).subtype_injective
  rw [← elementaryAbelianMaxJ_map_injective _ (K ⊔ Tv T v).subtype_injective,
    map_subgroupOf_eq_of_le (show Tv T v ≤ K ⊔ Tv T v from le_sup_right),
    map_subgroupOf_eq_of_le]
  exact (sSup_le fun _ hA => hA.1).trans le_sup_right

/-- The source local-family Sylow is the actual internal T_v. -/
theorem exists_localSylow (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) :
    ∃ P : Sylow 2 (K ⊔ Tv T v : Subgroup G),
      (P : Subgroup (K ⊔ Tv T v : Subgroup G)) = (Tv T v).subgroupOf (K ⊔ Tv T v) := by
  obtain ⟨P, hP⟩ := hK.1.2.2.1
  refine ⟨P, ?_⟩
  apply map_injective (K ⊔ Tv T v).subtype_injective
  rw [hP, map_subgroupOf_eq_of_le (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)]

variable [Finite G]

/-- The earlier characteristic-two centralizer and Sylow seed place W_K
inside the original T_v, before any Borel normalization is known. -/
theorem WK_le_Tv (K L T : Subgroup G) (z v : G) (hK : K ≤ Gv v)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hz : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    WK K L T z v ≤ Tv T v := by
  have hU := (WK_le_Uv K L T z v hK).trans (Uv_le_coreOmega T z v hSylow hz hf)
  obtain ⟨P, hP⟩ := hSylow
  intro w hw
  have hQ := ((mem_omegaOneCenterAmbient_iff _ _).mp (hU hw)).1
  obtain ⟨q, hq, rfl⟩ := hQ
  exact hP ▸ mem_map_of_mem (Gv v).subtype (pCore_isPGroup.le_sylow_of_normal P hq)

/-- The actual SQTK hypothesis is inherited from the earlier centralizer. -/
theorem local_sqtk (K T : Subgroup G) (v : G) (hK : K ≤ Gv v)
    {𝒞 : GroupClass} (hq : IsSQTK 𝒞 (Gv v)) :
    IsSQTK 𝒞 (K ⊔ Tv T v : Subgroup G) := by
  have hHG : K ⊔ Tv T v ≤ Gv v := sup_le hK inf_le_right
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hHG)).mp
    (hq.subgroup ((K ⊔ Tv T v).subgroupOf (Gv v)))

/-- Characteristic two passes from G_v to its actual Sylow overgroup KT_v. -/
theorem local_fitting_eq (K T : Subgroup G) (v : G) (hK : K ≤ Gv v)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    Theory.GroupTheory.generalizedFitting (K ⊔ Tv T v : Subgroup G) =
      pCore 2 (K ⊔ Tv T v : Subgroup G) := by
  let H := K ⊔ Tv T v
  have hHG : H ≤ Gv v := sup_le hK inf_le_right
  obtain ⟨P, hP⟩ := hSylow
  have hPH : (P : Subgroup (Gv v)) ≤ H.subgroupOf (Gv v) := by
    intro x hx
    exact (show Tv T v ≤ H from le_sup_right)
      (hP ▸ mem_map_of_mem (Gv v).subtype hx)
  have hF := (ChapterA.lemma_A_1_6 P (H.subgroupOf (Gv v)) hPH hf).2
  apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hHG)).mp
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hF)

omit [Finite G] in
/-- The block is the intrinsic two-residual of KT_v. -/
theorem local_residual_eq (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    {n : ℕ} (hb : ChapterC.IsL2EvenBlock K n) :
    pResidual 2 (K ⊔ Tv T v : Subgroup G) = K.subgroupOf (K ⊔ Tv T v) := by
  let H := K ⊔ Tv T v
  let C := K.subgroupOf H
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hnorm)
  let e : C ≃* K := subgroupOfEquivOfLe le_sup_left
  apply pResidual_eq_of_isPPerfect_sup C ((Tv T v).subgroupOf H)
    (hb.2.1.twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective)
    ((Chapter1.isSylowIn_iff.mp hK.1.2.2.1).1.comap_subtype)
  rw [← subgroupOf_sup (show K ≤ H from le_sup_left)
    (show Tv T v ≤ H from le_sup_right)]
  exact subgroupOf_self _

/-- The actual O² of the local action range has ambient image K⁺.
No Thompson subgroup is identified in this statement. -/
theorem localRange_residual_image (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    {n : ℕ} (hb : ChapterC.IsL2EvenBlock K n) :
    (pResidual 2 (localMap K L T z v hL hz).range).map
      (localMap K L T z v hL hz).range.subtype = plusImage K L T z v hL hz K := by
  rw [← map_pResidual_of_surjective 2 _
    (localMap K L T z v hL hz).rangeRestrict_surjective, map_map]
  change (pResidual 2 (K ⊔ Tv T v : Subgroup G)).map
    (localMap K L T z v hL hz) = _
  rw [local_residual_eq K L T z v hK hnorm hb,
    localMap_image K L T z v hL hz K le_sup_left]

/-- In this exact action, two-reducedness is equivalent to centralization
by the local two-core. The known two-group kernel supplies the reverse
inclusion; it does not supply the centralization asserted on the right. -/
theorem localReduced_iff_core_centralizes (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : Matrix.SpecialLinearGroup.RankOneResidual.NaturalSection (F := F)
      (componentRepresentation K L T z v hL hz) (movingSpace K L T z v))
    (hW : WK K L T z v ≤ K ⊔ Tv T v) :
    pCore 2 (localMap K L T z v hL hz).range = ⊥ ↔
      pCore 2 (K ⊔ Tv T v : Subgroup G) ≤
        centralizer (internalWK K L T z v hL hz : Set (K ⊔ Tv T v : Subgroup G)) := by
  rw [← localMap_ker_internal K L T z v hL hz hW]
  have hk := localMap_kernel_isPGroup K L T z v hL hz hK hnorm hF hb s
  constructor
  · intro hr
    exact ((localMap K L T z v hL hz).ker_eq_pCore_of_range_core_eq_bot 2 hk hr).ge
  · intro hc
    exact pCore_range_eq_bot_of_ker_eq_pCore 2 (localMap K L T z v hL hz)
      (le_antisymm (le_sSup ⟨inferInstance, hk⟩) hc)

/-- The 13.6.16 characteristic-normalizer obstruction supplies a genuine
FF-offender for the faithful local action. The source R₂ condition remains
separate from this counting argument. -/
theorem localRepresentation_isFFModule (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : Matrix.SpecialLinearGroup.RankOneResidual.NaturalSection (F := F)
      (componentRepresentation K L T z v hL hz) (movingSpace K L T z v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction (Tv T v) K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    Representation.BinaryOffender.IsFFModule
      (localRepresentation K L T z v hL hz
        ((WK_le_Tv K L T z v hK.1.1 hSylow hzOmega hf).trans le_sup_right)) := by
  have hWT := WK_le_Tv K L T z v hK.1.1 hSylow hzOmega hf
  apply Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
    (internalWK K L T z v hL hz) (localProjection K L T z v hL hz)
    (localMap K L T z v hL hz).rangeRestrict_surjective
    (localProjection_ker K L T z v hL hz (hWT.trans le_sup_right))
    ((Tv T v).subgroupOf (K ⊔ Tv T v)) (comap_mono hWT)
  rw [local_thompson_subgroupOf, localProjection, MonoidHom.ker_rangeRestrict, localMap_ker]
  intro h
  apply local_thompson_noncentral K L T z v hL hz hK hnorm hF hb s hzOmega hpush
  intro x hx
  have hxH : x ∈ K ⊔ Tv T v :=
    (show Tv T v ≤ K ⊔ Tv T v from le_sup_right)
      ((show elementaryAbelianMaxJ (Tv T v) ≤ Tv T v from
        sSup_le fun _ hA => hA.1) hx)
  exact h (show (⟨x, hxH⟩ : (K ⊔ Tv T v : Subgroup G)) ∈
    (elementaryAbelianMaxJ (Tv T v)).subgroupOf (K ⊔ Tv T v) from hx)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
end
