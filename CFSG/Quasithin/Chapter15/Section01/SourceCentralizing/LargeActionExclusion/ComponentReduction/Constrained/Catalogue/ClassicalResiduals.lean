module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalQuotients
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Selection
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ActionImage
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary

/-!
# The classical parabolic residuals in the original FF action

For every constrained escaping local member K, use its actual action on
U=⟨Z^{K N_S(K)}⟩ and its literal centralizer quotient. A marking of K* as
SL₃ or Sp₄ defines the two full parabolic preimages in K N_S(K). Their
solvable residuals lie in K and map to the original model residuals.

Both model residuals are nontrivial and have characteristic two. The
short-layer argument in `BlockStructure.ActionImage` therefore proves that
both preimage residuals are not short, retaining the original seed and any
central action kernel. No ambient componenthood or S-normality of K is
assumed. The original marker and later exchanged source supply the action.

Source: Aschbacher--Smith 15.1.20(2), printed p.1095; the concrete local
models are F.1.12(I), printed pp.262--264. Local-family membership, rank-one
core quotients and generation must still be assembled to exclude these FF
rows. General Borel placement and the remaining block/parabolic catalogue
remain obligations of this source-catalogue task. Original 15.1.14 stays
with its existing owner and the pre-exclusion assembly.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section01.ClassicalResidualAction
open Subgroup Theory.GroupTheory
variable {G D : Type*} [Group G] [Finite G] [Group D]
variable (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
variable (f : G →* D) (hf : Function.Surjective f)
  (hker : f.ker = centralizer (U : Set G))
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
open scoped MatrixGroups
include U hf hker
open Matrix.PSL3.LinearThree in

/-- Both actual linear-three parabolic preimages have nonshort residuals. -/
theorem linear_three (j : SL(3,F) →* D) (hj : Function.Injective j)
    (hF : 4 ≤ Nat.card F) :
    (¬ ChapterC.IsShort (solvableResidual (((pointParabolicSL F).map j).comap f))) ∧
    (¬ ChapterC.IsShort (solvableResidual (((lineParabolicSL F).map j).comap f))) := by
  let : IsSimpleGroup SL(2,F) :=
    Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple (by omega)
  have hp : pointLocalSL F ≠ ⊥ := by
    let : Nontrivial (pointLocalSL F) :=
      Function.Surjective.nontrivial ((pointLocalSLCoreQuotientEquiv F).surjective.comp
        (QuotientGroup.mk'_surjective _))
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  have hl : lineLocalSL F ≠ ⊥ := by
    let : Nontrivial (lineLocalSL F) :=
      Function.Surjective.nontrivial ((lineLocalSLCoreQuotientEquiv F).surjective.comp
        (QuotientGroup.mk'_surjective _))
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  exact ⟨ChapterC.not_isShort_residual_preimage_of_model U f hf hker j hj
      (pointParabolicSL F) (pointLocalSL F) (pointParabolicSL_residual F hF)
      hp (pointLocalSL_generalizedFitting_eq_twoCore F),
    ChapterC.not_isShort_residual_preimage_of_model U f hf hker j hj
      (lineParabolicSL F) (lineLocalSL F) (lineParabolicSL_residual F hF)
      hl (lineLocalSL_generalizedFitting_eq_twoCore F)⟩

open Theory.SpecificGroups.SymplecticFour
/-- Both actual symplectic-four parabolic preimages have nonshort residuals. -/
theorem symplectic_four (j : Sp F →* D) (hj : Function.Injective j)
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    (¬ ChapterC.IsShort (solvableResidual ((pointParabolic.map j).comap f))) ∧
    (¬ ChapterC.IsShort (solvableResidual ((planeParabolic.map j).comap f))) := by
  have hgt : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 = 2^1 by decide).trans_lt (Nat.pow_lt_pow_right (by decide) hn)
  let : IsSimpleGroup SL(2,F) := NaturalExtension.model_simple hgt
  have hp : pointLocal (F := F) ≠ ⊥ := by
    let : Nontrivial (pointLocal (F := F)) :=
      Function.Surjective.nontrivial (pointQuotient_surjective (F := F))
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  have hl : planeLocal (F := F) ≠ ⊥ := by
    let : Nontrivial (planeLocal (F := F)) :=
      Function.Surjective.nontrivial (Plane.quotientMap_surjective (F := F))
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  exact ⟨ChapterC.not_isShort_residual_preimage_of_model U f hf hker j hj
      pointParabolic pointLocal (pointParabolic_solvableResidual_eq hF hn)
      hp ((pointNaturalExtension hF hn).generalizedFitting_eq hgt),
    ChapterC.not_isShort_residual_preimage_of_model U f hf hker j hj
      planeParabolic planeLocal (planeParabolic_solvableResidual_eq hF hn)
      hl ((planeNaturalExtension hF hn).generalizedFitting_eq hgt)⟩
end CFSG.Quasithin.Chapter15.Section01.ClassicalResidualAction

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The literal preimage in H=K N_S(K) of a parabolic of K*. -/
@[expose] def normalizerParabolic (d : CaseIComponentData T M Mc V)
    (K : Subgroup G) (P : Subgroup (d.normalizerImage K)) :
    Subgroup (K ⊔ d.normalizerSylow K : Subgroup G) :=
  (P.map (d.normalizerImage K).subtype).comap
    (QuotientGroup.mk' (centralizer (d.normalizerModule K :
      Set (K ⊔ d.normalizerSylow K : Subgroup G))))

/-- The solvable residual of that preimage, embedded in the original G. -/
@[expose] def normalizerParabolicResidual (d : CaseIComponentData T M Mc V)
    (K : Subgroup G) (P : Subgroup (d.normalizerImage K)) : Subgroup G :=
  (solvableResidual (d.normalizerParabolic K P)).map
    ((K ⊔ d.normalizerSylow K).subtype.comp (d.normalizerParabolic K P).subtype)

/-- The construction is the residual of the same ambient parabolic. -/
theorem normalizerParabolicResidual_eq (d : CaseIComponentData T M Mc V)
    (K : Subgroup G) (P : Subgroup (d.normalizerImage K)) :
    d.normalizerParabolicResidual K P =
      (solvableResidual ((d.normalizerParabolic K P).map
        (K ⊔ d.normalizerSylow K).subtype)).map
          ((d.normalizerParabolic K P).map (K ⊔ d.normalizerSylow K).subtype).subtype := by
  rw [normalizerParabolicResidual,←map_map,map_embedded_solvableResidual_of_hom]

/-- Residual images use the literal quotient map on H and the original K*. -/
theorem normalizerParabolic_residual_image (d : CaseIComponentData T M Mc V)
    (K : Subgroup G) (P : Subgroup (d.normalizerImage K)) :
    ((solvableResidual (d.normalizerParabolic K P)).map
      (d.normalizerParabolic K P).subtype).map
      (QuotientGroup.mk' (centralizer (d.normalizerModule K :
        Set (K ⊔ d.normalizerSylow K : Subgroup G)))) =
      ((solvableResidual P).map P.subtype).map (d.normalizerImage K).subtype := by
  rw [normalizerParabolic,map_solvableResidual_comap _ (QuotientGroup.mk'_surjective _),
    ←map_embedded_solvableResidual_of_hom]

/-- Every constructed parabolic residual lies in the original perfect K. -/
theorem normalizerParabolicResidual_le (d : CaseIComponentData T M Mc V)
    (K : Subgroup G) [Group.IsPerfect K] (P : Subgroup (d.normalizerImage K)) :
    d.normalizerParabolicResidual K P ≤ K := by
  let H := K ⊔ d.normalizerSylow K
  let K0 := K.subgroupOf H
  let R := (d.normalizerSylow K).subgroupOf H
  let : K0.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer inf_le_right)
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect K0 := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hgen : K0 ⊔ R = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show d.normalizerSylow K ≤ H from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  have hp : IsPGroup 2 R :=
    (T.isPGroup'.to_le (show d.normalizerSylow K ≤ T from inf_le_left.trans d.S_le_T)).comap_subtype
  have hres := (residuals_of_perfect_normal_sup_twoGroup K0 R hp hgen).2
  have hh := map_mono (f := H.subtype)
    ((map_solvableResidual_le (d.normalizerParabolic K P).subtype).trans hres.le)
  rw [map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),map_map] at hh
  exact hh

private theorem normalizerParabolicResidual_not_short
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (P : Subgroup (d.normalizerImage K))
    (hn : ¬ ChapterC.IsShort (solvableResidual (d.normalizerParabolic K P))) :
    ¬ ChapterC.IsShort (d.normalizerParabolicResidual K P) := by
  let H := K ⊔ d.normalizerSylow K
  let j := H.subtype.comp (d.normalizerParabolic K P).subtype
  let e := (solvableResidual (d.normalizerParabolic K P)).equivMapOfInjective j
    (H.subtype_injective.comp (d.normalizerParabolic K P).subtype_injective)
  exact fun hs => hn (ChapterC.RankOne.Solvable.isShort_of_equiv e.symm hs)

private theorem normalizerParabolicResidual_model_not_short
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    {E : Type*} [Group E] (e : d.normalizerImage K ≃* E) (P : Subgroup E)
    (hn : ¬ ChapterC.IsShort (solvableResidual
      ((P.map ((d.normalizerImage K).subtype.comp e.symm.toMonoidHom)).comap
        (QuotientGroup.mk' (centralizer (d.normalizerModule K :
          Set (K ⊔ d.normalizerSylow K : Subgroup G))))))) :
    ¬ ChapterC.IsShort (d.normalizerParabolicResidual K (P.map e.symm.toMonoidHom)) := by
  apply normalizerParabolicResidual_not_short
  have he : d.normalizerParabolic K (P.map e.symm.toMonoidHom) =
      (P.map ((d.normalizerImage K).subtype.comp e.symm.toMonoidHom)).comap
        (QuotientGroup.mk' (centralizer (d.normalizerModule K :
          Set (K ⊔ d.normalizerSylow K : Subgroup G)))) := by
    unfold normalizerParabolic
    rw [map_map]
  let er := (MulEquiv.subgroupCongr he).solvableResidualEquiv
  exact fun hs => hn (ChapterC.RankOne.Solvable.isShort_of_equiv er hs)

open scoped MatrixGroups
/-- The two SL₃ residuals of the original FF action are not short groups.
The preimages retain H, U and the chosen model equivalence. -/
theorem NormalizerAction.linear_three_residuals_not_short
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} (a : d.NormalizerAction K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* SL(3,F)) (hF : 4 ≤ Nat.card F) :
    (¬ ChapterC.IsShort (d.normalizerParabolicResidual K
      ((Matrix.PSL3.LinearThree.pointParabolicSL F).map e.symm.toMonoidHom))) ∧
    (¬ ChapterC.IsShort (d.normalizerParabolicResidual K
      ((Matrix.PSL3.LinearThree.lineParabolicSL F).map e.symm.toMonoidHom))) := by
  let := a.reduced.elementary
  let q := QuotientGroup.mk' (centralizer (d.normalizerModule K :
    Set (K ⊔ d.normalizerSylow K : Subgroup G)))
  let j := (d.normalizerImage K).subtype.comp e.symm.toMonoidHom
  have hh := ClassicalResidualAction.linear_three (d.normalizerModule K) q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    j ((d.normalizerImage K).subtype_injective.comp e.symm.injective) hF
  exact ⟨normalizerParabolicResidual_model_not_short e _ hh.1,
    normalizerParabolicResidual_model_not_short e _ hh.2⟩

/-- The two Sp₄ residuals of the original FF action are not short groups,
including field size four and without assuming a two-group action kernel. -/
theorem NormalizerAction.symplectic_four_residuals_not_short
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} (a : d.NormalizerAction K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    (¬ ChapterC.IsShort (d.normalizerParabolicResidual K
      (Theory.SpecificGroups.SymplecticFour.pointParabolic.map e.symm.toMonoidHom))) ∧
    (¬ ChapterC.IsShort (d.normalizerParabolicResidual K
      (Theory.SpecificGroups.SymplecticFour.planeParabolic.map e.symm.toMonoidHom))) := by
  let := a.reduced.elementary
  let q := QuotientGroup.mk' (centralizer (d.normalizerModule K :
    Set (K ⊔ d.normalizerSylow K : Subgroup G)))
  let j := (d.normalizerImage K).subtype.comp e.symm.toMonoidHom
  have hh := ClassicalResidualAction.symplectic_four (d.normalizerModule K) q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    j ((d.normalizerImage K).subtype_injective.comp e.symm.injective) hF hn
  exact ⟨normalizerParabolicResidual_model_not_short e _ hh.1,
    normalizerParabolicResidual_model_not_short e _ hh.2⟩
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The nonblock clause for both pairs of literal higher-field parabolic
residuals. Every model marking is on the original normalizer action image. -/
@[expose] def ClassicalResidualsNonshort (d : CaseIComponentData T M Mc V)
    (K : Subgroup G) : Prop :=
  (∀ (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* SL(3,F)), 4 ≤ Nat.card F →
      (¬ ChapterC.IsShort (d.normalizerParabolicResidual K
        ((Matrix.PSL3.LinearThree.pointParabolicSL F).map e.symm.toMonoidHom))) ∧
      (¬ ChapterC.IsShort (d.normalizerParabolicResidual K
        ((Matrix.PSL3.LinearThree.lineParabolicSL F).map e.symm.toMonoidHom)))) ∧
  (∀ (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (n : ℕ), Nat.card F = 2^n → 1 < n →
      (¬ ChapterC.IsShort (d.normalizerParabolicResidual K
        (Theory.SpecificGroups.SymplecticFour.pointParabolic.map e.symm.toMonoidHom))) ∧
      (¬ ChapterC.IsShort (d.normalizerParabolicResidual K
        (Theory.SpecificGroups.SymplecticFour.planeParabolic.map e.symm.toMonoidHom))))

/-- The actual reduced FF action proves both classical nonblock clauses. -/
theorem NormalizerAction.classical_residuals_not_short
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} (a : d.NormalizerAction K) :
    d.ClassicalResidualsNonshort K :=
  ⟨fun _ _ _ _ e hF => a.linear_three_residuals_not_short e hF,
    fun _ _ _ _ e _ hF hn => a.symplectic_four_residuals_not_short e hF hn⟩

/-- The original local family supplies the actual action. K need not be an
ambient C-component or be normalized by all of S. -/
theorem localFamily_classical_residuals_not_short (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) : d.ClassicalResidualsNonshort K :=
  (d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf).classical_residuals_not_short

/-- Both original pre-exclusion primes retain the same literal residuals. -/
theorem PreExclusionSource.constrained_classical_residuals_not_short
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) : d.ClassicalResidualsNonshort d.L :=
  d.localFamily_classical_residuals_not_short hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf

/-- The exchanged source uses the same nonblock proof on both plane sizes. -/
theorem ExchangedSource.constrained_classical_residuals_not_short
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L) : d.ClassicalResidualsNonshort d.L :=
  d.localFamily_classical_residuals_not_short hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original-marker application of the classical parabolic nonblock argument.
The selected Z₁, row and prime remain fixed. Original 15.1.14 stays explicit
for the pre-exclusion assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_classical_residuals_not_short
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L → d.ClassicalResidualsNonshort d.L) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf =>
    s.constrained_classical_residuals_not_short (h := h) hG hempty hM hJ hu hf⟩
end CFSG.Quasithin.Chapter15.Section01

