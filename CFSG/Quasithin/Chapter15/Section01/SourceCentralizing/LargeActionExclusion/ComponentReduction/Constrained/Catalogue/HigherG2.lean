module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.HigherFieldApplications
public import Theory.GroupTheory.SolvableResidual.ParabolicGeneration
public import Theory.GroupTheory.CComponent.CenterlessRankNormal
public import Theory.SpecificGroups.G2Even.MarkedCover

/-!
# Excluding higher-field G₂ from the constrained FF catalogue

For every original local-family member with core quotient G₂(2ⁿ), n > 1,
cubic rank forces normalization by S. Align its Sylow with the model Sylow
and take the literal preimages of both full root parabolics. Their solvable
residuals have characteristic two, PSL₂(2ⁿ) core quotients, and nonzero core
triple commutators. They therefore belong to the same original local family
and are not short blocks. The rank-one nonblock theorem places both in M_Z.

A common solvable Borel supplement proves that these residuals generate the
original group even when the quotient kernel is not central. Thus the whole
member lies in M_Z. For the actual constrained FF image, the two-primary G₂
multiplier kills the possible extra central kernel after dividing by O₂,
including at field size four, and retains the original quotient marking.
This excludes the higher-field G₂ row of B.5.1 without any ambient component
hypothesis. Original-marker and exchanged-source consumers use this result.

Source: Aschbacher--Smith 15.1.20(2), printed p.1095; A.3.8(3) for normality;
I.1.1--4 for the covering kernel. The root calculations are supplied by the
licensed ATLAS port (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
The remaining SL₃/Sp₄ field exclusions, general Borel placement, and block
and parabolic catalogue assembly stay with this source-catalogue task.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.HigherFieldResiduals
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem g2_preimage_residuals_generate
    {X F : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    [Field F] [Finite F] [CharP F 2]
    (q : X →* Model F) (hq : Function.Surjective q) (hF : 2 < Nat.card F)
    (hk : IsPGroup 2 q.ker) :
    (solvableResidual ((parabolicAt 0).comap q)).map ((parabolicAt 0).comap q).subtype ⊔
      (solvableResidual ((parabolicAt 1).comap q)).map ((parabolicAt 1).comap q).subtype = ⊤ := by
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  let : Group.IsSolvable (borel (K := F)) := DerivedNormalizerSolvable.isSolvable_borel
  apply preimage_residuals_sup_eq_top q hq parabolic₁ parabolic₂ borel
    borel_le_parabolic₁ borel_le_parabolic₂ parabolics_generate
  · rw [parabolic₁_residual hF, local₁_sup_borel]
  · rw [parabolic₂_residual hF, local₂_sup_borel]

private theorem localFamily_G2_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    {L : Subgroup G} (hL : L ∈ Chapter1.LIn d.G1 d.S)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (L ⧸ pCore 2 L) ≃* Model F) : d.S ≤ normalizer (L : Set G) := by
  let := h.elementary
  let : Fact (2 < Nat.card F) := ⟨hF⟩
  let J := L ⊔ d.S
  have hJG : J ≤ d.G1 := sup_le hL.1 d.S_le_G1
  have hsq := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJG)).mp (hsq.subgroup (J.subgroupOf d.G1))
  let ec : L.subgroupOf J ≃* L := subgroupOfEquivOfLe le_sup_left
  let eq : ((L.subgroupOf J) ⧸ pCore 2 (L.subgroupOf J)) ≃* Model F :=
    (QuotientGroup.congr _ _ ec (pCore_map_iso 2 ec)).trans e
  let : IsQuasisimple ((L.subgroupOf J) ⧸ pCore 2 (L.subgroupOf J)) :=
    IsQuasisimple.of_mulEquiv eq.symm
  have hz : center ((L.subgroupOf J) ⧸ pCore 2 (L.subgroupOf J)) = ⊥ := by
    let : IsSimpleGroup ((L.subgroupOf J) ⧸ pCore 2 (L.subgroupOf J)) := eq.isSimpleGroup
    rcases (inferInstance : (center ((L.subgroupOf J) ⧸ pCore 2 (L.subgroupOf J))).Normal).eq_bot_or_eq_top with he | he
    · exact he
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he)).elim
  have hr : 2 ≤ primeRank 3 ((L.subgroupOf J) ⧸ pCore 2 (L.subgroupOf J)) := by
    rw [primeRank_equiv 3 eq]
    exact EvenThreeRank.two_le_primeRank
  have hn : (L.subgroupOf J).Normal := hL.2.1.normal_of_centerless_core_threeRank hz hr
    (hsqJ.stronglyQuasithin 3 Nat.prime_three (by decide))
  exact (show d.S ≤ J from le_sup_right).trans
    ((normal_subgroupOf_iff_le_normalizer (show L ≤ J from le_sup_left)).mp hn)

/-- Both literal parabolics and their nonblock residuals, on one common marking. -/
structure LocalG2Residuals (d : CaseIComponentData T M Mc V) (L : Subgroup G) (q : ℕ) where
  parabolic : Fin 2 → Subgroup G
  factor : Fin 2 → Subgroup G
  parabolic_le : ∀ i, parabolic i ≤ L
  parabolic_proper : ∀ i, parabolic i ≠ L
  sylow_le : ∀ i, (d.S ⊓ L) ≤ parabolic i
  normalized : ∀ i, d.S ≤ normalizer (parabolic i : Set G)
  residual : ∀ i, (solvableResidual (parabolic i)).map (parabolic i).subtype = factor i
  family : ∀ i, factor i ∈ Chapter1.LIn d.G1 d.S
  fitting : ∀ i, generalizedFitting (factor i) = pCore 2 (factor i)
  not_short : ∀ i, ¬ ChapterC.IsShort (factor i)
  quotient : ∀ i, ClassicalGroup.IsPSL (factor i ⧸ pCore 2 (factor i)) 2 q
  generated : factor 0 ⊔ factor 1 = L

/-- Both higher-field G₂ residuals for an arbitrary original local-family member. -/
theorem localFamily_G2_residuals (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    {L : Subgroup G} (hL : L ∈ Chapter1.LIn d.G1 d.S)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (e : (L ⧸ pCore 2 L) ≃* Model F) :
    Nonempty (d.LocalG2Residuals L (Nat.card F)) := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect hL.2
  have hnL := localFamily_G2_normalizes d hG h hL (by omega) e
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hL.2
  let q₀ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let U₀ := Q.mapSurjective hq₀
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) U₀ (sylow (F := F))
  let e' := e.trans (MulAut.conj g)
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hsur : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,QuotientGroup.ker_mk']
  have hk : IsPGroup 2 q.ker := hker ▸ pCore_isPGroup
  have hU : (Q : Subgroup L).map q = unipotent := by
    have hh := congrArg (fun U : Sylow 2 (Model F) => (U : Subgroup (Model F))) hg
    change ((Q : Subgroup L).map q₀).map (MulAut.conj g).toMonoidHom = unipotent at hh
    rw [map_map] at hh
    exact hh
  have hQL : (Q : Subgroup L) = (d.S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show (d.S ⊓ L) ≤ L from inf_le_right)]
    exact hQ
  let α : d.S →* MulAut (Model F) := (MulAut.congr e').toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hnL)))
  have heq (a : d.S) (l : L) :
      q (L.normalizerMonoidHom (inclusion hnL a) l) = α a (q l) := by
    change e' (QuotientGroup.mk' _ _) = e' (quotientAut _ _ (e'.symm (e' _)))
    rw [e'.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hnSL : d.S ≤ normalizer ((d.S ⊓ L) : Set G) :=
    (le_inf d.S.le_normalizer hnL).trans inf_normalizer_le_normalizer_inf
  have hUi (a : d.S) : unipotent.map (α a).toMonoidHom = unipotent := by
    have hh := EquivariantLift.map_invariant L q hnL α heq (D := d.S ⊓ L) hnSL a
    rw [←hQL,hU] at hh
    exact hh
  let P₀ := fun i : Fin 2 => (parabolicAt (F := F) i).comap q
  let B := fun i : Fin 2 => (P₀ i).map L.subtype
  let K := fun i : Fin 2 => (solvableResidual (B i)).map (B i).subtype
  let R := fun i : Fin 2 => solvableResidual (P₀ i)
  let ek (i : Fin 2) : R i ≃* K i :=
    (((P₀ i).equivMapOfInjective L.subtype L.subtype_injective).solvableResidualEquiv).trans
      ((solvableResidual (B i)).equivMapOfInjective (B i).subtype (B i).subtype_injective)
  have hBL (i : Fin 2) : B i ≤ L := map_subtype_le _
  have hnB (i : Fin 2) : d.S ≤ normalizer (B i : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    obtain ⟨l,hl,rfl⟩ := hx
    let a₀ : d.S := ⟨a,ha⟩
    refine ⟨L.normalizerMonoidHom (inclusion hnL a₀) l,?_,rfl⟩
    change q (L.normalizerMonoidHom (inclusion hnL a₀) l) ∈ parabolicAt i
    rw [heq]
    exact parabolicAt_invariant (α a₀) (hUi a₀) i ▸ mem_map_of_mem (α a₀).toMonoidHom hl
  have hnK (i : Fin 2) : d.S ≤ normalizer (K i : Set G) :=
    (hnB i).trans (normalizer_le_normalizer_characteristic_image (B i) (solvableResidual (B i)))
  have hKL (i : Fin 2) : K i ≤ L := (map_subtype_le _).trans (hBL i)
  let eq (i : Fin 2) : (K i ⧸ pCore 2 (K i)) ≃* PSL(2,F) :=
    (QuotientGroup.congr _ _ (ek i).symm (pCore_map_iso 2 (ek i).symm)).trans
      (preimageResidualCoreQuotientEquivPSL q hsur (by omega) hk i)
  have htriple (i : Fin 2) :
      ⁅⁅pCore 2 (K i), (⊤ : Subgroup (K i))⁆, pCore 2 (K i)⁆ ≠ ⊥ := by
    intro hh
    have hm := congrArg (Subgroup.map (ek i).symm.toMonoidHom) hh
    rw [map_commutator,map_commutator,pCore_map_iso,←MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (ek i).symm.surjective,Subgroup.map_bot] at hm
    exact preimage_residual_core_triple q hsur (by omega) hk i hm
  have hfit (i : Fin 2) : generalizedFitting (K i) = pCore 2 (K i) := by
    rw [←map_generalizedFitting_equiv (ek i),←pCore_map_iso 2 (ek i)]
    congr 1
    exact preimage_residual_generalizedFitting q hsur (by omega) hk i
  have hfamily (i : Fin 2) : K i ∈ Chapter1.LIn d.G1 d.S := by
    let : Group.IsPerfect (K i) :=
      Group.IsPerfect.ofSurjective (f := (ek i).toMonoidHom) (ek i).surjective
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq
    let : IsSimpleGroup (K i ⧸ pCore 2 (K i)) := (eq i).isSimpleGroup
    have hz : center (K i ⧸ pCore 2 (K i)) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (center (K i ⧸ pCore 2 (K i))) inferInstance with hh | hh
      · exact hh
      · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hh)).elim
    let : IsQuasisimple (K i ⧸ pCore 2 (K i)) :=
      { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
    have hc : (K i).pCoreIn 2 ≠ ⊥ := by
      intro hh
      have hb : pCore 2 (K i) = ⊥ := (map_eq_bot_iff_of_injective _ (K i).subtype_injective).mp hh
      exact htriple i (by rw [hb,commutator_bot_left,commutator_bot_left])
    exact ⟨(hKL i).trans hL.1,
      (Chapter1.mem_LIn_of_normalized_perfect hL.2.2.1
        ((hKL i).trans le_sup_left) (hnK i) hc).2⟩
  refine ⟨⟨B,K,hBL,?_,?_,hnB,(fun _ => rfl),hfamily,hfit,?_,?_,?_⟩⟩
  · intro i hb
    have hh : P₀ i = ⊤ := by
      apply map_injective L.subtype_injective
      rw [←MonoidHom.range_eq_map,range_subtype]
      exact hb
    have hm := congrArg (Subgroup.map q) hh
    rw [map_comap_eq_self_of_surjective hsur,←MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hsur] at hm
    exact (parabolicAt_isCoatom (F := F) i).ne_top hm
  · intro i
    rw [←hQ]
    apply map_mono
    intro x hx
    exact unipotent_le_parabolicAt i (hU ▸ mem_map_of_mem q hx)
  · intro i hs
    exact htriple i (commutator_eq_bot_iff_le_centralizer.mpr hs.central)
  · intro i
    exact ⟨F,inferInstance,inferInstance,rfl,⟨eq i⟩⟩
  · have hm := congrArg (Subgroup.map L.subtype)
      (g2_preimage_residuals_generate q hsur (by omega) hk)
    rw [Subgroup.map_sup,map_embedded_solvableResidual_of_hom,
      map_embedded_solvableResidual_of_hom,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm


/-- The actual G₂ FF map has no residual central kernel after dividing by O₂. -/
theorem NormalizerAction.G2_core_marking {d : CaseIComponentData T M Mc V}
    {K : Subgroup G} (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : d.normalizerImage K ≃* Model F) :
    ∃ j : (K ⧸ pCore 2 K) ≃* Model F,
      ∀ x : K, j (QuotientGroup.mk' (pCore 2 K) x) = e (d.toNormalizerImage K x) := by
  let := hq
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  let : Fact (2 < Nat.card F) := ⟨by omega⟩
  let c : Covering (K ⧸ pCore 2 K) (Model F) :=
    ⟨e.toMonoidHom.comp a.coreToImage, e.surjective.comp a.coreToImage_surjective⟩
  have hi : Function.Injective c.toMonoidHom :=
    (FiniteCover.cover_isUniversal F).injective_of_pGroup_kernel
      (FiniteCover.universalKernel_isPGroup_of_card_pow hF hn) c
      (pCore_quotient_pCore_eq_bot 2)
  exact ⟨MulEquiv.ofBijective c.toMonoidHom ⟨hi,c.surjective⟩,fun _ => rfl⟩

/-- The two actual nonblock residuals force the entire higher-field G₂ local
member into M_Z, with no ordinary-component or ambient normality premise. -/
theorem localFamily_G2_le_MZ (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (K ⧸ pCore 2 K) ≃* Model F) : K ≤ d.MZ := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  obtain ⟨r⟩ := d.localFamily_G2_residuals hG h hK hfour e
  have hi (i : Fin 2) : r.factor i ≤ d.MZ :=
    d.localFamily_nonshort_PSL2_le_MZ hG hempty hM hJ hu h
      (r.family i) (r.fitting i) (r.not_short i) n hn (hF ▸ r.quotient i)
  rw [←r.generated]
  exact sup_le (hi 0) (hi 1)

/-- Eliminate the higher-field G₂ row of the literal constrained FF image. -/
theorem localFamily_normalizerImage_not_G2 (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) {n : ℕ} (hn : 1 < n) :
    ¬ IsG2At (d.normalizerImage K) (2^n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  obtain ⟨j,_⟩ := a.G2_core_marking hq hF hn e
  exact hout (d.localFamily_G2_le_MZ hG hempty hM hJ hu h hK hF hn j)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}

/-- The original selected component excludes the higher-field G₂ FF row,
retaining either original pre-exclusion prime. -/
theorem PreExclusionSource.constrained_normalizerImage_not_G2
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) {n : ℕ} (hn : 1 < n) :
    ¬ IsG2At (d.normalizerImage d.L) (2^n) :=
  d.localFamily_normalizerImage_not_G2 hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf hn

/-- The same exclusion for the later exchanged source, on both plane sizes. -/
theorem ExchangedSource.constrained_normalizerImage_not_G2
    (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L) {n : ℕ} (hn : 1 < n) :
    ¬ IsG2At (d.normalizerImage d.L) (2^n) :=
  d.localFamily_normalizerImage_not_G2 hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf hn
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- The original marker selects the same component, prime, row and Z₁ and
supplies the constrained higher-field G₂ exclusion on its literal FF image.
Original 15.1.14 remains explicit for the pre-exclusion assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_no_higher_G2
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
      (generalizedFitting d.L = pCore 2 d.L → ∀ n : ℕ, 1 < n →
        ¬ IsG2At (d.normalizerImage d.L) (2^n)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf _ hn =>
    s.constrained_normalizerImage_not_G2 (h := h) hG hempty hM hJ hu hf hn⟩
end CFSG.Quasithin.Chapter15.Section01
