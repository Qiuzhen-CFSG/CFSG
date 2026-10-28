module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherG2Local
-- Reuse only the intrinsic preimage-residual generation lemma.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.HigherG2

/-! Higher-field G2 is excluded on the literal original normalizer image.
The native two parabolic residuals belong to the same raw local family,
have nonshort PSL2 core quotients, and generate the original component.
Their proved marked placement contradicts escape. The actual core marking
is obtained from its central cover, preserving the possible kernel. -/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.HigherFieldResiduals
variable {G : Type*} [Group G] [Finite G]

private theorem raw_higherG2_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (L ⧸ pCore 2 L) ≃* Model F) : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (L : Set G) := by
  let := h.elementary
  let : Fact (2 < Nat.card F) := ⟨hF⟩
  let J := L ⊔ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
  have hJG : J ≤ (centralizer (Z1 : Set G)) := sup_le hL.1 (show ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ (centralizer (Z1 : Set G)) from inf_le_right)
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJG)).mp (hsq.subgroup (J.subgroupOf (centralizer (Z1 : Set G))))
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
  exact (show ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ J from le_sup_right).trans
    ((normal_subgroupOf_iff_le_normalizer (show L ≤ J from le_sup_left)).mp hn)

private theorem raw_higherG2_residuals
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (e : (L ⧸ pCore 2 L) ≃* Model F) :
    ∃ K : Fin 2 → Subgroup G,
      (∀ i, K i ∈ Chapter1.LIn (centralizer (Z1 : Set G)) ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))) ∧
      (∀ i, generalizedFitting (K i) = pCore 2 (K i)) ∧
      (∀ i, ¬ChapterC.IsShort (K i)) ∧
      (∀ i, ClassicalGroup.IsPSL (K i ⧸ pCore 2 (K i)) 2 (Nat.card F)) ∧
      K 0 ⊔ K 1 = L := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect hL.2
  have hnL := raw_higherG2_normalizes hG T h hZ hZne hL (by omega) e
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
  have hQL : (Q : Subgroup L) = (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) ≤ L from inf_le_right)]
    exact hQ
  let α : ↥((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) →* MulAut (Model F) := (MulAut.congr e').toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hnL)))
  have heq (a : ↥((T : Subgroup G) ⊓ centralizer (Z1 : Set G))) (l : L) :
      q (L.normalizerMonoidHom (inclusion hnL a) l) = α a (q l) := by
    change e' (QuotientGroup.mk' _ _) = e' (quotientAut _ _ (e'.symm (e' _)))
    rw [e'.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hnSL : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer ((((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) : Set G) :=
    (le_inf ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)).le_normalizer hnL).trans inf_normalizer_le_normalizer_inf
  have hUi (a : ↥((T : Subgroup G) ⊓ centralizer (Z1 : Set G))) : unipotent.map (α a).toMonoidHom = unipotent := by
    have hh := EquivariantLift.map_invariant L q hnL α heq (D := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) hnSL a
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
  have hnB (i : Fin 2) : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (B i : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    obtain ⟨l,hl,rfl⟩ := hx
    let a₀ : ↥((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) := ⟨a,ha⟩
    refine ⟨L.normalizerMonoidHom (inclusion hnL a₀) l,?_,rfl⟩
    change q (L.normalizerMonoidHom (inclusion hnL a₀) l) ∈ parabolicAt i
    rw [heq]
    exact parabolicAt_invariant (α a₀) (hUi a₀) i ▸ mem_map_of_mem (α a₀).toMonoidHom hl
  have hnK (i : Fin 2) : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (K i : Set G) :=
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
  have hfamily (i : Fin 2) : K i ∈ Chapter1.LIn (centralizer (Z1 : Set G)) ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) := by
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
  refine ⟨K,hfamily,hfit,?_,?_,?_⟩
  · intro i hs
    exact htriple i (commutator_eq_bot_iff_le_centralizer.mpr hs.central)
  · intro i
    exact ⟨F,inferInstance,inferInstance,rfl,⟨eq i⟩⟩
  · have hm := congrArg (Subgroup.map L.subtype)
      (CaseIComponentData.g2_preimage_residuals_generate q hsur (by omega) hk)
    rw [Subgroup.map_sup,map_embedded_solvableResidual_of_hom,
      map_embedded_solvableResidual_of_hom,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm

/-- Both literal native residuals force a higher-field G2 core quotient
into the original marked local. -/
theorem PreparedChosenModule.raw_higherG2_core_le_marked
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (K ⧸ pCore 2 K) ≃* Model F) : K ≤ (centralizer (Z1 : Set G) ⊓ Mc) := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  obtain ⟨A,hfamily,hfit,hshort,hquot,hgen⟩ := raw_higherG2_residuals hG T h hZ hZne hK hfour e
  have hi (i : Fin 2) : A i ≤ (centralizer (Z1 : Set G) ⊓ Mc) :=
    h.raw_nonshort_pslTwo_le_marked hG T hempty hM hJ hu hZ hZne
      (hfamily i) (hfit i) (hshort i) n hn (hF ▸ hquot i)
  rw [←hgen]
  exact sup_le (hi 0) (hi 1)

/-- The actual seed-normalizer image has no higher-field G2 model. The
central comparison is made faithful through the native universal cover. -/
theorem PreparedChosenModule.raw_component_normalizer_not_higherG2
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hout : ¬K ≤ (centralizer (Z1 : Set G) ⊓ Mc)) :
    let S := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
    let H := K ⊔ (S ⊓ normalizer (K : Set G))
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let I := (K.subgroupOf H).map (QuotientGroup.mk' (centralizer (W : Set H)))
    ∀ {n : ℕ}, 1 < n → ¬IsG2At I (2^n) := by
  dsimp only
  intro n hn
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let S := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
  have houtM : ¬K ≤ M := by
    intro hKM
    let : Group.IsPerfect (K.subgroupOf (K ⊔ S)) := hK.2.1.perfect
    let i : K.subgroupOf (K ⊔ S) ≃* K := subgroupOfEquivOfLe le_sup_left
    let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
    exact hout (le_inf hK.1
      ((perfect_subgroup_centralizes_localModule hG T hempty hM hKM).trans
        (localModule_centralizer_le_partner T M hu)))
  obtain ⟨_,f,_,_,_,hfs,_,_⟩ :=
    h.raw_component_normalizer_quotient hG T hM hJ hu hZ hZne hK hq hf hout houtM
  let := hq
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  let : Fact (2 < Nat.card F) := ⟨by omega⟩
  let c : Covering (K ⧸ pCore 2 K) (Model F) :=
    ⟨e.toMonoidHom.comp f,e.surjective.comp hfs⟩
  have hi : Function.Injective c.toMonoidHom :=
    (FiniteCover.cover_isUniversal F).injective_of_pGroup_kernel
      (FiniteCover.universalKernel_isPGroup_of_card_pow hF hn) c
      (pCore_quotient_pCore_eq_bot 2)
  let ec := MulEquiv.ofBijective c.toMonoidHom ⟨hi,c.surjective⟩
  exact hout (h.raw_higherG2_core_le_marked hG T hempty hM hJ hu hZ hZne hK hF hn ec)

end CFSG.Quasithin.Chapter15.Section01
