module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherG2Local

/-! The original ordinary component has no higher-field G2 core quotient.
Cubic rank makes the actual component normal in the original centralizer.
Both native parabolic residuals, on one Sylow-compatible marking, belong to
the same local family and have nonshort PSL2 cores. Their proved marked
placement and native generation contradict escape. The central two-cover
is retained throughout; no component-data record or generation premise is used. -/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.HigherFieldResiduals
variable {G : Type*} [Group G] [Finite G]

private theorem raw_ordinary_higherG2_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G))
      (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Model F) :
    (L.subgroupOf (centralizer (Z1 : Set G))).Normal := by
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple (centralizer (Z1 : Set G)) := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  let ec : L.subgroupOf (centralizer (Z1 : Set G)) ≃* L := subgroupOfEquivOfLe hLG
  have hR : 2 ≤ primeRank 3 (L.subgroupOf (centralizer (Z1 : Set G))) := by
    rw [primeRank_equiv 3 ec]
    have hr : 2 ≤ primeRank 3 (L ⧸ pCore 2 L) := by
      rw [primeRank_equiv 3 e]
      exact EvenThreeRank.two_le_primeRank
    exact hr.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
  have hZtwo : IsPGroup 2 (center L) := by
    rw [hcenter]
    exact pCore_isPGroup
  have hZ := hZtwo.of_equiv (centerCongr ec.symm)
  obtain ⟨k,hk⟩ := hZ.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card (center (L.subgroupOf (centralizer (Z1 : Set G))))) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  exact hL.normal_of_coprime_center_primeRank 3 hc (by
    have hh := hsq.stronglyQuasithin 3 Nat.prime_three (by decide)
    omega)

private theorem raw_ordinary_higherG2_residuals
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G))
      (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (e : (L ⧸ pCore 2 L) ≃* Model F) :
    ∃ K : Fin 2 → Subgroup G,
      (∀ i, K i ∈ Chapter1.LIn (centralizer (Z1 : Set G))
        ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))) ∧
      (∀ i, generalizedFitting (K i) = pCore 2 (K i)) ∧
      (∀ i, ¬ChapterC.IsShort (K i)) ∧
      (∀ i, ClassicalGroup.IsPSL (K i ⧸ pCore 2 (K i)) 2 (Nat.card F)) ∧
      K 0 ⊔ K 1 = L := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe hLG)
  have hnL : S ≤ normalizer (L : Set G) := (show S ≤ centralizer (Z1 : Set G) from inf_le_right).trans
    ((normal_subgroupOf_iff_le_normalizer hLG).mp
      (raw_ordinary_higherG2_normal hG T h hZ hZne hLG hL hcenter e))
  obtain ⟨Q,hQ⟩ := hSylL
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
  have hc : q.ker ≤ center L := by rw [hker,←hcenter]
  have hU : (Q : Subgroup L).map q = unipotent := by
    have hh := congrArg (fun U : Sylow 2 (Model F) => (U : Subgroup (Model F))) hg
    change ((Q : Subgroup L).map q₀).map (MulAut.conj g).toMonoidHom = unipotent at hh
    rw [map_map] at hh
    exact hh
  have hQL : (Q : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show (S ⊓ L) ≤ L from inf_le_right)]
    exact hQ
  let α : S →* MulAut (Model F) := (MulAut.congr e').toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hnL)))
  have heq (a : S) (l : L) :
      q (L.normalizerMonoidHom (inclusion hnL a) l) = α a (q l) := by
    change e' (QuotientGroup.mk' _ _) = e' (quotientAut _ _ (e'.symm (e' _)))
    rw [e'.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hnSL : S ≤ normalizer ((S ⊓ L) : Set G) :=
    (le_inf S.le_normalizer hnL).trans inf_normalizer_le_normalizer_inf
  have hUi (a : S) : unipotent.map (α a).toMonoidHom = unipotent := by
    have hh := EquivariantLift.map_invariant L q hnL α heq (D := S ⊓ L) hnSL a
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
  have hnB (i : Fin 2) : S ≤ normalizer (B i : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    obtain ⟨l,hl,rfl⟩ := hx
    let a₀ : S := ⟨a,ha⟩
    refine ⟨L.normalizerMonoidHom (inclusion hnL a₀) l,?_,rfl⟩
    change q (L.normalizerMonoidHom (inclusion hnL a₀) l) ∈ parabolicAt i
    rw [heq]
    exact parabolicAt_invariant (α a₀) (hUi a₀) i ▸ mem_map_of_mem (α a₀).toMonoidHom hl
  have hnK (i : Fin 2) : S ≤ normalizer (K i : Set G) :=
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
  have hfamily (i : Fin 2) : K i ∈ Chapter1.LIn (centralizer (Z1 : Set G)) S := by
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
    apply Chapter1.mem_LIn_of_normalized_perfect hSylG
      ((hKL i).trans hLG) (hnK i)
    intro hh
    have hb : pCore 2 (K i) = ⊥ := (map_eq_bot_iff_of_injective _ (K i).subtype_injective).mp hh
    exact htriple i (by rw [hb,commutator_bot_left,commutator_bot_left])
  refine ⟨K,hfamily,hfit,?_,?_,?_⟩
  · intro i hs
    exact htriple i (commutator_eq_bot_iff_le_centralizer.mpr hs.central)
  · intro i
    exact ⟨F,inferInstance,inferInstance,rfl,⟨eq i⟩⟩
  · have hm := congrArg (Subgroup.map L.subtype)
      (preimage_residuals_generate q hsur (by omega) hc)
    rw [Subgroup.map_sup,map_embedded_solvableResidual_of_hom,
      map_embedded_solvableResidual_of_hom,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm

/-- Both ordinary G2 alternatives are excluded on the same original component,
including its retained central two-cover. Only the original component, center,
Sylow and escape facts are used. -/
theorem PreparedChosenModule.raw_ordinary_not_higherG2
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G))
      (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (n : ℕ) (hn : 1 < n) :
    ¬(IsG2At L (2^n) ∨ IsG2At (L ⧸ pCore 2 L) (2^n)) := by
  intro hm
  have hm' : IsG2At (L ⧸ pCore 2 L) (2^n) := by
    rcases hm with hm | hm
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      have hq : 2 < Nat.card F := by
        rw [hF]
        exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
      let : IsSimpleGroup (Model F) := isSimple hq
      let : Group.IsPerfect (Model F) := isPerfect hq
      have hz : center (Model F) = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Model F)) inferInstance with he | he
        · exact he
        · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he)).elim
      have hcore : pCore 2 L = ⊥ := by
        rw [←hcenter]
        apply bot_unique
        intro x hx
        exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨x,hx⟩).property)
      exact ⟨F,inferInstance,inferInstance,hF,
        ⟨((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans e⟩⟩
    · exact hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm'
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  obtain ⟨K,hfamily,hfit,hshort,hquot,hgen⟩ :=
    raw_ordinary_higherG2_residuals hG T h hZ hZne hLG hL hcenter hSylG hSylL hfour e
  have hi (i : Fin 2) : K i ≤ centralizer (Z1 : Set G) ⊓ Mc :=
    h.raw_nonshort_pslTwo_le_marked hG T hempty hM hJ hu hZ hZne
      (hfamily i) (hfit i) (hshort i) n hn (hF ▸ hquot i)
  exact hout (hgen ▸ sup_le (hi 0) (hi 1))

end CFSG.Quasithin.Chapter15.Section01
