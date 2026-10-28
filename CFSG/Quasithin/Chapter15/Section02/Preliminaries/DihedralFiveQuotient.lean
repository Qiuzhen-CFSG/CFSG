module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveSylow
public import Theory.GroupTheory.SylowSmallIndexModels
/-!
# The actual order-five residual join has the required rank-one quotient

The original Rc is Sylow in YRc, and [Y:O₂(Y)]=5 gives [YRc:Rc]=5.
It cannot be normal: its actual two-group image moves the marked prime
residual, whereas mutual normality would force their coprime images to
commute. The proved Sylow index-five recognition therefore identifies
YRc/O₂(YRc) with D₁₀ or the concrete Suzuki matrix group Sz(2).

This is the L₀ quotient premise for both mixed-amalgam invocations in
original15.2.4. It uses the literal chosen module and intersection core;
no arbitrary model label or full actor classification is assumed.
Source: Aschbacher--Smith15.2.4, printed p.1106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem index_sup_normal (K R : Subgroup G) [K.Normal] :
    R.relIndex (K ⊔ R) = R.relIndex K := by
  have hm : K.relIndex R * R.relIndex (K ⊔ R) = K.relIndex R * R.relIndex K := by
    calc
      K.relIndex R * R.relIndex (K ⊔ R) = (R ⊓ K).relIndex (K ⊔ R) := by
        rw [←inf_relIndex_left (H := R) (K := K)]
        exact relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
      _ = (R ⊓ K).relIndex K * K.relIndex (K ⊔ R) :=
        (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
      _ = K.relIndex R * R.relIndex K := by simp [inf_relIndex_right,Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero
    (index_ne_zero_of_finite : K.relIndex R ≠ 0)) hm

private theorem index_join_of_normalizes (K R : Subgroup G)
    (hn : R ≤ normalizer (K : Set G)) : R.relIndex (K ⊔ R) = R.relIndex K := by
  let L := K ⊔ R
  let KL := K.subgroupOf L
  let RL := R.subgroupOf L
  let : KL.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  have hsup : KL ⊔ RL = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ L from le_sup_left) (show R ≤ L from le_sup_right)]
    exact subgroupOf_self L
  have hh := index_sup_normal KL RL
  rw [hsup,relIndex_top_right] at hh
  exact hh.trans (relIndex_subgroupOf (show K ≤ L from le_sup_left))

omit [Finite G] in
private theorem image_movement_not_normalizes {D : Type*} [Group D] [Finite D]
    (f : G →* D) (K R : Subgroup G) [(K.map f).Normal]
    (hK : Nat.card (K.map f) = 5) (hR : IsPGroup 2 R)
    (hmove : ¬ R.map f ≤ centralizer (K.map f : Set D)) :
    ¬ K ≤ normalizer (R : Set G) := by
  intro hn
  have him : K.map f ≤ normalizer (R.map f : Set D) :=
    (map_mono hn).trans (R.le_normalizer_map f)
  have hdis : Disjoint (K.map f) (R.map f) :=
    IsPGroup.disjoint_of_coprime (IsPGroup.of_card (n := 1) (by simpa using hK))
      (hR.map f) (by decide : Nat.Coprime 5 2)
  have hc : ⁅K.map f,R.map f⁆ = ⊥ := bot_unique
    ((le_inf (commutator_le_left _ _) (le_normalizer_iff_commutator_le_right.mp him)).trans hdis.le_bot)
  exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))

private theorem residual_notation (K : Subgroup G) :
    twoResidualAmbient K = (pResidual 2 K).map K.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN,n,hn⟩
    exact ⟨hN,IsPGroup.of_card hn⟩
  · rintro ⟨hN,hn⟩
    exact ⟨hN,IsPGroup.iff_card.mp hn⟩

section ChosenFive
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype)) {m : ℕ}
    (hp : PrimeDimensionOptions 5 m) (hd : DihedralMarking l 5 m)
include hG hempty hM hJ hu hmany hp hd

/-- The original YRc quotient is D₁₀ or the actual Sz(2) model. -/
theorem source_dihedral_five_join_quotient :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let L := Y ⊔ (M ⊓ Mc).pCoreIn 2
    Nonempty ((L ⧸ pCore 2 L) ≃* DihedralGroup 5) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let R := (M ⊓ Mc).pCoreIn 2
  let L := Y ⊔ R
  have hRn : R ≤ normalizer (Y : Set G) := by
    let A := twoResidualAmbient (chosenStarredPreimage M V hV.normalized) ⊔ (T : Subgroup G)
    let K := conjugateSpanBy R A
    have hYR : Y = (pResidual 2 K).map K.subtype := residual_notation K
    rw [hYR]
    exact (le_conjugateSpanBy R A).trans (K.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K (pResidual 2 K)))
  obtain ⟨hi,hcore⟩ := source_dihedral_five_residual_core_index hG T hempty hM hJ hu hmany hV l hp hd
  have hcoreR : Y.pCoreIn 2 ≤ R :=
    hcore.trans ((hV.intersection_core_centralizer T hM.1.2 hu).symm.le.trans inf_le_left)
  let P : Sylow 2 Y := pCore_isPGroup.toSylow (by rw [hi]; decide)
  have hRcore : R.subgroupOf Y = pCore 2 Y := by
    exact P.is_maximal' (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype
      (fun y hy => hcoreR (mem_map_of_mem Y.subtype hy))
  obtain ⟨S,hS⟩ := source_dihedral_five_intersection_core_sylow hG T hempty hM hJ hu hmany hV l hp hd
  have hSR : (S : Subgroup L) = R.subgroupOf L := by
    have hh := congrArg (comap L.subtype) hS
    rwa [comap_map_eq_self_of_injective L.subtype_injective] at hh
  have hindex : S.index = 5 := by
    rw [hSR]
    change R.relIndex L = 5
    rw [index_join_of_normalizes Y R hRn]
    change (R.subgroupOf Y).index = 5
    rwa [hRcore]
  apply sylow_index_five_core_quotient S hindex
  refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S) ?_
  intro he
  have hnormal : (R.subgroupOf L).Normal := by rw [←hSR,←he]; infer_instance
  have hYR : Y ≤ normalizer (R : Set G) := le_sup_left.trans
    ((normal_subgroupOf_iff_le_normalizer (show R ≤ L from le_sup_right)).mp hnormal)
  let ρ := imageRepresentation M V hV.normalized
  let f : M →* internalActionImage M V hV.normalized := (actionHom M V hV.normalized).rangeRestrict
  let RB := (R.subgroupOf M).map f
  have hRne : RB ≠ ⊥ := by
    intro hb
    have hk := (Subgroup.map_eq_bot_iff _).mp hb
    apply source_chosen_core_noncentral hG T hempty hM hJ hu hmany hV
    intro r hr
    let x : M := ⟨r,((pCoreIn_le 2 (M ⊓ Mc)).trans inf_le_left) hr⟩
    have hx : x ∈ (actionHom M V hV.normalized).ker := congrArg Subtype.val (hk hr)
    rwa [actionHom_ker] at hx
  have hRtwo : IsPGroup 2 RB := (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype.map f
  have hmove := dihedral_prime_moves_twoGroup ρ (imageRepresentation_injective _ _ _)
    hV.quadratic_ratio l hp hd RB hRtwo hRne
  have him := source_dihedral_caseIIResidual_image hG T hempty hM hJ hu hmany hV l hp hd
  change (Y.subgroupOf M).map f = l.kernel.map (Jhat ρ).subtype at him
  let : (Jhat ρ).Normal := Jhat_normal ρ
  obtain ⟨_,_,hc,hn,_,_,_,_,_,_⟩ := hd.ambient_marks (Jhat ρ) hp
  let : ((Y.subgroupOf M).map f).Normal := him.symm ▸ hn
  have hfive : Nat.card ((Y.subgroupOf M).map f) = 5 := him ▸ hc
  have hn := image_movement_not_normalizes f (Y.subgroupOf M) (R.subgroupOf M) hfive
    (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype (by rwa [him])
  exact hn ((comap_mono hYR).trans (R.le_normalizer_comap M.subtype))
end ChosenFive
end CFSG.Quasithin.Chapter15.Section02
