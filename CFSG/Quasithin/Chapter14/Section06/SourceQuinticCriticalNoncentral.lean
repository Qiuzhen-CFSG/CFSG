module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCriticalPlacement
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCenterLayerAction
public import Theory.GroupTheory.PGroup.IndexTwoCentralOmegaBound
public import Theory.Representation.BinaryOffender.FiveInvolutionMoved.SmallModels
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.Representation.ElementaryAbelianAction
public import Theory.ElementaryAbelian.Quotient
import all CFSG.Quasithin.Chapter14.Section06.SourceQuinticHyperplanes

/-!
# The actual small-quintic critical intersection is noncentral

The whole original Sylow has a central omega line and its cubic core has
index two.  Thus a central critical intersection has order at most four,
and equals the marked plane.  Its commutator image on UH/ZT would then
have order at most two, contradicting faithful involution movement in
the actual D10 or Sz(2) quotient.

The intentional internal import reuses only the frozen generic elementary
image bound for the two small quintic quotients.  No F.9 path or parameter
is substituted for the actual DGS critical path.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem small_center_layer_contradiction
    (H U D V Z : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 D]
    [(Z.subgroupOf U).Normal]
    (hHU : H ≤ normalizer (U : Set G)) (hDH : D ≤ H)
    (hDne : ¬ D ≤ H.pCoreIn 2) (hZV : Z ≤ V) (hVU : V ≤ U)
    (hV : Nat.card V = 4) (hZ : Nat.card Z = 2)
    (hm : Nonempty ((H ⧸ pCore 2 H) ≃* DihedralGroup 5) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    (α : H →* MulAut (U ⧸ Z.subgroupOf U)) (hker : α.ker = pCore 2 H)
    (hα : ∀ h : H, ∀ u : U, α h (QuotientGroup.mk' (Z.subgroupOf U) u) =
      QuotientGroup.mk' (Z.subgroupOf U) ⟨(h : G)*u*(h : G)⁻¹,
        (mem_normalizer_iff.mp (hHU h.property) u).mp u.property⟩)
    (hcomm : ⁅U,D⁆ ≤ V) : False := by
  let W := U ⧸ Z.subgroupOf U
  let π := QuotientGroup.mk' (Z.subgroupOf U)
  let q := QuotientGroup.mk' (pCore 2 H)
  let β := QuotientGroup.lift (pCore 2 H) α hker.ge
  have hβ : Function.Injective β :=
    (QuotientGroup.injective_lift_iff _ α hker.ge).mpr hker.symm
  let : MulDistribMulAction (H ⧸ pCore 2 H) W := MulDistribMulAction.compHom _ β
  let ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive W) :=
    Representation.ofElementaryAbelianAction
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply hβ
    ext w
    exact congrArg Additive.toMul (DFunLike.congr_fun hab (Additive.ofMul w))
  let f : D →* (H ⧸ pCore 2 H) := q.comp (inclusion hDH)
  let E := f.range
  have hEmap : E = (D.subgroupOf H).map q := by
    ext w
    constructor
    · rintro ⟨d,rfl⟩
      exact mem_map_of_mem q d.property
    · rintro ⟨d,hd,rfl⟩
      exact ⟨⟨d,hd⟩,rfl⟩
  let : IsElementaryAbelian 2 (D.subgroupOf H) := IsElementaryAbelian.subgroupOf hDH
  let : IsElementaryAbelian 2 E := hEmap.symm ▸ IsElementaryAbelian.map q
  have hEne : E ≠ ⊥ := by
    intro he
    apply hDne
    intro d hd
    have hh : q ⟨d,hDH hd⟩ ∈ E := ⟨⟨d,hd⟩,rfl⟩
    rw [he,mem_bot] at hh
    have hp := (QuotientGroup.eq_one_iff (⟨d,hDH hd⟩ : H)).mp hh
    exact mem_map_of_mem H.subtype hp
  have hE : Nat.card E = 2 := by
    have hu := quintic_elementary_bound hm E
    have hp := Nat.card_pos (α := E)
    have hn : Nat.card E ≠ 1 := fun hh => hEne (card_eq_one.mp hh)
    omega
  have hbig : 4 ≤ Nat.card (subspaceCommutator ρ ⊤ E) := by
    rcases hm with hd | hs
    · exact dihedral_five_four_le_card_subspaceCommutator ρ hd.some hρ E hE
    · exact suzuki_zero_four_le_card_subspaceCommutator ρ hs.some hρ E hE
  have hDU : D ≤ normalizer (U : Set G) := hDH.trans hHU
  have hact (d : D) (u : U) : ρ (f d) (Additive.ofMul (π u)) =
      Additive.ofMul (π ⟨(d : G)*u*(d : G)⁻¹,
        le_normalizer_iff.mp hDU d d.property u u.property⟩) := by
    exact congrArg Additive.ofMul (hα (inclusion hDH d) u)
  have hP : binarySubgroup (⊤ : Submodule (ZMod 2) (Additive W)) =
      (U.subgroupOf U).map π := by
    change (⊤ : Subgroup W) = (U.subgroupOf U).map π
    symm
    apply top_unique
    intro w _
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
    exact mem_map_of_mem π u.property
  have himage := commutator_image_eq ρ U U D hDU le_rfl f π hact ⊤ hP
  let C := (V.subgroupOf U).map π
  have hC : Nat.card C = 2 := by
    change Nat.card ((V.subgroupOf U).map π) = 2
    rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hVU]
    have hh := (Z.subgroupOf V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv] at hh
    change Nat.card Z * Z.relIndex V = Nat.card V at hh
    rw [hZ,hV] at hh
    omega
  have hsmall : Nat.card (subspaceCommutator ρ ⊤ E) ≤ 2 := by
    rw [←binarySubgroup_card,himage.symm]
    exact (card_le_of_le (map_mono (subgroupOf_mono U hcomm))).trans_eq hC
  omega

/-- The actual reciprocal critical intersection fails to centralize the
full original cubic core, in both small quintic quotient branches. -/
theorem source_quintic_critical_intersection_noncentral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let UH := conjugateSpanBy (localModule T M) H
    ∃ g ∈ X,
      let Ustar := UH.map (MulAut.conj g).toMonoidHom
      Ustar ≤ X.pCoreIn 2 ∧ ¬ Ustar ≤ H.pCoreIn 2 ∧
        localModule T M ≤ UH ⊓ Ustar ∧
        (T : Subgroup G) ≤ normalizer (UH ⊓ Ustar : Set G) ∧
        ¬ UH ⊓ Ustar ≤ centralizer (X.pCoreIn 2 : Set G) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  obtain ⟨g,hg,hDQ,hDne,hVI,hTI⟩ :=
    source_quintic_critical_span_placement hG T hempty hM hu hmany hcard e H hH hi
  let D := U.map (MulAut.conj g).toMonoidHom
  let I := U ⊓ D
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)]
      using pCoreIn_le_sylow X (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right))
  let : IsElementaryAbelian 2 U := (Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi).1
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.of_injective
    (inclusion (show I ≤ U from inf_le_left)) (inclusion_injective _)
  refine ⟨g,hg,hDQ,hDne,hVI,hTI,?_⟩
  intro hcentral
  have hiQ : (X.pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
    obtain ⟨_,⟨eX⟩⟩ := Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e
    have hTX : (T : Subgroup G) ≤ X := le_sup_right
    let S := T.subtype hTX
    have hm := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal S)
    rw [SymmetricThreeTwoCore.sylow_index_three eX S,SymmetricThreeTwoCore.core_index eX] at hm
    have hi' : (pCore 2 X).relIndex (S : Subgroup X) = 2 := by omega
    have hmap : (S : Subgroup X).map X.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le hTX
    rw [←hmap,pCoreIn,relIndex_map_map_of_injective _ _ X.subtype_injective]
    exact hi'
  have hIcard : Nat.card I ≤ 4 := elementary_card_le_four_of_relIndex_two_omegaCenterIn
    (T : Subgroup G) (X.pCoreIn 2) I (inf_le_right.trans (hDQ.trans hQT)) hTI hcentral hiQ
      (plane_centralInvolutions_card T M hM.1.2 hcard e)
  have hI : I = localModule T M :=
    (eq_of_le_of_card_ge hVI (hIcard.trans_eq hcard.symm)).symm
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hQH : X.pCoreIn 2 ≤ H := hQT.trans hH.1.1.2
  have hQN : X ≤ normalizer (X.pCoreIn 2 : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hQD : X.pCoreIn 2 ≤ normalizer (D : Set G) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) (hQH.trans hHU)
    have hmap : (X.pCoreIn 2).map (MulAut.conj g).toMonoidHom = X.pCoreIn 2 :=
      mem_normalizer_iff_map_conj_eq.mp (hQN hg)
    rw [hmap] at hh
    exact hh.trans (U.le_normalizer_map (MulAut.conj g).toMonoidHom)
  have hUQ : U ≤ X.pCoreIn 2 := by
    intro u hu'
    exact (mem_normalizer_iff.mp (hQN hg) u).mpr
      (hDQ (mem_map_of_mem (MulAut.conj g).toMonoidHom hu'))
  have hcomm : ⁅U,D⁆ ≤ localModule T M := by
    rw [←hI]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp ((hDQ.trans hQH).trans hHU))
      (le_normalizer_iff_commutator_le_right.mp (hUQ.trans hQD))
  obtain ⟨hN,α,hker,_,hα⟩ :=
    source_quintic_faithful_center_layer_action hG T hempty hM hu hmany hcard e H hH hi
  let := hN
  exact small_center_layer_contradiction H U D (localModule T M) (centralInvolutions T)
    hHU (hDQ.trans hQH) hDne (le_conjugateSpanBy _ _) (le_conjugateSpanBy _ _) hcard
    (plane_centralInvolutions_card T M hM.1.2 hcard e)
    (Section02.SolvableAmalgam.source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi)
    α hker hα hcomm

end CFSG.Quasithin.Chapter14.Section06
