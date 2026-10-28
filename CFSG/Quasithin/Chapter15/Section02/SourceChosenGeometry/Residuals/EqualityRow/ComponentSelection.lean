module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EscapingReductions
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.ComponentSelectionPreparation
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualCommonPlane
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.SourceAction

/-!
# The original Omega intersection and its normalized component

For the actual residual input and offender plane, the intersection residual
has nonnormal image in the original action of M on V whenever NI = M ∩ I
escapes MI = Mc ∩ I. The earlier restricted actions then force genuine
Omega. The plane's actual inverter lies in NI's action image, so its
nonnormal residual supplies the faithful S₃ quotient with the literal
V-centralizer kernel and index six.

That action kills the original intersection two-core and gives the C.2.3
input. Component extraction and C.2.4 yield the same escaping component
normalized by both K and O₂(NI). Neither an extra action marking nor the
partner's prime-to-three residual identity is required. The only independent
classification premise left in the final selection is the no-chi result.

Source: Aschbacher--Smith, 15.2.18(3), 15.2.19(2), and the component-selection
paragraph of 15.2.23, printed pp.1113 and 1116, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions
open PlaneUniquenessPreceding.OmegaAction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

namespace ResidualInput
variable (r : ResidualInput hsource H B)
include r

/-- The actual S is Sylow in NI as well as I. -/
theorem planeSylow_in_intersection (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    Chapter1.IsSylowIn 2 (planeCentralizer T ⁅V,B⁆) (M ⊓ I) :=
  Chapter1.IsSylowIn.restrict (r.sylow_in_escape hI)
    (le_inf (inf_le_left.trans hsource.maximal.1.2)
      ((le_sup_right.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right))
    inf_le_right

/-- The residual and the literal plane Sylow generate the original NI. -/
theorem intersection_residual_sup_planeSylow (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    (pResidual 2 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype ⊔ planeCentralizer T ⁅V,B⁆ = M ⊓ I := by
  obtain ⟨P,hP⟩ := r.planeSylow_in_intersection hI
  have hh := congrArg (Subgroup.map (M ⊓ I).subtype) (pResidual_sup_sylow_eq_top P)
  rwa [Subgroup.map_sup,hP,←MonoidHom.range_eq_map,range_subtype] at hh

/-- The first source alternative is exactly centralization by O²(NI). -/
theorem intersection_le_partner_iff_residual_centralizes (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    M ⊓ I ≤ Mc ⊓ I ↔
      (pResidual 2 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype ≤ centralizer (V : Set G) := by
  constructor
  · intro hn
    exact (embedded_pResidual_mono 2 (le_inf inf_le_left (hn.trans inf_le_left))).trans
      (r.partner_intersection_residual_le_module_centralizer.trans inf_le_right)
  · intro hx
    rw [←r.intersection_residual_sup_planeSylow hI]
    exact sup_le
      (le_inf (hx.trans ((centralizer_le r.plane_le).trans
        (r.plane_centralizer_le_intersection hI) |>.trans inf_le_left))
        ((map_subtype_le _).trans inf_le_right))
      (le_sup_right.trans (r.residual_sup_planeCentralizer_le hI))

/-- The source obstruction rules out normality in the whole M-action. -/
theorem residualImage_not_normal (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I) : ¬ (residualImage hsource I).Normal := by
  intro hn
  let hc := hn.comap (action hsource)
  have hMn : M ≤ normalizer
      ((((residualImage hsource I).comap (action hsource)).map M.subtype : Subgroup G) : Set G) := by
    intro m hm
    exact ((residualImage hsource I).comap (action hsource)).le_normalizer_map M.subtype
      (mem_map_of_mem M.subtype (show (⟨m,hm⟩ : M) ∈
        normalizer (((residualImage hsource I).comap (action hsource) : Subgroup M) : Set M) from
          by rw [normalizer_eq_top]; exact mem_top _))
  rw [residualImage_preimage] at hMn
  exact r.residual_join_centralizer_not_normalized hI
    (fun hx => hout ((r.intersection_le_partner_iff_residual_centralizes hI).mpr hx))
    (hsource.maximal.1.2.trans hMn)

/-- The cyclic-residual alternatives of 15.2.13 cannot escape MI. -/
theorem intersection_le_partner_of_cyclic_residual (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    [IsCyclic (pResidual 2 (internalActionImage M V hsource.prepared.normalized))] :
    M ⊓ I ≤ Mc ⊓ I := by
  by_contra hout
  apply residualImage_not_normal r hI hout
  apply normalizer_eq_top_iff.mp
  apply top_unique
  exact (le_normalizer_of_normal (H := pResidual 2
    (internalActionImage M V hsource.prepared.normalized))).trans
      (normalizer_le_normalizer_of_le_cyclic _ _
        (map_pResidual_le 2 (intersectionImage hsource I).subtype))

omit r in
private theorem cyclic_twoResidual_of_card_twenty {D : Type*} [Group D] [Finite D]
    (hc : Nat.card D = 20) : IsCyclic (pResidual 2 D) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 D := Classical.choice inferInstance
  let : Subsingleton (Sylow 5 D) := Sylow.subsingleton_five_of_card_twenty hc
  let : (P : Subgroup D).Normal := P.normal_of_subsingleton
  have hP : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity,hc]
    decide +kernel
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hquot : IsPGroup 2 (D ⧸ (P : Subgroup D)) := by
    apply IsPGroup.of_card (n := 2)
    have hm := (P : Subgroup D).card_mul_index
    rw [hP,hc,index_eq_card] at hm
    norm_num at hm ⊢
    omega
  have hle : pResidual 2 D ≤ P := sInf_le ⟨inferInstance,hquot⟩
  exact isCyclic_of_injective (inclusion hle) (inclusion_injective hle)

/-- The marked involution belongs to the image of the original plane Sylow. -/
theorem inverter_mem_planeCentralizer_image (b : PlaneInverter hsource ⁅V,B⁆) :
    b.involution ∈ ((planeCentralizer T ⁅V,B⁆).subgroupOf M).map (action hsource) := by
  obtain ⟨t,ht,he⟩ := b.in_sylow
  refine ⟨t,⟨ht,?_⟩,he⟩
  intro z hz
  have hh : (action hsource t).val (⟨z,r.plane_le hz⟩ : V) =
      ⟨z,r.plane_le hz⟩ := by
    rw [he]
    exact (b.fixed_plane _).mp hz
  have hc := congrArg Subtype.val hh
  change (t : G) * z * (t : G)⁻¹ = z at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

/-- The escape is in the original restricted-action row of 15.2.14(2b). -/
theorem escape_restricted_actions (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    letI := hsource.prepared.elementary
    Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) := by
  let := hsource.prepared.elementary
  rcases r.source_plane_alternatives with he | hi
  · have hi := (r.escape_index hI).2
    rw [he.1,relIndex_self] at hi
    contradiction
  · exact hi.1

/-- Genuine Omega is forced on the original M-action when NI escapes MI. -/
theorem omega_of_escape_not_le_partner (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) := by
  let := hsource.prepared.elementary
  rcases r.escape_restricted_actions hI with he | ho
  · obtain ⟨e⟩ := he
    let := cyclic_twoResidual_of_card_twenty
      ((Nat.card_congr e.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card)
    exact (hout (r.intersection_le_partner_of_cyclic_residual hI)).elim
  · exact ho

/-- The actual intersection image is S₃, using its nonnormal residual and
its original distinguished involution. No point marking is assumed. -/
theorem intersection_image_equiv_of_omega (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ho : letI := hsource.prepared.elementary;
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (b : PlaneInverter hsource ⁅V,B⁆) :
    Nonempty (intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) := by
  let := hsource.prepared.elementary
  obtain ⟨e⟩ := ho.2.2.2.1
  let N := intersectionImage hsource I
  let N' := N.map e.toMonoidHom
  have hn : ¬ ((pResidual 2 N').map N'.subtype).Normal := by
    rw [←map_embedded_pResidual]
    intro hn
    exact residualImage_not_normal r hI hout ((MulEquiv.normal_map_iff (f := e)).mp hn)
  have hSN : planeCentralizer T ⁅V,B⁆ ≤ M ⊓ I := le_inf
    (inf_le_left.trans hsource.maximal.1.2)
    ((le_sup_right.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right)
  have hbN : b.involution ∈ N :=
    (map_mono (comap_mono hSN)) (inverter_mem_planeCentralizer_image r b)
  let b' : N' := ⟨e b.involution,mem_map_of_mem e.toMonoidHom hbN⟩
  have hb' : orderOf b' = 2 := (Subgroup.orderOf_coe b').symm.trans
    ((orderOf_injective e.toMonoidHom e.injective b.involution).trans b.order_two)
  obtain ⟨j⟩ := SymmetricThreeProductResidual.equiv_symmetricThree_of_nonnormal_residual
    N' hn b' hb'
  exact ⟨(e.subgroupMap N).trans j⟩

/-- NI contains the full M-action kernel, so its index is the image index. -/
theorem intersection_index_eq_image (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    (M ⊓ I).relIndex M = (intersectionImage hsource I).index := by
  have hk : (action hsource).ker ≤ (M ⊓ I).subgroupOf M := by
    rw [action_ker]
    intro x hx
    exact ⟨x.property,r.module_centralizer_le_escape hI hx⟩
  exact (index_map_eq ((M ⊓ I).subgroupOf M)
    (actionHom M V hsource.prepared.normalized).rangeRestrict_surjective hk).symm

/-- Index six is computed from the genuine Omega and S₃ image orders. -/
theorem intersection_index_six_of_image_equiv (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (ho : letI := hsource.prepared.elementary;
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (e : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    (M ⊓ I).relIndex M = 6 := by
  let := hsource.prepared.elementary
  obtain ⟨x,a,hx⟩ := ho.2.2.2.2
  have hD : Nat.card (internalActionImage M V hsource.prepared.normalized) = 36 :=
    (Nat.card_congr a.toEquiv).trans OrthogonalFourBinary.SylowGeometry.omega_card
  have hN : Nat.card (intersectionImage hsource I) = 6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hh := (intersectionImage hsource I).card_mul_index
  rw [hN,hD] at hh
  rw [intersection_index_eq_image r hI]
  omega

/-- The actual NI action has the original centralizer kernel, index six and
its source pushing-up setup. Every action premise is derived from r. -/
theorem intersection_source_action (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I) :
    (M ⊓ I).relIndex M = 6 ∧
      ∃ f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3), Function.Surjective f ∧
        f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I) ∧
        PushingUpSetup KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) := by
  have ho := r.omega_of_escape_not_le_partner hI hout
  obtain ⟨b⟩ := r.exists_planeInverter
  obtain ⟨e⟩ := r.intersection_image_equiv_of_omega hI hout ho b
  obtain ⟨f,hf,hker⟩ := exists_symmetricThree_action_of_image_equiv e
  have hcore := r.intersection_core_eq_of_centralizes hI
    (PlaneUniquenessPreceding.intersection_core_centralizes_of_symmetricThree f hf hker)
  exact ⟨r.intersection_index_six_of_image_equiv hI ho e,f,hf,hker,
    PlaneUniquenessPreceding.intersection_pushingUpSetup (hsource := hsource) hI hcore⟩

/-- Source 15.2.19(2) on the actual NI, without an assumed action quotient. -/
theorem intersection_core_eq_of_not_le_partner (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I) :
    (M ⊓ I).pCoreIn 2 = M.pCoreIn 2 := by
  obtain ⟨_,f,hf,hker,_⟩ := r.intersection_source_action hI hout
  exact r.intersection_core_eq_of_centralizes hI
    (PlaneUniquenessPreceding.intersection_core_centralizes_of_symmetricThree f hf hker)

/-- The component-selection paragraph of 15.2.23 on the original residual
input. The independent no-chi premise is the only earlier block exclusion. -/
theorem escaping_normalized_component_of_not_le_partner
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I) :
    ∃ X : Subgroup G, ComponentCatalogue.Normalized H M I X :=
  r.escaping_normalized_component_of_core hI hfit
    (r.intersection_core_eq_of_not_le_partner hI hout) hno

end ResidualInput
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
