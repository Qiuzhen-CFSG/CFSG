module
public import Theory.SpecificGroups.OrthogonalFourBinary.OmegaPointStabilizer
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.Nonnormal
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.PlaneInput
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.Transport
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.RestrictedActions
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.FullSylow

/-!
# The faithful symmetric-three quotient of the actual Omega intersection

The residual-normalizer obstruction makes O²(NI) nonnormal in the original
M-action. In the genuine S₃ × S₃ image, its order is three and projection
onto either symmetric factor is faithful on NI's image. The distinguished
involution belongs to the image of S = C_T(ZS), hence to NI's image, making
that projection surjective. This constructs the faithful S₃ action with
kernel exactly C_NI(V), computes index six, and applies C.2.3 and C.2.4 to
select the original escaping component with both required normalizers.

Only the earlier restricted-action and PlaneInverter inputs remain from
15.2.13--14, produced by `qt-e-152-plane-geometry` and
`qt-e-152-small-parabolic`. The no-chi premise comes from
`qt-e-152-char2-block-exclusion`. Their final earlier-source discharge
belongs to `qt-e-152-plane-uniqueness`. The original natural-action marking
identifies NI's image with a nonsingular-point stabilizer and constructs
the complement Z1 with NI = C_M(Z1), on these same groups and maps.

Source: Aschbacher--Smith, 15.2.18(3ii), 15.2.19(2), printed p.1113,
and the component-selection paragraph of 15.2.23, printed p.1116.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.OmegaAction
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The actual intersection image is S₃, using its nonnormal residual and
its original distinguished involution. No point marking is assumed. -/
theorem intersection_image_equiv_of_omega (hI : PlaneEscapes Mc ZS I)
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ho : letI := hsource.prepared.elementary;
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (b : PlaneInverter hsource ZS) :
    Nonempty (intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) := by
  let := hsource.prepared.elementary
  obtain ⟨e⟩ := ho.2.2.2.1
  let N := intersectionImage hsource I
  let N' := N.map e.toMonoidHom
  have hn : ¬ ((pResidual 2 N').map N'.subtype).Normal := by
    rw [←map_embedded_pResidual]
    intro hn
    exact residualImage_not_normal d hI hout ((MulEquiv.normal_map_iff (f := e)).mp hn)
  have hSN : planeSylow T ZS ≤ M ⊓ I := le_inf
    (inf_le_left.trans hsource.maximal.1.2)
    ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right)
  have hbN : b.involution ∈ N :=
    (map_mono (comap_mono hSN)) (inverter_mem_planeSylow_image d b)
  let b' : N' := ⟨e b.involution,mem_map_of_mem e.toMonoidHom hbN⟩
  have hb' : orderOf b' = 2 := (Subgroup.orderOf_coe b').symm.trans
    ((orderOf_injective e.toMonoidHom e.injective b.involution).trans b.order_two)
  obtain ⟨j⟩ := SymmetricThreeProductResidual.equiv_symmetricThree_of_nonnormal_residual
    N' hn b' hb'
  exact ⟨(e.subgroupMap N).trans j⟩

/-- Construct the exact action of NI on V and its source index. The remaining
premises are the earlier action alternatives and distinguished involution. -/
theorem intersection_source_action (hI : PlaneEscapes Mc ZS I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (b : PlaneInverter hsource ZS)
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I) :
    (M ⊓ I).relIndex M = 6 ∧
      ∃ f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3), Function.Surjective f ∧
        f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I) ∧
        PushingUpSetup KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) := by
  have ho := omega_of_restricted_actions d hI ha hout
  obtain ⟨e⟩ := intersection_image_equiv_of_omega d hI hout ho b
  obtain ⟨f,hf,hker⟩ := exists_symmetricThree_action_of_image_equiv e
  exact ⟨intersection_index_six_of_image_equiv d hI ho e,f,hf,hker,
    d.intersection_pushingUpSetup_of_symmetricThree hI f hf hker⟩

/-- The literal classification consumer now needs neither an S₃ quotient
nor radical normalization as an extra component-selection premise. -/
theorem escaping_normalized_component_of_restricted_actions
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (b : PlaneInverter hsource ZS)
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y) :
    ∃ X : Subgroup G, ComponentCatalogue.Normalized H M I X := by
  obtain ⟨_,f,hf,hker,_⟩ := intersection_source_action d hI ha b hout
  exact d.escaping_normalized_component_of_symmetricThree hI hfit f hf hker hno

/-- The fixed point is transported by the original natural-action marking.
It belongs to ZS and generates a complement to the original seed Z. -/
theorem original_point_marking (hI : PlaneEscapes Mc ZS I)
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ho : letI := hsource.prepared.elementary;
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (b : PlaneInverter hsource ZS) :
    ∃ w : V, (w : G) ∈ ZS ∧ (w : G) ∉ centralInvolutions T ∧
      intersectionImage hsource I = pointStabilizer hsource w := by
  let := hsource.prepared.elementary
  obtain ⟨x,a,hx⟩ := ho.2.2.2.2
  obtain ⟨e⟩ := intersection_image_equiv_of_omega d hI hout ho b
  let N := intersectionImage hsource I
  let N' := N.map a.toMonoidHom
  have hn : ¬ ((pResidual 2 N').map N'.subtype).Normal := by
    rw [←map_embedded_pResidual]
    intro hn
    exact residualImage_not_normal d hI hout ((MulEquiv.normal_map_iff (f := a)).mp hn)
  have hN : Nat.card N' = 6 := by
    change Nat.card (N.map a.toMonoidHom) = 6
    rw [card_map_of_injective (f := a.toMonoidHom) a.injective,
      Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    rfl
  have hSN : planeSylow T ZS ≤ M ⊓ I := le_inf
    (inf_le_left.trans hsource.maximal.1.2)
    ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right)
  have hbN : b.involution ∈ N :=
    (map_mono (comap_mono hSN)) (inverter_mem_planeSylow_image d b)
  have hbo : orderOf (a b.involution) = 2 :=
    (orderOf_injective a.toMonoidHom a.injective b.involution).trans b.order_two
  obtain ⟨v,hv,hbv,he⟩ :=
    OrthogonalFourBinary.SylowGeometry.point_stabilizer_of_nonnormal_residual
      N' hN hn (a b.involution) (mem_map_of_mem a.toMonoidHom hbN) hbo
  let w : V := (x.symm v).toMul
  have hw : x (Additive.ofMul w) = v := x.apply_symm_apply v
  have hfix (g : internalActionImage M V hsource.prepared.normalized) :
      g.val w = w ↔ (a g) • v = v := by
    have hh := hx g (Additive.ofMul w)
    rw [hw] at hh
    change x (Additive.ofMul (g.val w)) = (a g).val.val v at hh
    constructor
    · intro hg
      change (a g).val.val v = v
      rw [←hh,hg,hw]
    · intro hg
      have hg' : Additive.ofMul (g.val w) = Additive.ofMul w :=
        x.injective (hh.trans (hg.trans hw.symm))
      exact congrArg Additive.toMul hg'
  have hp : N = pointStabilizer hsource w := by
    ext g
    have hg : g ∈ N ↔ a g ∈ N' := (mem_map_iff_mem a.injective).symm
    rw [he] at hg
    exact hg.trans (hfix g).symm
  have hwplane : (w : G) ∈ ZS := (b.fixed_plane w).mpr ((hfix b.involution).mpr hbv)
  have hwne : (w : G) ≠ 1 := by
    intro h1
    have h1' : Additive.ofMul w = 0 := congrArg Additive.ofMul (Subtype.ext h1)
    have hv0 : v = 0 := hw.symm.trans (h1' ▸ map_zero x)
    rw [hv0,map_zero] at hv
    exact zero_ne_one hv
  refine ⟨w,hwplane,?_,hp⟩
  intro hwZ
  have hw2 : (w : G)^2=1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property
  have hwo : orderOf (w : G) = 2 := orderOf_eq_prime hw2 hwne
  have heZ : zpowers (w : G) = centralInvolutions T :=
    eq_of_le_of_card_ge (zpowers_le.mpr hwZ)
      (by rw [Nat.card_zpowers,hwo,(d.escape_index hI).1])
  have hc := intersection_eq_centralizer_of_image d hI w hp
  rw [heZ,←d.partner_eq] at hc
  exact hout (le_inf (hc.le.trans inf_le_right) inf_le_right)

/-- The literal dichotomy of 15.2.18(3): either NI lies in MI, or the
original complement, centralizer, index-six action and C.2.3 input are all
constructed on the same NI. -/
theorem intersection_alternative_of_restricted_actions (hI : PlaneEscapes Mc ZS I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (b : PlaneInverter hsource ZS) :
    M ⊓ I ≤ Mc ⊓ I ∨
      (¬ M ⊓ I ≤ Mc ⊓ I) ∧
      (letI := hsource.prepared.elementary;
        SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized)) ∧
      ∃ Z1 : Subgroup G, Z1 ≤ ZS ∧ Disjoint (centralInvolutions T) Z1 ∧
        centralInvolutions T ⊔ Z1 = ZS ∧
        M ⊓ I = M ⊓ centralizer (Z1 : Set G) ∧ (M ⊓ I).relIndex M = 6 ∧
        ∃ f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3),
          Function.Surjective f ∧
          f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I) ∧
          PushingUpSetup KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) := by
  by_cases hout : M ⊓ I ≤ Mc ⊓ I
  · exact Or.inl hout
  · let := hsource.prepared.elementary
    have ho := omega_of_restricted_actions d hI ha hout
    obtain ⟨w,hw,hwZ,hpoint⟩ := original_point_marking d hI hout ho b
    obtain ⟨e⟩ := intersection_image_equiv_of_omega d hI hout ho b
    exact Or.inr ⟨hout, ho, original_stabilizer_consequences d hI ho w hw hwZ hpoint e⟩

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.OmegaAction
