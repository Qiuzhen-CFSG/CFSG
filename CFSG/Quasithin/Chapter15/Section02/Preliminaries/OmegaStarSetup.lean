module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidualImage
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidualStar
public import Theory.GroupTheory.PResidual.InvolutiveImage
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# The literal star action in the full Omega residual branch

The action factors through M/O₂(M), since its image S₃×S₃ has trivial
two-core. When the image of Y has order nine it is the full two-residual;
together with the Sylow two-subgroup it covers the actor. Lifting gives
the cover Y* C_M(V)* T*. The source centralization and this cover prove
that Rc* meets the action kernel trivially, so its action is faithful.

These are preparations for the elementary-nine/extraspecial alternatives
of Aschbacher--Smith15.2.3(1), printed p.1105. The original Y, chosen module,
and quotient maps are retained throughout.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation {D : Type*} [Group D] [Finite D] (H : Subgroup D) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    exact ⟨hN, IsPGroup.of_card hn⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hN, IsPGroup.iff_card.mp hp⟩

omit [Finite G] in
/-- The Omega action kills the original two-core. -/
theorem source_omega_core_le_kernel {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    pCore 2 M ≤ (actionHom M V hn).rangeRestrict.ker := by
  let f := (actionHom M V hn).rangeRestrict
  let e := ho.2.2.2.1.some
  have hn : ((pCore 2 M).map (e.toMonoidHom.comp f)).Normal :=
    Normal.map inferInstance _ (e.surjective.comp (actionHom M V hn).rangeRestrict_surjective)
  have hp : (pCore 2 M).map (e.toMonoidHom.comp f) ≤
      pCore 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
    le_sSup ⟨hn, pCore_isPGroup.map _⟩
  rw [SymmetricThreeProduct.twoCore_eq_bot] at hp
  intro x hx
  exact e.injective ((Subgroup.mem_bot.mp (hp (mem_map_of_mem _ hx))).trans e.map_one.symm)

omit [Finite G] in
/-- The chosen-module actor on the literal star quotient. -/
noncomputable def omegaStarActor {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    (M ⧸ pCore 2 M) →* (actionHom M V hn).range :=
  QuotientGroup.lift (pCore 2 M) (actionHom M V hn).rangeRestrict
    (source_omega_core_le_kernel hn ho)

omit [Finite G] in
/-- Passing through the star quotient preserves the actual action image. -/
theorem omegaStarActor_map {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) (X : Subgroup M) :
    (X.map (QuotientGroup.mk' (pCore 2 M))).map (omegaStarActor hn ho) =
      X.map (actionHom M V hn).rangeRestrict := by
  rw [map_map]
  rfl

omit [Finite G] in
/-- The star action kernel is precisely the image of the original centralizer. -/
theorem omegaStarActor_ker {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    (omegaStarActor hn ho).ker =
      ((M ⊓ centralizer (V : Set G)).subgroupOf M).map (QuotientGroup.mk' (pCore 2 M)) := by
  rw [omegaStarActor, QuotientGroup.ker_lift, MonoidHom.ker_rangeRestrict, actionHom_ker]
  congr 1
  ext x
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

/-- The original residual is contained in M. -/
theorem source_omega_caseIIResidual_le (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    caseIIResidual T M (chosenStarredPreimage M V hn) Mc ≤ M := by
  rw [source_omega_caseIIResidual_eq T hTM hn ho]
  exact (map_subtype_le _).trans
    (conjugateSpanBy_le_self ((pCoreIn_le 2 _).trans inf_le_left))

/-- The intrinsic quotient of the original Y is its literal image in M/O₂(M). -/
noncomputable def omegaResidualCoreQuotientEquivStar (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hn) Mc
    (Y ⧸ pCore 2 Y) ≃* (Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M)) := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hn) Mc
  let N := Y.subgroupOf M
  let : N.Normal := source_omega_lemma_15_2_3_2 T hTM hn ho
  let e := (subgroupOfEquivOfLe (source_omega_caseIIResidual_le T (Mc := Mc) hTM hn ho)).symm
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans (coreQuotientEquivImage 2 N)

/-- The quotient identification retains the actual source representatives. -/
@[simp] theorem omegaResidualCoreQuotientEquivStar_apply_mk (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn))
    (y : caseIIResidual T M (chosenStarredPreimage M V hn) Mc) :
    ((omegaResidualCoreQuotientEquivStar T hTM hn ho)
      (QuotientGroup.mk' (pCore 2 (caseIIResidual T M (chosenStarredPreimage M V hn) Mc)) y) :
      M ⧸ pCore 2 M) = QuotientGroup.mk' (pCore 2 M)
        (Subgroup.inclusion (source_omega_caseIIResidual_le T hTM hn ho) y) := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hn) Mc
  let : (Y.subgroupOf M).Normal := source_omega_lemma_15_2_3_2 T hTM hn ho
  change ((coreQuotientEquivImage 2 (Y.subgroupOf M))
    (QuotientGroup.mk' _ ((subgroupOfEquivOfLe
      (source_omega_caseIIResidual_le T hTM hn ho)).symm y)) : M ⧸ pCore 2 M) = _
  exact coreQuotientEquivImage_apply_mk _ _ _

/-- The order-nine action image is the full ambient two-residual. -/
theorem source_omega_nine_image_eq (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 9) :
    ((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict = pResidual 2 (actionHom M V hn).range := by
  have he := source_omega_caseIIResidual_image T (Mc := Mc) hTM hn ho
    (actionHom M V hn).rangeRestrict (actionHom M V hn).rangeRestrict_surjective
  rw [he, residual_notation] at hcard ⊢
  exact SymmetricThreeProductResidual.normalClosure_residual_eq_of_card_nine
    ho.2.2.2.1.some _ hcard

/-- The source cover and normalizing subgroup on the actual star quotient. -/
theorem source_omega_nine_star_cover (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 9) :
    let q := QuotientGroup.mk' (pCore 2 M)
    let P := ((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map q
    let R := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map q
    let S := (T.subtype hTM : Subgroup M).map q
    P ⊔ (omegaStarActor hn ho).ker ⊔ S = ⊤ ∧ S ≤ normalizer (R : Set (M ⧸ pCore 2 M)) := by
  let q := QuotientGroup.mk' (pCore 2 M)
  let P := ((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map q
  let R := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map q
  let S := (T.subtype hTM : Subgroup M).map q
  let f := omegaStarActor hn ho
  constructor
  · have hm : (P ⊔ S).map f = ⊤ := by
      rw [Subgroup.map_sup, omegaStarActor_map, omegaStarActor_map,
        source_omega_nine_image_eq T hTM hn ho hcard]
      exact pResidual_sup_sylow_eq_top
        ((T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective)
    have hh := congrArg (comap f) hm
    rw [comap_map_eq, comap_top] at hh
    exact (sup_right_comm P f.ker S).trans hh
  · apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    have hRcM : (M ⊓ Mc).pCoreIn 2 ≤ M := (pCoreIn_le 2 _).trans inf_le_left
    rw [← subgroupOf_normalizer_eq hRcM]
    change (T : Subgroup G).subgroupOf M ≤ (normalizer ((M ⊓ Mc).pCoreIn 2 : Set G)).subgroupOf M
    apply comap_mono
    exact (le_inf hTM hTMc).trans ((M ⊓ Mc).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (M ⊓ Mc) (pCore 2 (M ⊓ Mc : Subgroup G))))

/-- On the full-image branch, Rc* has faithful action on the chosen module. -/
theorem source_omega_nine_rc_star_disjoint_kernel (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 9) :
    Disjoint ((((M ⊓ Mc).pCoreIn 2).subgroupOf M).map (QuotientGroup.mk' (pCore 2 M)))
      (omegaStarActor hV.normalized ho).ker := by
  have hTMc : (T : Subgroup G) ≤ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  let q := QuotientGroup.mk' (pCore 2 M)
  let P := ((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map q
  let R := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map q
  let S := (T.subtype hTM : Subgroup M).map q
  let f := omegaStarActor hV.normalized ho
  obtain ⟨hcover, hs⟩ := source_omega_nine_star_cover T hTM hTMc hV.normalized ho hcard
  have hc : f.ker ≤ centralizer ((P ⊔ R : Subgroup (M ⧸ pCore 2 M)) : Set _) := by
    rw [omegaStarActor_ker]
    apply le_centralizer_iff.mpr
    rw [sup_comm]
    exact source_omega_lemma_15_2_3_5 T hTM hu hV ho
  have hR : IsPGroup 2 R := (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype.map q
  apply disjoint_iff.mpr
  apply bot_unique
  have hh := inf_le_twoCore_of_centralizing_cover P R f.ker S hR hc hs hcover
  rwa [pCore_quotient_pCore_eq_bot] at hh

end CFSG.Quasithin.Chapter15.Section02
end
