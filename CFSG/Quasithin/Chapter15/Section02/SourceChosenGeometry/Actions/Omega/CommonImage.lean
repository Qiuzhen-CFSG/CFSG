module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.CubicObstruction
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Inputs
public import Theory.GroupTheory.OddCoreInvolutionGeometry

/-!
# The common plane in the natural Omega action

These are the original preceding 15.2.1--12 inputs, retaining the actual
conjugation image and natural Omega coordinates. A source involution has
no nontrivial cubic subgroup in its centralizer, by the literal plane
normalizer and residual bounds. Its elementary odd core therefore has
full commutator. Fitting self-centralization proves uniqueness in the
original Sylow image, and the existing fixed/moved transport identifies
all ambient commutator planes.

The earlier premises are discharged by qt-e-152-plane-geometry. No common
image, odd-core identity or fixed/moved-plane conclusion is assumed here.
Source: Aschbacher--Smith 15.2.13, printed pp.1111--1112, refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Omega
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open Cyclic
variable {G : Type*} [Group G] [Finite G]
structure Preceding {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (H : Subgroup G) : Prop where
  omega : letI := h.prepared.elementary
    SourceCases.Omega (imageRepresentation M V h.prepared.normalized)
  outside : H ∈ Chapter3.HStar (T : Subgroup G) M
  two_overgroups : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc}
  quotient : Nonempty ((H ⧸ pCore 2 H) ≃*
    RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))
  full : V = localModule T M
  nonempty : (sigmaOutside (T : Subgroup G) H).Nonempty
  planes : letI := h.prepared.elementary
    ∀ B ∈ sigmaOutside (T : Subgroup G) H,
      IsElementaryTwo (actor M V B h.prepared.normalized) ∧
      IsQuadratic (imageRepresentation M V h.prepared.normalized)
        (actor M V B h.prepared.normalized) ∧
      ⁅V,B⁆ ≤ V ∧ Nat.card (⁅V,B⁆ : Subgroup G) = 4 ∧
      H ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
      normalizer (⁅V,B⁆ : Subgroup G) ≤ Mc ∧
      ChosenGeometry.residual H ≤ centralizer (⁅V,B⁆ : Subgroup G)
  residual_eq : partnerSpan H Mc = threePrimeResidual Mc
  residual_centralizes : partnerSpan H Mc ≤ centralizer (centralInvolutions T : Set G)

/-- The sigma actors lie in the fixed ambient Sylow subgroup because they lie
in the two-core of H. -/
theorem Preceding.actor_le_sylow {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) : B ≤ (T : Subgroup G) := by
  obtain ⟨A,hA,hAT,rfl⟩ := exists_offender_of_mem_sigmaOutside hB
  have hh := map_mono (f := H.subtype)
    (pCore_isPGroup.le_sylow_of_normal (T.subtype d.outside.1.1.2))
  change (pCore 2 H).map H.subtype ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
  rw [map_subgroupOf_eq_of_le d.outside.1.1.2] at hh
  exact inf_le_right.trans hh


/-- No nontrivial three-subgroup centralizes a literal offender image. -/
theorem Preceding.three_centralizer_eq_bot {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H)
    (C : Subgroup (internalActionImage M V h.prepared.normalized))
    (hp : IsPGroup 3 C)
    (hC : C ≤ centralizer (actor M V B h.prepared.normalized : Set _)) : C = ⊥ := by
  let := h.prepared.elementary
  let A := actor M V B h.prepared.normalized
  have hAc := (quadratic_fixed_eq_moved h A (d.planes B hB).1 (d.planes B hB).2.1).1
  let : IsCyclic A := isCyclic_of_prime_card hAc
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hAt : zpowers t = A := ht
  have htA : t ∈ A := ht ▸ mem_zpowers t
  have ht2 : t ^ 2 = 1 := congrArg Subtype.val
    (hAc ▸ pow_card_eq_one' (x := (⟨t,htA⟩ : A)))
  have hpE := (d.planes B hB).2.2
  apply three_image_centralizer_eq_bot h hpE.1 hpE.2.1 hpE.2.2.2.1 hpE.2.2.2.2.1
    (d.residual_eq ▸ d.residual_centralizes) t ht2 _ C hp
    (hC.trans (centralizer_le (Set.singleton_subset_iff.mpr htA)))
  rw [hAt, ambientSpace_fixed _ ((d.actor_le_sylow hB).trans h.maximal.1.2)]
  exact ambient_fixed_eq_commutator h ((d.actor_le_sylow hB).trans h.maximal.1.2)
    (d.planes B hB).1 (d.planes B hB).2.1




/-- The natural Omega odd core is elementary abelian of exponent three. -/
theorem Preceding.oddCore_elementary {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H) :
    IsElementaryAbelian 3 (pPrimeCore 2 (internalActionImage M V h.prepared.normalized)) := by
  let := h.prepared.elementary
  obtain ⟨x,e,hx⟩ := d.omega.2.2.2.2
  let f := (e.toMonoidHom.comp (pPrimeCore 2 _).subtype).codRestrict
    (pResidual 2 OrthogonalFourBinary.omega) (fun a =>
      map_pResidual_le 2 e.toMonoidHom
        (mem_map_of_mem e.toMonoidHom (pPrimeCore_le_pResidual a.property)))
  let := OrthogonalFourBinary.omega_twoResidual_elementary
  exact IsElementaryAbelian.of_injective f (fun a b hab =>
    Subtype.ext (e.injective (congrArg Subtype.val hab)))

/-- Each literal source offender moves the entire odd core of the image. -/
theorem Preceding.oddCore_commutator {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
      ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),
        actor M V B h.prepared.normalized⁆ := by
  let := h.prepared.elementary
  let A := actor M V B h.prepared.normalized
  have hc := (quadratic_fixed_eq_moved h A (d.planes B hB).1 (d.planes B hB).2.1).1
  let : IsCyclic A := isCyclic_of_prime_card hc
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have he : zpowers t = actor M V B h.prepared.normalized := ht
  rw [←he]
  apply oddCore_commutator_of_three_centralizer d.oddCore_elementary.isPGroup t
  intro C hp hC
  apply d.three_centralizer_eq_bot hB C hp
  rw [←he]
  apply le_centralizer_iff.mp
  apply zpowers_le.mpr
  intro c hc
  exact mem_centralizer_singleton_iff.mp (hC hc)

/-- The odd-core condition uniquely identifies an order-two subgroup in T-bar. -/
theorem Preceding.order_two_images_eq {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (A B : Subgroup (internalActionImage M V h.prepared.normalized))
    (hAP : A ≤ actor M V (T : Subgroup G) h.prepared.normalized)
    (hBP : B ≤ actor M V (T : Subgroup G) h.prepared.normalized)
    (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    (ha : pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
      ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),A⁆)
    (hb : pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
      ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),B⁆) : A = B := by
  let := h.prepared.elementary
  let := d.oddCore_elementary
  have hs := source_chosen_action_isSolvable h.ambient T h.empty h.maximal V
    h.prepared.normalized h.prepared.le_local
  have hc : pCore 2 (internalActionImage M V h.prepared.normalized) = ⊥ := by
    rw [←chosenNormalizer_actionImage_eq T h.maximal.1.2 h.prepared.normalized]
    exact chosenNormalizer_actionImage_reduced T h.maximal.1.2 h.prepared.le_selected
      h.prepared.normalized h.prepared.seed_span
  exact oddCore_involution_subgroup_unique hs hc _ A B
    ((T.subtype h.maximal.1.2).isPGroup'.map _) hAP hBP hA hB ha hb

/-- The common involution image and all fixed/moved-plane identities in the
natural Omega row of original 15.2.13. -/
theorem Preceding.common_plane {T : Sylow 2 G} {M Mc V H : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H) :
    letI := h.prepared.elementary
    ∃ B₀ : Subgroup (internalActionImage M V h.prepared.normalized),
      B₀ ≤ actor M V (T : Subgroup G) h.prepared.normalized ∧ Nat.card B₀ = 2 ∧
      pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
        ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),B₀⁆ ∧
      (∀ A : Subgroup (internalActionImage M V h.prepared.normalized),
        A ≤ actor M V (T : Subgroup G) h.prepared.normalized → Nat.card A = 2 →
        pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
          ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),A⁆ → A = B₀) ∧
      ∀ B ∈ sigmaOutside (T : Subgroup G) H,
        actor M V B h.prepared.normalized = B₀ ∧
        V ⊓ centralizer (B : Set G) = ⁅V,B⁆ ∧
        ⁅V,B⁆ = ambientSpace V (subspaceCommutator
          (imageRepresentation M V h.prepared.normalized) ⊤ B₀) ∧
        ambientSpace V (subspaceCommutator
          (imageRepresentation M V h.prepared.normalized) ⊤ B₀) =
          ambientSpace V (fixedSpace (imageRepresentation M V h.prepared.normalized) B₀) ∧
        centralInvolutions T ≤ ⁅V,B⁆ := by
  let := h.prepared.elementary
  obtain ⟨B,hB⟩ := d.nonempty
  let B₀ := actor M V B h.prepared.normalized
  have hBT := d.actor_le_sylow hB
  have hBP : B₀ ≤ actor M V (T : Subgroup G) h.prepared.normalized :=
    map_mono (comap_mono hBT)
  obtain ⟨hc,hfm⟩ := quadratic_fixed_eq_moved h B₀ (d.planes B hB).1 (d.planes B hB).2.1
  have ho := d.oddCore_commutator hB
  refine ⟨B₀,hBP,hc,ho,?_,?_⟩
  · intro A hAP hAc hAo
    exact d.order_two_images_eq A B₀ hAP hBP hAc hc hAo ho
  · intro C hC
    have hCT := d.actor_le_sylow hC
    have hcc := (quadratic_fixed_eq_moved h _ (d.planes C hC).1 (d.planes C hC).2.1).1
    have he : actor M V C h.prepared.normalized = B₀ :=
      d.order_two_images_eq _ _ (map_mono (comap_mono hCT)) hBP hcc hc
        (d.oddCore_commutator hC) ho
    refine ⟨he,ambient_fixed_eq_commutator h (hCT.trans h.maximal.1.2)
      (d.planes C hC).1 (d.planes C hC).2.1,?_,?_,
      seed_le_commutator h d.full hCT (d.planes C hC).1 (d.planes C hC).2.1⟩
    · rw [←he]
      exact (ambientSpace_moved _ h.prepared.le_selected (hCT.trans h.maximal.1.2)).symm
    · exact congrArg (ambientSpace V) hfm.symm
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Omega
