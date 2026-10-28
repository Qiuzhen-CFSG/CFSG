module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Assembly
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallRankOneSelection.Omega
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.PlaneInput

/-!
# The common offender plane from the actual residual inputs

In the cyclic rows the prime odd core is moved by every nontrivial offender.
In the Omega row the offender centralizer has order prime to three, so its
involution moves the whole elementary cubic odd core. The involution image
is therefore unique in the original Sylow image. All actual residual inputs
have the same commutator plane, and every H-star residual centralizes it.

This constructs the marked plane inverter without the prime-complement
residual identities. The global H-star wreath quotients remain explicit.
Source: Aschbacher--Smith, 15.2.13--14, printed pp.1111--1112.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor Cyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

private theorem action_core_eq_bot {h : ChosenSmallSource T M Mc V} :
    pCore 2 (internalActionImage M V h.prepared.normalized) = ⊥ := by
  let := h.prepared.elementary
  rw [←chosenNormalizer_actionImage_eq T h.maximal.1.2 h.prepared.normalized]
  exact chosenNormalizer_actionImage_reduced T h.maximal.1.2 h.prepared.le_selected
    h.prepared.normalized h.prepared.seed_span

private theorem omega_oddCore_elementary {h : ChosenSmallSource T M Mc V}
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) :
    IsElementaryAbelian 3 (pPrimeCore 2 (internalActionImage M V h.prepared.normalized)) := by
  let := h.prepared.elementary
  obtain ⟨x,e,hx⟩ := ho.2.2.2.2
  let f := (e.toMonoidHom.comp (pPrimeCore 2 _).subtype).codRestrict
    (pResidual 2 OrthogonalFourBinary.omega) (fun a =>
      map_pResidual_le 2 e.toMonoidHom
        (mem_map_of_mem e.toMonoidHom (pPrimeCore_le_pResidual a.property)))
  let := OrthogonalFourBinary.omega_twoResidual_elementary
  exact IsElementaryAbelian.of_injective f (fun a b hab =>
    Subtype.ext (e.injective (congrArg Subtype.val hab)))

private theorem restricted_card {h : ChosenSmallSource T M Mc V} (hr : RestrictedModels h) :
    Nat.card (internalActionImage M V h.prepared.normalized) = 6 ∨
      Nat.card (internalActionImage M V h.prepared.normalized) = 10 ∨
      Nat.card (internalActionImage M V h.prepared.normalized) = 20 := by
  let := h.prepared.elementary
  rcases hr with ⟨_,⟨e⟩⟩ | ⟨_,he⟩
  · left
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  · rcases he with he | he
    · obtain ⟨e⟩ := he
      exact Or.inr (Or.inl ((Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card))
    · obtain ⟨e⟩ := he
      exact Or.inr (Or.inr ((Nat.card_congr e.toEquiv).trans
        BenderSuzuki.MatrixGroups.suzukiZero_card))

/-- The actual offender moves the whole odd core in each surviving action model. -/
theorem ResidualInput.actor_oddCore_commutator {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) :
    pPrimeCore 2 (internalActionImage M V h.prepared.normalized) =
      ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),
        actor M V B h.prepared.normalized⁆ := by
  let := h.prepared.elementary
  let D := internalActionImage M V h.prepared.normalized
  by_cases ho : SourceCases.Omega (imageRepresentation M V h.prepared.normalized)
  · have hAc := (quadratic_fixed_eq_moved h _
      d.actor_quadratic_of_plane.1 d.actor_quadratic_of_plane.2).1
    let : IsCyclic (actor M V B h.prepared.normalized) := isCyclic_of_prime_card hAc
    obtain ⟨t,ht⟩ := (actor M V B h.prepared.normalized).isCyclic_iff_exists_zpowers_eq_top.mp
      inferInstance
    rw [←ht]
    apply oddCore_commutator_of_three_centralizer (omega_oddCore_elementary (h := h) ho).isPGroup t
    intro C hp hC
    apply eq_bot_of_card_eq
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    have hcop := (d.actor_generator_centralizer_three_free t ht).of_dvd_right (card_dvd_of_le hC)
    have hc : Nat.card C ∣ 3 ^ n := by rw [hn]
    exact Nat.eq_one_of_dvd_coprimes (hcop.symm.pow_right n) dvd_rfl hc
  · have hr : RestrictedModels h := d.restricted_models_or_omega.resolve_right ho
    let P : Sylow 2 D := (T.subtype h.maximal.1.2).mapSurjective
      (actionHom M V h.prepared.normalized).rangeRestrict_surjective
    have hP : IsCyclic P := sylow_image_cyclic h h.action_alternatives ho
    have hc := restricted_card hr
    have heven : 2 ∣ Nat.card D := by
      rcases hc with hc | hc | hc <;> rw [hc] <;> decide
    have hprime : (Nat.card (pPrimeCore 2 D)).Prime := by
      have hcount := (P.isComplement'_pPrimeCore_of_isCyclic hP heven).card_mul_card
      have hPc := P.card_eq_multiplicity
      rcases hc with hc | hc | hc
      all_goals
        rw [hc] at hPc hcount
        norm_num [show (Nat.factorization 6) 2 = 1 from by decide +kernel,
          show (Nat.factorization 10) 2 = 1 from by decide +kernel,
          show (Nat.factorization 20) 2 = 2 from by decide +kernel] at hPc
        rw [hPc] at hcount
        have hh : Nat.card (pPrimeCore 2 D) = 3 ∨ Nat.card (pPrimeCore 2 D) = 5 := by omega
        rcases hh with hh | hh <;> rw [hh] <;> decide
    exact oddCore_commutator_eq_of_cyclic_sylow P hP heven (action_core_eq_bot (h := h)) hprime _
      (map_mono (comap_mono d.offender_le_sylow)) d.actor_quadratic_of_plane.1.1

/-- Any two original residual inputs have the same order-two actor image. -/
theorem ResidualInput.actor_eq_of_residualInput {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) {J C : Subgroup G} (r : ResidualInput h J C) :
    actor M V B h.prepared.normalized = actor M V C h.prepared.normalized := by
  let := h.prepared.elementary
  have hBP := map_mono (f := (actionHom M V h.prepared.normalized).rangeRestrict)
    (comap_mono (f := M.subtype) d.offender_le_sylow)
  have hCP := map_mono (f := (actionHom M V h.prepared.normalized).rangeRestrict)
    (comap_mono (f := M.subtype) r.offender_le_sylow)
  have hb := (quadratic_fixed_eq_moved h _
    d.actor_quadratic_of_plane.1 d.actor_quadratic_of_plane.2).1
  have hc := (quadratic_fixed_eq_moved h _
    r.actor_quadratic_of_plane.1 r.actor_quadratic_of_plane.2).1
  by_cases ho : SourceCases.Omega (imageRepresentation M V h.prepared.normalized)
  · let := omega_oddCore_elementary (h := h) ho
    have hs := source_chosen_action_isSolvable h.ambient T h.empty h.maximal V
      h.prepared.normalized h.prepared.le_local
    exact oddCore_involution_subgroup_unique hs (action_core_eq_bot (h := h)) _ _ _
      ((T.subtype h.maximal.1.2).isPGroup'.map _) hBP hCP hb hc
      d.actor_oddCore_commutator r.actor_oddCore_commutator
  · exact order_two_images_eq h h.action_alternatives ho hBP hCP hb hc

/-- The literal offender commutator plane is independent of the residual input. -/
theorem ResidualInput.plane_eq_of_residualInput {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) {J C : Subgroup G} (r : ResidualInput h J C) :
    ⁅V,B⁆ = ⁅V,C⁆ := by
  let := h.prepared.elementary
  rw [←ambientSpace_moved _ h.prepared.le_selected
      (d.offender_le_sylow.trans h.maximal.1.2),
    ←ambientSpace_moved _ h.prepared.le_selected (r.offender_le_sylow.trans h.maximal.1.2),
    d.actor_eq_of_residualInput r]

/-- Every H-star residual centralizes the common plane, without a residual-identity premise. -/
theorem ResidualInput.all_residuals_centralize_plane {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B)
    (hquotient : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((J ⧸ pCore 2 J) ≃* Wreath)) :
    ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (⁅V,B⁆ : Subgroup G) := by
  intro J hJ
  obtain ⟨C,r⟩ := h.exists_residualInput_of_preceding h.action_alternatives hJ
    (hquotient J hJ) d.two_overgroups
  rw [d.plane_eq_of_residualInput r]
  exact r.residual_centralizes_plane

/-- The common order-two actor provides the marked inverter of the original plane. -/
theorem ResidualInput.exists_planeInverter {h : ChosenSmallSource T M Mc V}
    (d : ResidualInput h H B) :
    Nonempty (PlaneUniquenessPreceding.OmegaAction.PlaneInverter h ⁅V,B⁆) := by
  let := h.prepared.elementary
  let A := actor M V B h.prepared.normalized
  have hc : Nat.card A = 2 := (quadratic_fixed_eq_moved h _
    d.actor_quadratic_of_plane.1 d.actor_quadratic_of_plane.2).1
  let : IsCyclic A := isCyclic_of_prime_card hc
  obtain ⟨b,hb⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hBP : A ≤ actor M V (T : Subgroup G) h.prepared.normalized :=
    map_mono (comap_mono d.offender_le_sylow)
  refine ⟨⟨b,hBP (hb ▸ mem_zpowers b),?_,?_,?_⟩⟩
  · rw [←Nat.card_zpowers,hb,hc]
  · rw [hb]; exact d.actor_oddCore_commutator.symm
  · have he : ambientSpace V (fixedSpace
        (imageRepresentation M V h.prepared.normalized) (zpowers b)) = ⁅V,B⁆ := by
      rw [hb,ambientSpace_fixed _ (d.offender_le_sylow.trans h.maximal.1.2)]
      exact ambient_fixed_eq_commutator h (d.offender_le_sylow.trans h.maximal.1.2)
        d.actor_quadratic_of_plane.1 d.actor_quadratic_of_plane.2
    intro v
    rw [←he,mem_ambientSpace,mem_fixedSpace_zpowers_iff]
    rfl

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
