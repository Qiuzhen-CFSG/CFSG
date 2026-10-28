module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexInitialReduction
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexCenter
public import Stellmacher.SectionEight.GeneratedEightSixInitialCenterResidual
public import Stellmacher.SectionEight.GeneratedEightFiveActionFromFour
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_involutive_subgroup_c4_square_card_le
    {G : Type u} [Group G] [Finite G] {core elementary : Subgroup G}
    (hmodel : IsModel core (C4 × C4))
    (hsquares : ∀ element : elementary, element ^ 2 = 1)
    (hle : elementary ≤ core) : Nat.card elementary ≤ 4 := by
  classical
  obtain ⟨model⟩ := hmodel
  let embedding : elementary → {element : C4 × C4 // element ^ 2 = 1} :=
    fun element => ⟨model ⟨element, hle element.property⟩, by
      have hsquare : element ^ 2 = 1 := hsquares element
      have hsquareCore : (⟨element, hle element.property⟩ : core) ^ 2 = 1 :=
        Subtype.ext (congrArg (fun point : elementary => (point : G)) hsquare)
      rw [← map_pow, hsquareCore, map_one]⟩
  have hinjective : Function.Injective embedding := by
    intro first second heq
    apply Subtype.ext
    exact congrArg (fun point : core => (point : G))
      (model.injective (congrArg Subtype.val heq))
  have hcard : Nat.card {element : C4 × C4 // element ^ 2 = 1} = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact hcard ▸ Nat.card_le_card_of_injective embedding hinjective

public theorem eight_six_elementary_subgroup_c4_square_card_le
    {G : Type u} [Group G] [Finite G] {core elementary : Subgroup G}
    (hmodel : IsModel core (C4 × C4))
    (helementary : IsElementaryAbelianSubgroup 2 elementary)
    (hle : elementary ≤ core) : Nat.card elementary ≤ 4 := by
  let _ : IsElementaryAbelian 2 elementary := helementary
  exact eight_six_involutive_subgroup_c4_square_card_le hmodel
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 elementary)) hle

public theorem eight_six_elementary_eight_escapes_c4_square
    {G : Type u} [Group G] [Finite G] {core D : Subgroup G}
    (hmodel : IsModel core (C4 × C4))
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hDcard : Nat.card D = 8) : ∃ actor : G,
      actor ∈ D ∧ actor ∉ core ∧ actor ^ 2 = 1 := by
  have hnot : ¬ D ≤ core := by
    intro hle
    have hbound := eight_six_elementary_subgroup_c4_square_card_le hmodel helementary hle
    omega
  obtain ⟨actor, hactor, houtside⟩ := SetLike.not_le_iff_exists.mp hnot
  let _ : IsElementaryAbelian 2 D := helementary
  refine ⟨actor, hactor, houtside, ?_⟩
  exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 D) (⟨actor, hactor⟩ : D))

public theorem eight_six_initial_center_full_action_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    ∀ symmetry : MulAut (ZAt ctx.Γ ctx.criticalPath.a), ∃ actor : G,
      actor ∈ GAt ctx.Γ ctx.criticalPath.a ∧
      ∀ element : ZAt ctx.Γ ctx.criticalPath.a,
        actor * (element : G) * actor⁻¹ = (symmetry element : G) := by
  classical
  let center := ZAt ctx.Γ ctx.criticalPath.a
  let initial := GAt ctx.Γ ctx.criticalPath.a
  have hfirst : ctx.criticalPath.firstStep ∈ neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hfirst
  have hcenterCore : center ≤ QAt ctx.Γ ctx.criticalPath.a :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _ hfirst).trans
      (Subgroup.map_subtype_le _)
  have hcoreInitial : QAt ctx.Γ ctx.criticalPath.a ≤ initial := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  obtain ⟨witness⟩ := exists_quotientModuleWitness initial center
    (hcenterCore.trans hcoreInitial) (stabilizer_le_normalizer_z ctx.Γ _)
  let _ := witness.groupX
  let _ := witness.finiteX
  have haction := eight_five_action_of_card_four_local ctx hcard witness
  have hXcard : Nat.card witness.X = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card haction
  let _ : Nontrivial center := not_subsingleton_iff_nontrivial.mp (by
    intro hsubsingleton
    have hone : Nat.card center = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨hsubsingleton, inferInstance⟩
    change Nat.card center = 4 at hcard
    omega)
  let _ : IsKleinFour center := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  have hsurjective : Function.Surjective witness.action :=
    ((Nat.bijective_iff_injective_and_card witness.action).mpr
      ⟨witness.action_injective, hXcard.trans (IsKleinFour.card_mulAut center).symm⟩).2
  intro symmetry
  obtain ⟨image, himage⟩ := hsurjective symmetry
  obtain ⟨actor, hactor⟩ := witness.surjective image
  refine ⟨actor, actor.property, fun element => ?_⟩
  rw [← witness.action_compatible actor element, hactor, himage]

public theorem eight_six_initial_center_le_residual_core_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    ZAt ctx.Γ ctx.criticalPath.a ≤ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) := by
  have hfirst : ctx.criticalPath.firstStep ∈ neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj
  have hcenterCore : ZAt ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ ctx.criticalPath.a :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _ hfirst).trans
      (Subgroup.map_subtype_le _)
  have hcommutator := eight_six_initial_center_residual_local ctx hcenter hcard
  rw [← hcommutator, Subgroup.commutator_comm]
  exact (Subgroup.commutator_mono le_rfl hcenterCore).trans (by
    change ⁅ctx.Γ.twoResidualAt ctx.criticalPath.a,
      ctx.Γ.twoCoreAt ctx.criticalPath.a⁆ ≤ twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a)
    simp only [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def]
    exact SevenSix.residual_commutator_core_le (GAt ctx.Γ ctx.criticalPath.a))

public theorem eight_six_initial_residual_core_normal_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2) :
    NormalIn (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a))
      (GAt ctx.Γ ctx.criticalPath.a) := by
  change NormalIn (twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a)) _
  rw [ctx.Γ.twoResidualAt_def]
  exact ⟨(SevenSix.twoCoreIn_le _).trans (SevenSix.twoResidualIn_le _),
    SevenSix.twoCoreIn_normal_of_normal _ _ (SevenSix.twoResidualIn_le _)
      (SevenSix.twoResidualIn_normal _)⟩

public theorem eight_six_elementary_intersection_c4_square
    {G : Type u} [Group G] [Finite G] {core D Z : Subgroup G}
    (hmodel : IsModel core (C4 × C4))
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hZcard : Nat.card Z = 4) (hZD : Z ≤ D) (hZcore : Z ≤ core) :
    D ⊓ core = Z := by
  let _ : IsElementaryAbelian 2 D := helementary
  have hsquares : ∀ element : (D ⊓ core : Subgroup G), element ^ 2 = 1 := by
    intro element
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := D)
      (element : G) element.property.1
  have hbound := eight_six_involutive_subgroup_c4_square_card_le hmodel hsquares inf_le_right
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hZD hZcore) (by omega)).symm

public theorem eight_six_initial_inverter_of_elementary_action_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (orders : EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hcore : IsModel (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) (C4 × C4))
    (hQcard : Nat.card Q = 32)
    (hclassification : ∀ actor : G, actor ∈ D →
      (∀ element : G, element ∈ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) →
        actor * element * actor⁻¹ = element) ∨
      IsInvertingOn actor (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a))) :
    ∃ actor : G, actor ∈ Q ∧
      IsInvertingOn actor (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) := by
  have hDcard : Nat.card D = 8 := by
    rcases eight_six_initial_order_cases ctx.Γ ctx.criticalPath orders hcard with hsmall | hlarge
    · omega
    · exact hlarge.1
  obtain ⟨actor, hactorD, houtside, _⟩ :=
    eight_six_elementary_eight_escapes_c4_square hcore helementary hDcard
  have hDQ := (eight_six_equation_one_core_containments ctx.Γ ctx.criticalPath
    previous D L Q data helementary).1
  have hactorQ := hDQ hactorD
  refine ⟨actor, hactorQ, ?_⟩
  rcases hclassification actor hactorD with hfixed | hinverts
  · have hcoreQ : twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤ Q := by
      rw [eight_six_initial_residual_core_eq ctx.Γ ctx.criticalPath orders]
      exact inf_le_right
    have hcorecard : Nat.card (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) = 16 := by
      obtain ⟨model⟩ := hcore
      rw [Nat.card_congr model.toEquiv, Nat.card_prod]
      simp [C4]
    have hgenerated := eight_six_generated_with_of_index_two hcoreQ
      (by rw [hQcard, hcorecard]) hactorQ houtside
    have hcoreCentral : twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
        Subgroup.centralizer ({actor} : Set G) := by
      intro element helement
      apply Subgroup.mem_centralizer_iff.mpr
      intro other hother
      obtain rfl := Set.mem_singleton_iff.mp hother
      exact mul_inv_eq_iff_eq_mul.mp (hfixed element helement)
    have hactorCentral : actor ∈ Subgroup.centralizer ({actor} : Set G) := by
      simp [Subgroup.mem_centralizer_iff]
    have hQCentral : Q ≤ Subgroup.centralizer ({actor} : Set G) := by
      rw [hgenerated]
      exact sup_le hcoreCentral (Subgroup.zpowers_le.mpr hactorCentral)
    have hcentral : actor ∈ CenterAmbient Q := by
      rw [eight_six_centerAmbient_eq_inf_centralizer]
      refine ⟨hactorQ, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro element helement
      exact (Subgroup.mem_centralizer_iff.mp (hQCentral helement) actor (by simp)).symm
    have hactorZ : actor ∈ ZAt ctx.Γ ctx.criticalPath.a := by
      rw [← orders.center_intersection]
      exact ⟨hactorD, hcentral⟩
    exact False.elim (houtside
      (eight_six_initial_center_le_residual_core_local ctx hcenter hcard hactorZ))
  · exact hinverts

public theorem eight_six_initial_inverter_intersection_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    {D Q : Subgroup G}
    (orders : EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hcore : IsModel (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a)) (C4 × C4)) :
    D ⊓ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) = ZAt ctx.Γ ctx.criticalPath.a := by
  exact eight_six_elementary_intersection_c4_square hcore helementary hcard
    (by rw [← orders.center_intersection]; exact inf_le_left)
    (eight_six_initial_center_le_residual_core_local ctx hcenter hcard)

end Stellmacher.SectionEight
