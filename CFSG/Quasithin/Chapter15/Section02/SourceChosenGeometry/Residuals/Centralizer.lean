module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.Intersection
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Recognition
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallWholeAction

/-!
# Partner centralization from the original residual plane

The four-dimensional non-FF action and the literal commutator plane of
order four force the offender image to be quadratic. The already proved
intersection residual calculation makes its plane stabilizer have order
prime to three. This excludes the S₃ × C₃ and cyclic-fifteen action rows
without assuming the still-open equality Kc = O^{3′}(Mc).

The surviving cyclic models have maximal Sylow image. In the Omega row,
the intersection image is a two-group and hence equals the original Sylow
image. The source ordering factorization then identifies Mc with C_G(Z)
in every row. Consequently the literal O^{3′}(Mc) centralizes Z, and every
three-subgroup normalizing the actual commutator plane fixes it pointwise.
The actual seed lies in that plane as well.

These consequences do not identify Kc with O^{3′}(Mc) in the equality row
or exclude the retained Held model. Those obligations stay with
`qt-e-152-residual-geometry`; `qt-e-152-plane-geometry` supplies the earlier
`ResidualInput` premises and owns the final source assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
15.2.12(4)--15.2.14(5), printed pp.1111--1112. This proof obtains the
centralization and centralizer clauses before the full residual identity.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor Cyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- The order-four commutator on the chosen four-space forces the literal actor to be quadratic. -/
theorem ResidualInput.actor_quadratic_of_plane
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    letI := h.prepared.elementary
    IsElementaryTwo (actor M V B h.prepared.normalized) ∧
      IsQuadratic (imageRepresentation M V h.prepared.normalized)
        (actor M V B h.prepared.normalized) := by
  let := h.prepared.elementary
  let A := actor M V B h.prepared.normalized
  let ρ := imageRepresentation M V h.prepared.normalized
  have hBE : IsElementaryAbelian 2 B := by
    obtain ⟨C,hC,rfl⟩ := d.offender.1
    let := hC.1.2.1
    exact IsElementaryAbelian.of_injective (inclusion (show C ⊓ ChapterD.twoCoreIn H ≤ C from inf_le_left))
      (inclusion_injective _)
  let := hBE
  let : IsElementaryAbelian 2 A := actor_elementary _ (d.offender_le_sylow.trans h.maximal.1.2)
  have hmove : ¬ B ≤ centralizer (V : Set G) := by
    intro hb
    have he : ⁅V,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hb)
    have hc := d.plane_card
    rw [he,card_bot] at hc
    contradiction
  have hA : IsElementaryTwo A :=
    ⟨actor_nontrivial _ (d.offender_le_sylow.trans h.maximal.1.2) hmove,inferInstance⟩
  let W := subspaceCommutator ρ ⊤ A
  have hw : Module.finrank (ZMod 2) W = 2 := by
    have he := commutator_card_image h.prepared.normalized h.prepared.le_selected
      (d.offender_le_sylow.trans h.maximal.1.2)
    rw [d.plane_card] at he
    exact (Nat.pow_right_injective (by decide : 1 < 2)) he.symm
  have hr (a : A) (ha : (a : internalActionImage M V h.prepared.normalized) ≠ 1) :
      LinearMap.range (ρ a - LinearMap.id) = W := by
    have ho : orderOf (a : internalActionImage M V h.prepared.normalized) = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (a : internalActionImage M V h.prepared.normalized) a.property) ha
    obtain ⟨hea,_,hqa,_⟩ := involution_actor_rank_and_fixedCodim ρ a ho
    have hc := (h.quadratic_actor _ hea hqa).2
    have hle : LinearMap.range (ρ a - LinearMap.id) ≤ W := by
      rintro _ ⟨v,rfl⟩
      exact Submodule.subset_span ⟨a,a.property,v,Submodule.mem_top,rfl⟩
    exact Submodule.eq_of_le_of_finrank_eq hle (by
      rw [←fixedCodim_zpowers_eq_displacement_rank,hc,hw])
  refine ⟨hA,?_⟩
  intro a ha b hb v
  by_cases ha1 : a = 1
  · simp [ha1]
  have hm : ρ b v - v ∈ LinearMap.range (ρ a - LinearMap.id) := by
    rw [hr ⟨a,ha⟩ ha1]
    exact Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩
  obtain ⟨w,hw⟩ := hm
  change ρ a (ρ b v-v) = ρ b v-v
  rw [←hw]
  exact involution_fixes_displacement ρ
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha) w

/-- The literal plane stabilizer embeds in the original intersection action, whose order is prime to three. -/
theorem ResidualInput.plane_stabilizer_three_free
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    letI := h.prepared.elementary
    ∀ W : Submodule (ZMod 2) (Additive V), ambientSpace V W = ⁅V,B⁆ →
      Nat.Coprime 3 (Nat.card (subspaceStabilizer
        (imageRepresentation M V h.prepared.normalized) W)) := by
  let := h.prepared.elementary
  intro W he
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  have hle : subspaceStabilizer (imageRepresentation M V h.prepared.normalized) W ≤
      ((M ⊓ Mc).subgroupOf M).map f := by
    intro a ha
    obtain ⟨x,rfl⟩ := (actionHom M V h.prepared.normalized).rangeRestrict_surjective a
    have hn : (x : G) ∈ normalizer (ambientSpace V W : Set G) := by
      intro v
      constructor
      · rintro ⟨w,hw,rfl⟩
        refine ⟨(actionHom M V h.prepared.normalized) x w,?_,rfl⟩
        exact (ha (Additive.ofMul w)).2 hw
      · rintro ⟨w,hw,hwv⟩
        let u := (actionHom M V h.prepared.normalized) x⁻¹ w
        have hu : (u : G) = v := by
          change (x : G)⁻¹ * (w : G) * ((x : G)⁻¹)⁻¹ = v
          change (w : G) = (x : G) * v * (x : G)⁻¹ at hwv
          rw [hwv]
          group
        refine ⟨u,?_,hu⟩
        have hi := (subspaceStabilizer (imageRepresentation M V h.prepared.normalized) W).inv_mem ha
        exact (hi (Additive.ofMul w)).2 hw
    rw [he] at hn
    exact ⟨x,⟨x.property,d.plane_normalizer hn⟩,rfl⟩
  exact (intersection_image_three_free h d.intersection_centralizes_source).of_dvd_right
    (card_dvd_of_le hle)

/-- The centralizer of an offender generator stabilizes its fixed plane and has order prime to three. -/
theorem ResidualInput.actor_generator_centralizer_three_free
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (t : internalActionImage M V h.prepared.normalized)
    (ht : zpowers t = actor M V B h.prepared.normalized) :
    Nat.Coprime 3 (Nat.card (centralizer ({t} : Set _))) := by
  let := h.prepared.elementary
  let ρ := imageRepresentation M V h.prepared.normalized
  let W := fixedSpace ρ (zpowers t)
  have he : ambientSpace V W = ⁅V,B⁆ := by
    rw [show W = fixedSpace ρ (zpowers t) from rfl,ht,
      ambientSpace_fixed _ (d.offender_le_sylow.trans h.maximal.1.2)]
    exact ambient_fixed_eq_commutator h (d.offender_le_sylow.trans h.maximal.1.2)
      d.actor_quadratic_of_plane.1 d.actor_quadratic_of_plane.2
  have hle : centralizer ({t} : Set _) ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    intro a ha v hv
    rw [mem_fixedSpace_zpowers_iff] at hv ⊢
    rw [←Module.End.mul_apply,←map_mul,←mem_centralizer_singleton_iff.mp ha,
      map_mul,Module.End.mul_apply,hv]
  exact (d.plane_stabilizer_three_free W he).of_dvd_right (card_dvd_of_le hle)

private theorem ResidualInput.actor_generator
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    ∃ t : internalActionImage M V h.prepared.normalized,
      zpowers t = actor M V B h.prepared.normalized ∧ orderOf t = 2 := by
  let := h.prepared.elementary
  let A := actor M V B h.prepared.normalized
  have hAc : Nat.card A = 2 :=
    (quadratic_fixed_eq_moved h A d.actor_quadratic_of_plane.1 d.actor_quadratic_of_plane.2).1
  let : IsCyclic A := isCyclic_of_prime_card hAc
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  exact ⟨t,ht,by rw [←Nat.card_zpowers,ht,hAc]⟩

/-- The central cubic in the S₃ × C₃ row contradicts the actual plane stabilizer. -/
theorem ResidualInput.not_symmetric_three_cubic
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    ¬ Nonempty (internalActionImage M V h.prepared.normalized ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))) := by
  rintro ⟨e⟩
  obtain ⟨t,ht,_⟩ := d.actor_generator
  let c := e.symm (1,Multiplicative.ofAdd (1 : ZMod 3))
  have hc3 : c ^ 3 = 1 := by
    apply e.injective
    simp [c,←map_pow]
    decide
  have hcne : c ≠ 1 := by
    intro he
    have hh := congrArg e he
    simp [c] at hh
  have hc : c ∈ centralizer ({t} : Set _) := by
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simp only [map_mul,c,e.apply_symm_apply,Prod.mul_def,one_mul,mul_one]
    exact Prod.ext rfl (mul_comm _ _)
  have ho : orderOf (⟨c,hc⟩ : centralizer ({t} : Set _)) = 3 :=
    (Subgroup.orderOf_coe _).symm.trans (orderOf_eq_prime hc3 hcne)
  exact (Nat.prime_three.coprime_iff_not_dvd.mp (d.actor_generator_centralizer_three_free t ht))
    (ho ▸ orderOf_dvd_natCard (⟨c,hc⟩ : centralizer ({t} : Set _)))

/-- A normal cyclic fifteen forces a forbidden cubic in the offender centralizer. -/
theorem ResidualInput.not_fitting_fifteen
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    ¬ Nonempty (fittingSubgroup (internalActionImage M V h.prepared.normalized) ≃*
      Multiplicative (ZMod 15)) := by
  let := h.prepared.elementary
  intro he
  obtain ⟨t,ht,ho⟩ := d.actor_generator
  exact (Nat.prime_three.coprime_iff_not_dvd.mp (d.actor_generator_centralizer_three_free t ht))
    (SmallBinaryFiveOvergroup.three_dvd_involution_centralizer_of_normal_fifteen
      (imageRepresentation M V h.prepared.normalized) (imageRepresentation_injective _ _ _)
      h.finrank_eq_four _ he t (ho ▸ pow_orderOf_eq_one t)
      (by intro he; rw [he,orderOf_one] at ho; contradiction))

/-- The original residual input suffices to recognize all surviving chosen action models. -/
theorem ResidualInput.restricted_models_or_omega
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    letI := h.prepared.elementary
    RestrictedModels h ∨ SourceCases.Omega (imageRepresentation M V h.prepared.normalized) := by
  let := h.prepared.elementary
  let D := internalActionImage M V h.prepared.normalized
  let ρ := imageRepresentation M V h.prepared.normalized
  let K := Jhat ρ
  let : K.Normal := Jhat_normal ρ
  rcases h.action_alternatives with h3 | ⟨_,h18⟩ | hω | ⟨hK,_,hF⟩
  · exact Or.inl (Or.inl h3)
  · exact (d.not_symmetric_three_cubic h18).elim
  · exact Or.inr hω
  · refine Or.inl (Or.inr ⟨hK,?_⟩)
    have hcK : Nat.card K = 10 := (Nat.card_congr hK.some.toEquiv).trans DihedralGroup.nat_card
    have hF : Nat.card (fittingSubgroup D) = 5 := by
      rcases h.small with ⟨l,p,m,hpm,hd⟩ | hω
      · have hm : m = 2 := by
          have hh := hd.dimension
          rw [h.finrank_eq_four] at hh
          omega
        subst m
        rcases (ChapterD.CyclicSource.primeDimensionOptions_iff p 2).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩
        · have hc : Nat.card K = 6 := (Nat.card_congr hd.dihedral.some.toEquiv).trans DihedralGroup.nat_card
          omega
        · let P := l.kernel.map K.subtype
          have hp : ChapterD.CyclicSource.PrimeDimensionOptions 5 2 :=
            (ChapterD.CyclicSource.primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
          have hmks := hd.ambient_marks K hp
          let : P.Normal := hmks.2.2.2.1
          rcases SmallBinaryFiveOvergroup.fitting_alternatives ρ
              (imageRepresentation_injective _ _ _) h.finrank_eq_four P hmks.2.2.1 with he | he
          · exact he ▸ hmks.2.2.1
          · exact (d.not_fitting_fifteen he).elim
      · obtain ⟨e⟩ := hω.2.2.2.1
        have hc : Nat.card D = 36 := by
          rw [Nat.card_congr e.toEquiv]
          norm_num [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
        change Nat.card (Jhat ρ) = 10 at hcK
        rw [hω.1,card_top] at hcK
        have hbad : (36 : ℕ) = 10 := hc.symm.trans hcK
        contradiction
    have htwo : 2 ∣ Nat.card D := by
      have hd := K.card_subgroup_dvd_card
      rw [hcK] at hd
      exact (by decide : 2 ∣ 10).trans hd
    exact small_models_of_fitting_card_five
      (source_chosen_action_isSolvable h.ambient T h.empty h.maximal V
        h.prepared.normalized h.prepared.le_local) hF htwo

/-- The actual partner is C_G(Ω₁Z(T)), without assuming the full partner residual identity. -/
theorem ResidualInput.partner_eq_centralizer
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    Mc = centralizer (centralInvolutions T : Set G) := by
  let := h.prepared.elementary
  rcases d.restricted_models_or_omega with hr | ho
  · exact (centralizers_of_restricted_models h d.full hr).1
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let I := ((M ⊓ Mc).subgroupOf M).map f
  let P := (T.subtype h.maximal.1.2).mapSurjective
    (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  have hD : Nat.card (internalActionImage M V h.prepared.normalized) = 36 := by
    obtain ⟨e⟩ := ho.2.2.2.1
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hI : IsPGroup 2 I := by
    have hc := intersection_image_three_free h d.intersection_centralizes_source
    change Nat.Coprime 3 (Nat.card I) at hc
    have hd : Nat.card I ∣ 4 * 9 := by
      have hd := I.card_subgroup_dvd_card
      change Nat.card I ∣ Nat.card (internalActionImage M V h.prepared.normalized) at hd
      rwa [hD] at hd
    exact IsPGroup.of_card_dvd_pow (p := 2) (n := 2)
      ((hc.symm.pow_right 2).dvd_mul_right.mp hd)
  have heI : I = (P : Subgroup _) := P.is_maximal' hI (by
    apply map_mono
    intro x hx
    exact ⟨h.maximal.1.2 hx,(partner_mem_overgroups h).2 hx⟩)
  have hZV : centralInvolutions T ≤ V := by rw [d.full]; exact le_conjugateSpanBy _ _
  have hi : M ⊓ Mc ≤ centralizer (centralInvolutions T : Set G) := by
    intro x hx
    have him : f ⟨x,hx.1⟩ ∈ (P : Subgroup _) := heI ▸ mem_map_of_mem f hx
    obtain ⟨t,ht,he⟩ := him
    have hk : t⁻¹ * (⟨x,hx.1⟩ : M) ∈ (actionHom M V h.prepared.normalized).ker := by
      rw [←MonoidHom.ker_rangeRestrict]
      change f (t⁻¹ * ⟨x,hx.1⟩) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    rw [actionHom_ker] at hk
    have htZ : (t : G) ∈ centralizer (centralInvolutions T : Set G) :=
      (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)) ht
    have hh := (centralizer (centralInvolutions T : Set G)).mul_mem htZ
      (centralizer_le hZV hk)
    change (t : G) * ((t : G)⁻¹ * x) ∈ centralizer (centralInvolutions T : Set G) at hh
    simpa only [mul_inv_cancel_left] using hh
  have hC := centralizer_le_partner T h.partner
  have hord := source_ordering_of_centralizing_orderingMaximal h.ambient T h.empty
    h.maximal h.centralizing Mc (partner_mem_overgroups h)
  apply le_antisymm ?_ hC
  intro x hx
  obtain ⟨a,ha,c,hc,rfl⟩ := hord x hx
  exact mul_mem (hi ⟨ha.2,ha.1⟩) (centralizer_le (le_conjugateSpanBy _ _) hc.2)

/-- The literal prime-complement residual centralizes the original Sylow-central seed. -/
theorem ResidualInput.threePrimeResidual_centralizes_source
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    threePrimeResidual Mc ≤ centralizer (centralInvolutions T : Set G) :=
  (map_subtype_le _).trans d.partner_eq_centralizer.le

/-- Actual consumer: every three-subgroup normalizing the distinguished plane fixes it. -/
theorem ResidualInput.threeSubgroup_plane_centralizes
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    {X : Subgroup G} (hX : IsPGroup 3 X)
    (hXN : X ≤ normalizer (⁅V,B⁆ : Subgroup G)) :
    X ≤ centralizer (⁅V,B⁆ : Subgroup G) :=
  h.threeSubgroup_plane_normalizer_centralizes d.plane_le d.plane_card
    (d.outside.1.1.2.trans d.plane_normalized) d.plane_normalizer
    d.threePrimeResidual_centralizes_source hX hXN

/-- The original Sylow-central seed lies in the literal distinguished commutator plane. -/
theorem ResidualInput.seed_le_plane
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    centralInvolutions T ≤ ⁅V,B⁆ :=
  seed_le_commutator h d.full d.offender_le_sylow
    d.actor_quadratic_of_plane.1 d.actor_quadratic_of_plane.2

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
