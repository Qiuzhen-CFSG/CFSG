module
public import Stellmacher.SectionTen.TenOneDihedralActionSupportData
public import Stellmacher.SectionTen.TenOneDihedralCoatomEscape
public import Stellmacher.SectionTen.TenOneDihedralCoatomSupport
public import Theory.GroupAction.ActorSubtypeCommutator
public import Theory.GroupAction.CardFourCommonDisplacementActors
public import Theory.GroupAction.InvertedOddSupportDisplacement
public import Theory.GroupAction.QuotientDisplacementCard

/-!
# Comparing the prescribed actor with its middle-core conjugates

For the actual Section Ten terminal quotient action, consider the prescribed
actor whose displacement has order four and contains the first center.
Under the no-transvection hypothesis, each middle-core conjugate acts in
exactly the same way, unless the extracted odd support has order four and
contains the image of that center. The supplied quotient normality and
elementary-module instances and the exact action kernel are retained.

Coatom escape and the raw factorization put the difference of the two actors
in the extracted coatom. It fixes the odd support and has displacement in
the complementary fixed subgroup. Odd inversion supplies a common nontrivial
displacement inside the support, whose order squares to the support order.
Conjugation preserves both displacement planes and their common first-center
line. The finite common-displacement comparison then gives the alternatives;
the difference cannot be a transvection by the actual source hypothesis.

Source: Stellmacher (10.1), printed p.63, the paragraph before (13). The
separate first-support exclusion removes the remaining alternative before
actor-line normality is asserted.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionThree
open scoped Pointwise IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem quotient_actor_card_iff
    (P V Z : Subgroup G) (hPV : P ≤ Subgroup.normalizer (V : Set G))
    (hZV : Z ≤ V) [(Z.subgroupOf V).Normal]
    (action : P →* MulAut (V ⧸ Z.subgroupOf V))
    (hformula : ∀ mover : P, ∀ point : V,
      action mover (QuotientGroup.mk' (Z.subgroupOf V) point) =
      QuotientGroup.mk' (Z.subgroupOf V)
        ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hPV mover.property) point).mp point.property⟩)
    (actor : P) (n : ℕ) :
    Nat.card (commutatorAction (Subgroup.zpowers (action actor)) (V ⧸ Z.subgroupOf V)) = n ↔
      QuotientCardEq (⁅V, Subgroup.zpowers (actor : G)⁆ ⊔ Z) Z n := by
  have hnative : (Subgroup.zpowers (actor : G)).subgroupOf P = Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr actor.property),
      MonoidHom.map_zpowers]
    rfl
  have hh := Subgroup.quotient_conjugation_commutatorAction_card_iff P V Z
    (Subgroup.zpowers (actor : G)) hPV (Subgroup.zpowers_le.mpr actor.property)
    hZV action hformula n
  rwa [hnative, MonoidHom.map_zpowers] at hh

public theorem ten_one_dihedral_actor_comparison
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (data : TenOneDihedralConfigurationData ctx middle (actor : G) hactor)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [_hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a',
      ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
      QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
        ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp
            (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
              point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))

    (hno : ∀ element : G, element ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      element ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers element⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcard : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 4)
    (hselected : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆)
    (mover : GAt ctx.Γ ctx.criticalPath.a') (hmover : (mover : G) ∈ QAt ctx.Γ middle) :
    let V := VAt ctx.Γ ctx.criticalPath.a'
    let Z := ZAt ctx.Γ ctx.criticalPath.a'
    let W := V ⧸ Z.subgroupOf V
    let U := commutatorAction
      ((data.raw.F₀.subgroupOf (GAt ctx.Γ ctx.criticalPath.a')).map action) W
    let L := ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf V).map
      (QuotientGroup.mk' (Z.subgroupOf V))
    action actor = action (mover * actor * mover⁻¹) ∨ (Nat.card U = 4 ∧ L ≤ U) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let A := VAt Γ cp.firstStep
  let Zfirst := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let π : V →* W := QuotientGroup.mk' (Z.subgroupOf V)
  let R := (data.raw.F₀.subgroupOf P).map action
  let U := commutatorAction R W
  let C := FixedPoints.subgroup R W
  let L := (Zfirst.subgroupOf V).map π
  let other : P := mover * actor * mover⁻¹
  let delta : P := actor⁻¹ * other
  have hshort : 1 < cp.length := by have := ctx.critical_length; change 1 < ctx.criticalPath.length; omega
  let _ : IsElementaryAbelian 2 A :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hmfirst : (mover : G) ∈ GAt Γ cp.firstStep :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core middle cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr hfirst) default).2.2 hmover
  have hother : (other : G) ∈ A :=
    (Subgroup.mem_normalizer_iff.mp (stabilizer_le_normalizer_v Γ cp.firstStep hmfirst)
      (actor : G)).mp hactor
  have hout : (other : G) ∉ data.raw.A₀ :=
    ten_one_dihedral_coatom_escape ctx middle hpath actor hactor data hselected mover hmover
  have hactorNe : (actor : G) ≠ 1 := by
    intro heq
    have hP : actor = 1 := Subtype.ext heq
    have hh := data.raw.reflection_involution.1
    apply hh
    change QuotientGroup.mk' (pCore 2 P) actor = 1
    rw [hP, map_one]
  have horder : orderOf (actor : G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (actor : G) hactor) hactorNe
  have hdelta : (delta : G) ∈ data.raw.A₀ := by
    have hfactor : (other : G) ∈ (Subgroup.zpowers (actor : G) : Set G) *
        (data.raw.A₀ : Set G) := data.raw.A_factor ▸ hother
    obtain ⟨power, hpower, coactor, hcoactor, heq⟩ := hfactor
    change power ∈ Subgroup.zpowers (actor : G) at hpower
    rw [mem_zpowers_iff_mem_range_orderOf, horder] at hpower
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hpower
    have hn : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · simp only [pow_zero, one_mul] at heq
      exact False.elim (hout (heq ▸ hcoactor))
    · simp only [pow_one] at heq
      change (actor : G)⁻¹ * (other : G) ∈ data.raw.A₀
      rw [← heq, inv_mul_cancel_left]
      exact hcoactor
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hZmV : ZAt Γ middle ≤ V := nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hterminal)
  have hsplit := (sectionTenOpeningData ctx middle hpath).center_direct_product
  have hZV : Z ≤ V := (show Z ≤ ZAt Γ middle by rw [hsplit.1]; exact le_sup_right).trans hZmV
  have hZfirstV : Zfirst ≤ V :=
    (show Zfirst ≤ ZAt Γ middle by rw [hsplit.1]; exact le_sup_left).trans hZmV
  have hLcard : Nat.card L = 2 := by
    change Nat.card ((Zfirst.subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V))) = 2
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk',
      Subgroup.relIndex_subgroupOf hZfirstV, ← Subgroup.inf_relIndex_right,
      hsplit.2.1.symm.eq_bot, Subgroup.relIndex_bot_left]
    exact (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
      hshort cp.firstStep ⟨1, Γ.act_one _⟩).1
  have hVmap : V.map (MulAut.conj (mover : G)).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPV mover.property)
  have hZmap : Z.map (MulAut.conj (mover : G)).toMonoidHom = Z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (stabilizer_le_normalizer_z Γ cp.a' mover.property)
  have hZfirstMap : Zfirst.map (MulAut.conj (mover : G)).toMonoidHom = Zfirst :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (stabilizer_le_normalizer_z Γ cp.firstStep hmfirst)
  have hdisplacementMap : (⁅V, Subgroup.zpowers (actor : G)⁆ ⊔ Z).map
      (MulAut.conj (mover : G)).toMonoidHom = ⁅V, Subgroup.zpowers (other : G)⁆ ⊔ Z := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, hVmap, hZmap, MonoidHom.map_zpowers]
    rfl
  have hotherCard : QuotientCardEq (⁅V, Subgroup.zpowers (other : G)⁆ ⊔ Z) Z 4 := by
    change Nat.card (⁅V, Subgroup.zpowers (other : G)⁆ ⊔ Z : Subgroup G) = 4 * Nat.card Z
    rw [← hdisplacementMap, Subgroup.card_map_of_injective (MulAut.conj (mover : G)).injective]
    exact hcard
  have hotherSelected : Zfirst ≤ ⁅V, Subgroup.zpowers (other : G)⁆ := by
    have hh := Subgroup.map_mono (f := (MulAut.conj (mover : G)).toMonoidHom) hselected
    rwa [hZfirstMap, Subgroup.map_commutator, hVmap, MonoidHom.map_zpowers] at hh
  have himage (element : P) : commutatorAction (Subgroup.zpowers (action element)) W =
      (⁅V, Subgroup.zpowers (element : G)⁆.subgroupOf V).map π := by
    have hnative : (Subgroup.zpowers (element : G)).subgroupOf P = Subgroup.zpowers element := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr element.property),
        MonoidHom.map_zpowers]
      rfl
    have hh := Subgroup.quotient_conjugation_commutatorAction_eq_image P V Z
      (Subgroup.zpowers (element : G)) hPV (Subgroup.zpowers_le.mpr element.property) hN action hformula
    rwa [hnative, MonoidHom.map_zpowers] at hh
  have hLfirst : L ≤ commutatorAction (Subgroup.zpowers (action actor)) W := by
    rw [himage]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono V hselected)
  have hLsecond : L ≤ commutatorAction (Subgroup.zpowers (action other)) W := by
    rw [himage]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono V hotherSelected)
  obtain ⟨hodd, hRne, hinvolution, hinverts, hcoatom⟩ :=
    ten_one_dihedral_action_support_data ctx middle actor hactor data action hformula hkernel
  obtain ⟨hUC, D, hD, hDU, hDfirst, hsquare, hDgen⟩ :=
    inverted_odd_support_displacement_packet R hodd hRne (action actor) hinvolution hinverts
  have hfix : ∀ point ∈ U, action delta point = point :=
    ten_one_dihedral_coatom_fixes_support ctx middle actor hactor data action hformula hkernel delta hdelta
  have hsame (point : W) (hpoint : point ∈ U) : action other point = action actor point := by
    have heq : other = actor * delta := by dsimp only [delta]; group
    rw [heq, map_mul, MulAut.mul_apply, hfix point hpoint]
  have hDsecond : D ≤ commutatorAction (Subgroup.zpowers (action other)) W := by
    apply hDgen
    intro point hpoint
    rw [← hsame point hpoint, commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨action other, Subgroup.mem_zpowers _⟩, point, rfl⟩
  have hdeltaImage : action actor⁻¹ * action other = action delta := by
    rw [← map_mul]
  have hdeltaC : commutatorAction (Subgroup.zpowers ((action actor)⁻¹ * action other)) W ≤ C := by
    rw [← map_inv, hdeltaImage]
    exact hcoatom delta hdelta
  have hdeltaNo : Nat.card (commutatorAction
      (Subgroup.zpowers ((action actor)⁻¹ * action other)) W) ≠ 2 := by
    rw [← map_inv, hdeltaImage]
    intro htwo
    have hdeltaA : (delta : G) ∈ A := data.raw.A₀_le hdelta
    have hdeltaOut : (delta : G) ∉ QAt Γ cp.a' := by
      intro hQ
      have hcore : (QAt Γ cp.a').subgroupOf P = pCore 2 P := by
        change (Γ.twoCoreAt _).subgroupOf P = _
        rw [Γ.twoCoreAt_def]
        exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
      have hk : delta ∈ action.ker := by rw [hkernel, ← hcore]; exact hQ
      have hd : action delta = 1 := MonoidHom.mem_ker.mp hk
      have hbot : commutatorAction (Subgroup.zpowers (action delta)) W = ⊥ := by
        rw [hd, Subgroup.zpowers_one_eq_bot, commutatorAction_eq_closure]
        apply le_bot_iff.mp
        rw [Subgroup.closure_le]
        rintro _ ⟨element, point, rfl⟩
        have he : (element : MulAut W) = 1 := element.property
        change point⁻¹ * (element : MulAut W) point ∈ (⊥ : Subgroup W)
        simp only [he, MulAut.one_apply, inv_mul_cancel, Subgroup.one_mem]
      rw [hbot, Subgroup.card_bot] at htwo
      omega
    exact hno delta hdeltaA hdeltaOut ((quotient_actor_card_iff P V Z hPV hZV
      action hformula delta 2).mp htwo)
  exact eq_or_card_four_support_of_common_displacement (action actor) (action other)
    U C D L ((quotient_actor_card_iff P V Z hPV hZV action hformula actor 4).mpr hcard)
    ((quotient_actor_card_iff P V Z hPV hZV action hformula other 4).mpr hotherCard)
    hD hDU hDfirst hDsecond hLcard hLfirst hLsecond hsquare hUC hdeltaC hdeltaNo

end Stellmacher.SectionTen
