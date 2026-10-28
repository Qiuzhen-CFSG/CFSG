module

public import Stellmacher.Recognition.LargeTerminalDerivedIntersection
public import Theory.GroupAction.FiveFourOrbitFixed
public import Theory.GroupAction.FiveFourInvolutionFixed

/-!
# Fusion of the derived residual into the common elementary eight

The first module modulo its center has order sixteen and a faithful action
of the local Frobenius group of order twenty. An involution from the terminal
module escapes the first core. Its image fixes four quotient points, whose
lift is exactly the common module intersection: that lift has order eight
and contains the intersection of order eight.

Every orbit of the Frobenius group meets this involution's fixed subgroup.
Lifting the conjugator therefore moves every first-module element into the
common intersection. The residual derived-subgroup identity transports this
to the original ambient group. Source: Thompson VI, printed pp.627--630,
the three orbits in the subgroup denoted F there.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
open scoped IsMulCommutative
universe u

/-- Every element of the actual derived residual fuses into the common
intersection. No simplicity, Sylow order, or order-five fixed-point premises
are required beyond the retained large terminal context. -/
public theorem LargeTerminalContext.derived_fusion_into_intersection
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (t : G)
    (ht : t ∈ DerivedAmbient ctx.firstResidual) :
    ∃ x : G, x ∈ ctx.derivedIntersection ∧ IsConj t x := by
  classical
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let tenCtx := ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three
  let Γ := tenCtx.Γ
  let cp := tenCtx.criticalPath
  have hlength : cp.length = 3 := ctx.length_three
  have hb : 1 < cp.length := by omega
  let middle := cp.path ⟨2, by omega⟩
  have hpath : IsCriticalPathOffset Γ cp 2 middle := ⟨⟨2, by omega⟩, rfl, rfl⟩
  let P := GAt Γ cp.firstStep
  let Q := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let A := VAt Γ cp.a'
  let I := V ⊓ A
  obtain ⟨_, hfirst, hterminal, hne⟩ := sectionTenOpeningGeometry tenCtx middle hpath
  let _ : IsElementaryAbelian 2 V :=
    ((lemma_seven_five tenCtx.sectionSeven Γ cp ctx.commuting).longer_case hb).1
  obtain ⟨mover, hmove⟩ := (lemma_seven_one tenCtx.sectionSeven Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
  change Γ.act (mover : K) cp.firstStep = cp.a' at hmove
  have hmap : V.map (MulAut.conj (mover : K)⁻¹).toMonoidHom = A := by
    change (v Γ cp.firstStep).map _ = v Γ cp.a'
    rw [← v_act, hmove]
  let _ : IsElementaryAbelian 2 A := by
    rw [← hmap]
    exact IsElementaryAbelian.map _
  have hVcard : Nat.card V = 32 := by
    have hc := (ten_one_large_terminal_structure tenCtx middle hpath ctx.noTransvections).2.1
    change Nat.card A = 32 at hc
    rw [← hmap, card_map_of_injective (MulAut.conj (mover : K)⁻¹).injective] at hc
    exact hc
  have hIcard : Nat.card I = 8 :=
    (ten_one_large_terminal_structure tenCtx middle hpath ctx.noTransvections).2.2
  have hZI : Z ≤ I := by
    have hmid : ZAt Γ middle ≤ I := le_inf
      (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hfirst))
      (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hterminal))
    have hsplit := (sectionTenOpeningData tenCtx middle hpath).center_direct_product.1
    exact (show Z ≤ ZAt Γ middle from hsplit ▸ le_sup_left).trans hmid
  have hZV : Z ≤ V := hZI.trans inf_le_left
  obtain ⟨hN, hW, action, hformula, hkernel⟩ := nine_next_quotient_conjugation_action
    tenCtx.toAmbientSectionNineContext hb cp.firstStep ⟨1, Γ.act_one _⟩
  let _ := hN
  let _ : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V) := hW
  let W := V ⧸ Z.subgroupOf V
  let q := QuotientGroup.mk' (Z.subgroupOf V)
  have hformula' (p : P) (v : V) : action p (q v) = q
      ⟨(p : K) * (v : K) * (p : K)⁻¹,
        (mem_normalizer_iff.mp (stabilizer_le_normalizer_v Γ cp.firstStep p.property) v).mp
          v.property⟩ := hformula p v
  have hZcard : Nat.card Z = 2 := (nine_next_center_commutator_and_kernel
    tenCtx.toAmbientSectionNineContext hb cp.firstStep ⟨1, Γ.act_one _⟩).1
  have hWcard : Nat.card W = 16 := by
    have hc := card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv, hZcard, hVcard] at hc
    change 32 = Nat.card W * 2 at hc
    omega
  obtain ⟨φ, hφ, π, hπsurj, hπker⟩ :=
    ten_one_large_first_frobenius tenCtx middle hpath ctx.noTransvections
  have hcore : Q.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  have hker : π.ker = action.ker := by rw [hπker, hkernel]; exact hcore
  let lift : (P ⧸ π.ker) →* MulAut W := QuotientGroup.lift π.ker action hker.le
  have hlift : Function.Injective lift :=
    (QuotientGroup.injective_lift_iff _ _ _).mpr hker
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπsurj
  let f := lift.comp e.symm.toMonoidHom
  have hf : Function.Injective f := hlift.comp e.symm.injective
  have hcompat (p : P) : f (π p) = action p := by
    change lift (e.symm (π p)) = action p
    have he : e (QuotientGroup.mk' π.ker p) = π p := rfl
    rw [← he, e.symm_apply_apply]
    rfl
  have hAP : A ≤ P := by
    have hAmid : A ≤ QAt Γ middle :=
      (show A ≤ GeneratedNeighborhoodV Γ middle from
        le_sSup ⟨_, (mem_neighborhood_iff_adjacent Γ).mpr hterminal, rfl⟩).trans
          (nine_seven_neighborhood_le_own_core tenCtx.toLocalContext.toSectionNineLocalContext
            (by change 2 < cp.length; omega) middle)
    exact hAmid.trans ((lemma_seven_three tenCtx.sectionSeven Γ).sylow_and_core
      middle cp.firstStep ((mem_neighborhood_iff_adjacent Γ).mpr hfirst) default).2.2
  have hescape : ¬ A ≤ Q :=
    ten_one_neighbor_module_not_le_core tenCtx middle hpath hterminal hfirst hne.symm
  obtain ⟨a, haA, haQ⟩ := SetLike.not_le_iff_exists.mp hescape
  let aP : P := ⟨a, hAP haA⟩
  let u := π aP
  have hu2 : u ^ 2 = 1 := by
    change (π aP) ^ 2 = 1
    rw [← map_pow, show aP ^ 2 = 1 from
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a haA), map_one]
  have hu1 : u ≠ 1 := by
    intro h
    have hm : aP ∈ π.ker := h
    rw [hπker] at hm
    exact haQ hm
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  let F := FixedPoints.subgroup (zpowers (f u)) W
  have hFcard : Nat.card F = 4 :=
    (Theory.GroupAction.five_four_involution_fixed_displacement hWcard φ hφ f hf u hu).1
  let L := (F.comap q).map V.subtype
  have hLcard : Nat.card L = 8 := by
    have hc := (lift_support_basic V Z hZV F).2.2.1
    change Nat.card L = Nat.card F * Nat.card Z at hc
    rw [hFcard, hZcard] at hc
    exact hc
  have hIL : I ≤ L := by
    intro x hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    apply (MulAut.mem_fixed_zpowers_iff (f u) (q ⟨x, hx.1⟩)).mpr
    rw [show f u = action aP from hcompat aP, hformula']
    apply congrArg q
    apply Subtype.ext
    change a * x * a⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr (setLike_mul_comm (s := A) haA hx.2)
  have hLI : L = I := (eq_of_le_of_card_ge hIL (by rw [hLcard, hIcard])).symm
  rw [ctx.first_residual_structure.2.2.1] at ht
  obtain ⟨v, hv, rfl⟩ := ht
  obtain ⟨g, hg⟩ := Theory.GroupAction.five_four_orbit_meets_involution_fixed
    hWcard φ f hf u hu (q ⟨v, hv⟩)
  obtain ⟨p, rfl⟩ := hπsurj g
  rw [hcompat p, hformula'] at hg
  let w : V := ⟨(p : K) * v * (p : K)⁻¹,
    (mem_normalizer_iff.mp (stabilizer_le_normalizer_v Γ cp.firstStep p.property) v).mp hv⟩
  have hwF : q w ∈ F := (MulAut.mem_fixed_zpowers_iff (f u) (q w)).mpr hg
  have hwI : (w : K) ∈ I := hLI ▸ (show (w : K) ∈ L from ⟨w, hwF, rfl⟩)
  refine ⟨K.subtype w, mem_map_of_mem K.subtype hwI, ?_⟩
  exact isConj_iff.mpr ⟨((p : K) : G), rfl⟩

end Stellmacher.Recognition
