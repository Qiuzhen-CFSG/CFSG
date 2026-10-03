module
public import Stellmacher.SectionNine.DistanceOneVstarResidualPreliminaries
public import Theory.GroupTheory.QuaternionFixedEight
public import Theory.GroupTheory.InnerRestrictionsCommutingSup

/-!
# The initial elementary center swaps the quaternion factors of Vstar

For the actual distance-one configuration, some element of the initial vertex
center lies in the terminal stabilizer and interchanges the two intrinsic
quaternion factors of Vstar. The faithful and local conclusions remain explicit
inputs; no independent fixedfree-action hypothesis is imposed.

The seed Z_a∩Q_d has order eight: the terminal core has index two in the edge
Sylow, Z_a has order sixteen, and criticality gives Z_a≰Q_d. It is elementary
and centralized by Z_a. An elementary subgroup of order eight in Q8∘Q8 projects
onto either quaternion factor modulo the common center. Indeed its intersection
with the other factor has order at most two, so their product has order32 and
is the whole central product.

Choose an element of Z_a outside Q_d. If it preserved both factors, fixing the
seed would make its two restrictions central automorphisms, hence inner. Combine
the two inner conjugators into w∈Vstar. The original actor differs from w by an
element of the terminal centralizer of Vstar, which the preliminary module puts
inside Q_d. This contradicts the choice of actor. Intrinsic-factor uniqueness
therefore forces the transposition.

Source: the residual-action calculation of Stellmacher (9.1), Journal of
Algebra190 (1997), p.48. The proof uses the actual seed and criticality to
exclude the factor-preserving alternative; the abstract central-product model
alone supplies no such exclusion. The shared fixed-eight inner-restriction
calculation is imported from `Theory.GroupTheory.QuaternionFixedEight`.
-/

namespace Stellmacher.SectionNine
open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven

/-- The actual seed is elementary of order eight, and criticality supplies an
element of the initial center outside the terminal core that fixes it. -/
public theorem distance_one_seed_data
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx)
    (hlocal : DistanceOneLocalConclusion ctx) :
    let seed := ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a'
    Nat.card seed = 8 ∧ (∀ x ∈ seed, x ^ 2 = 1) ∧
      ∃ actor : G, actor ∈ ZAt ctx.Γ ctx.criticalPath.a ∧
        actor ∉ QAt ctx.Γ ctx.criticalPath.a' ∧
        ∀ x ∈ seed, Commute actor x := by
  let Za := ZAt ctx.Γ ctx.criticalPath.a
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  have hZaT : Za ≤ T := by
    change ZAt ctx.Γ ctx.criticalPath.a ≤ T
    rw [← hlocal.2.2.2.1]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  have hne : ¬ Za ≤ Q := ctx.criticalPath.critical.2
  have hindex : Q.relIndex Za = 2 := by
    have hupper := Subgroup.relIndex_le_of_le_right hZaT
      (show Q.relIndex T ≠ 0 by rw [distance_one_terminal_core_index_in_sylow ctx hlength hlocal]; decide)
    have hnotone : Q.relIndex Za ≠ 1 := fun hh => hne (Subgroup.relIndex_eq_one.mp hh)
    have hpos : 0 < Q.relIndex Za := Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := Q.subgroupOf Za))
    rw [distance_one_terminal_core_index_in_sylow ctx hlength hlocal] at hupper
    omega
  have hcard : Nat.card (Za ⊓ Q : Subgroup G) = 8 := by
    have hc := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (Za ⊓ Q) Za bot_le inf_le_left
    simp only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_left] at hc
    rw [hindex, hfaithful.1] at hc
    omega
  have hneighbor : ctx.criticalPath.a' ∈
      CosetGraphContext.neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [CosetGraphContext.neighborhood, ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hlength)
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  obtain ⟨actor, ha, hq⟩ := SetLike.not_le_iff_exists.mp hne
  refine ⟨hcard, ?_, actor, ha, hq, ?_⟩
  · intro x hx
    exact elemPow_eq_one_of_isElementaryAbelian x hx.1
  · intro x hx
    exact setLike_mul_comm (s := ZAt ctx.Γ ctx.criticalPath.a) ha hx.1


private theorem not_preserves_factors_of_outside_core
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hlocal : DistanceOneLocalConclusion ctx)
    (left right seed : Subgroup G)
    (hleft : Nonempty (left ≃* QuaternionGroup 2))
    (hright : Nonempty (right ≃* QuaternionGroup 2))
    (hjoin : conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') = left ⊔ right)
    (hcomm : ∀ b ∈ left, ∀ c ∈ right, b * c = c * b)
    (hseed : seed ≤ left ⊔ right) (hseedcard : Nat.card seed = 8)
    (hseedexp : ∀ x ∈ seed, x ^ 2 = 1)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.a')
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hfix : ∀ x ∈ seed, Commute actor x) :
    ¬ (actor ∈ Subgroup.normalizer (left : Set G) ∧
      actor ∈ Subgroup.normalizer (right : Set G)) := by
  rintro ⟨hln, hrn⟩
  have hVcard : Nat.card (left ⊔ right : Subgroup G) = 32 := by
    rw [← hjoin]
    exact distance_one_vstar_card ctx hlocal
  obtain ⟨b, hb, hactB⟩ := Subgroup.factor_inner_of_fixed_eight left right seed hleft hright
    hcomm hVcard hseed hseedcard hseedexp actor hln hrn hfix
  obtain ⟨c, hc, hactC⟩ := Subgroup.factor_inner_of_fixed_eight right left seed hright hleft
    (fun c hc b hb => (hcomm b hb c hc).symm) (by simpa [sup_comm] using hVcard)
    (by simpa [sup_comm] using hseed) hseedcard hseedexp actor hrn hln hfix
  obtain ⟨w, hwV, hkV⟩ :=
    Subgroup.exists_mul_inv_mem_centralizer_of_inner_restrictions left right hcomm actor
      ⟨b, hb, hactB⟩ ⟨c, hc, hactC⟩
  let k := w⁻¹ * actor
  have hcont := distance_one_vstar_containments ctx hlength
  have hwcore : w ∈ QAt ctx.Γ ctx.criticalPath.a' := hcont.2.1 (hjoin.symm ▸ hwV)
  have hwterm : w ∈ GAt ctx.Γ ctx.criticalPath.a' := hcont.1.1 (hjoin.symm ▸ hwV)
  have hkterm : k ∈ GAt ctx.Γ ctx.criticalPath.a' :=
    (GAt ctx.Γ ctx.criticalPath.a').mul_mem
      ((GAt ctx.Γ ctx.criticalPath.a').inv_mem hwterm) hactor
  have hkcore := distance_one_vstar_centralizer_le_core ctx hlength hlocal ⟨hkterm, hjoin.symm ▸ hkV⟩
  apply hout
  have hm := (QAt ctx.Γ ctx.criticalPath.a').mul_mem hwcore hkcore
  simpa [k] using hm


public theorem distance_one_vstar_factor_swap
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx)
    (hlocal : DistanceOneLocalConclusion ctx) :
    let V := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    ∃ left right : Subgroup G,
      IsModel left Q8 ∧ IsModel right Q8 ∧ V = left ⊔ right ∧
      Nat.card (left ⊓ right : Subgroup G) = 2 ∧
      (∀ b ∈ left, ∀ c ∈ right, b * c = c * b) ∧
      ∃ actor : G, actor ∈ ZAt ctx.Γ ctx.criticalPath.a ∧
        actor ∈ GAt ctx.Γ ctx.criticalPath.a' ∧
        left.map (MulAut.conj actor).toMonoidHom = right ∧
        right.map (MulAut.conj actor).toMonoidHom = left := by
  obtain ⟨left, right, hleft, hright, hjoin, hinter, hcomm, _⟩ := hlocal.2.2.2.2
  refine ⟨left, right, hleft, hright, hjoin, hinter, hcomm, ?_⟩
  obtain ⟨hseedcard, hseedexp, actor, ha, hout, hfix⟩ :=
    distance_one_seed_data ctx hlength hfaithful hlocal
  let seed := ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a'
  have hseed : seed ≤ left ⊔ right := by
    rw [← hjoin]
    intro x hx
    exact Subgroup.subset_closure ⟨1, ⟨x, hx⟩, by simp⟩
  have haT : actor ∈ T := by
    apply (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1
    change actor ∈ QAt ctx.Γ ctx.criticalPath.a
    rw [hlocal.2.2.2.1]
    exact ha
  have haTerm : actor ∈ GAt ctx.Γ ctx.criticalPath.a' := by
    have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
      rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
      congr 1
      exact Fin.ext hlength
    rw [hend]
    exact (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2.1 haT
  have hnot := not_preserves_factors_of_outside_core ctx hlength hlocal left right seed
    hleft hright hjoin hcomm hseed hseedcard hseedexp actor haTerm hout hfix
  have hn := (distance_one_vstar_containments ctx hlength).1
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hn.1).mp hn.2 haTerm
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm
  rw [hjoin] at hmap
  let e : G ≃* G := MulAut.conj actor
  have himage (D : Subgroup G) (hD : Nonempty (D ≃* QuaternionGroup 2))
      (hle : D ≤ left ⊔ right) : D.map e.toMonoidHom = left ∨ D.map e.toMonoidHom = right := by
    obtain ⟨model⟩ := hD
    apply Subgroup.quaternion_subgroup_eq_factor left right _ hleft hright hinter hcomm
    · exact ⟨(D.equivMapOfInjective e.toMonoidHom e.injective).symm.trans model⟩
    · exact (Subgroup.map_mono hle).trans_eq hmap
  have hne : left ≠ right := by
    intro heq
    have hlcard : Nat.card left = 8 := by
      obtain ⟨model⟩ := hleft
      rw [Nat.card_congr model.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← heq, inf_idem, hlcard] at hinter
    omega
  have hmL := himage left hleft le_sup_left
  have hmR := himage right hright le_sup_right
  rcases hmL with hmL | hmL
  · rcases hmR with hmR | hmR
    · exact (hne (Subgroup.map_injective e.injective (hmL.trans hmR.symm))).elim
    · exact (hnot ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmL,
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmR⟩).elim
  · rcases hmR with hmR | hmR
    · exact ⟨actor, ha, haTerm, hmL, hmR⟩
    · exact (hne (Subgroup.map_injective e.injective (hmL.trans hmR.symm))).elim

end Stellmacher.SectionNine
