module
public import Stellmacher.SectionNine.DistanceOneVstarSylowCentralizer
public import Stellmacher.SectionNine.DistanceOneVstarThreeAction
public import Theory.GroupTheory.SpecificGroups.QuaternionEightCubicNormalizer
public import Theory.GroupTheory.InnerRestrictionsCommutingSup

/-!
# The terminal core swaps the quaternion factors of Vstar

In the original ambient distance-one configuration, the terminal two-core
contains an element interchanging any supplied pair of quaternion factors
of the exact Vstar. The faithful and local conclusions remain explicit inputs.
This distinguishes the exceptional core-normalized diagonal from the elementary
eights used for the two local S4 normalizers.

If the core preserved both factors, each restriction would be a two-subgroup
of quaternion automorphisms normalized by the actual nontrivial cubic residual
action. The quaternion cubic-normalizer theorem makes these restrictions inner.
The common product-conjugation lemma then puts each core element in Vstar times
its ambient centralizer. The first wreath quotient already places its Sylow
centralizer inside Vstar Z_a, so the core lies in Vstar Z_a.

Both the core and Vstar Z_a have order64, whereas Z_a is not contained in the
core by criticality. This contradiction proves non-preservation. Intrinsic
uniqueness of the quaternion factors turns it into their actual transposition.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), p.48. The proof uses
the actual two-core, residual actor, and first-vertex quotient; an abstract
central-product action alone does not imply the claimed core swap.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven

private theorem core_restriction_inner
    {G : Type*} [Group G] (D Q : Subgroup G)
    (model : D ≃* QuaternionGroup 2) (hQp : IsPGroup 2 Q)
    (hQD : Q ≤ Subgroup.normalizer (D : Set G))
    (g : G) (hgD : g ∈ Subgroup.normalizer (D : Set G))
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) (hg3 : g ^ 3 = 1)
    (hgne : D.normalizerMonoidHom ⟨g,hgD⟩ ≠ 1)
    (q : G) (hq : q ∈ Q) :
    ∃ d : G, d ∈ D ∧ ∀ x ∈ D, q*x*q⁻¹=d*x*d⁻¹ := by
  let N := Subgroup.normalizer (D : Set G)
  let P := (Q.subgroupOf N).map D.normalizerMonoidHom
  let e := D.normalizerMonoidHom ⟨g,hgD⟩
  have hPp : IsPGroup 2 P := (hQp.comap_of_injective N.subtype N.subtype_injective).map D.normalizerMonoidHom
  have he3 : e ^ 3 = 1 := by
    rw [← map_pow]
    have hh : (⟨g,hgD⟩ : N)^3 = 1 := Subtype.ext hg3
    rw [hh, map_one]
  have hnQ : (⟨g,hgD⟩ : N) ∈ Subgroup.normalizer (Q.subgroupOf N : Set N) :=
    Subgroup.le_normalizer_comap N.subtype hgQ
  have hnP : e ∈ Subgroup.normalizer (P : Set (MulAut D)) :=
    Subgroup.le_normalizer_map D.normalizerMonoidHom (Subgroup.mem_map_of_mem _ hnQ)
  have hinner := QuaternionGroup.le_inner_of_isPGroup_two_of_normalized_by_cubic_of_equiv
    model P hPp e he3 hgne hnP
  have hqP : D.normalizerMonoidHom ⟨q,hQD hq⟩ ∈ P :=
    Subgroup.mem_map_of_mem _ hq
  obtain ⟨d, hd⟩ := hinner hqP
  refine ⟨d, d.property, ?_⟩
  intro x hx
  exact (congrArg (fun a : MulAut D => (a ⟨x,hx⟩ : G)) hd).symm

universe u
private theorem core_not_preserves_factors
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (left right : Subgroup G)
    (hleft : IsModel left Q8) (hright : IsModel right Q8)
    (hjoin : conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') = left ⊔ right)
    (hinter : Nat.card (left ⊓ right : Subgroup G) = 2)
    (hcomm : ∀ b ∈ left, ∀ c ∈ right, b*c=c*b) :
    ¬ QAt ctx.Γ ctx.criticalPath.a' ≤
      Subgroup.normalizer (left : Set G) ⊓ Subgroup.normalizer (right : Set G) := by
  classical
  intro hpres
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let Za := ZAt ctx.Γ ctx.criticalPath.a
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  change V = left ⊔ right at hjoin
  have hcont := distance_one_vstar_containments ctx.toLocalContext hlength
  have hQT : Q ≤ T := by
    have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
      rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
      congr 1
      exact Fin.ext hlength
    change QAt ctx.Γ ctx.criticalPath.a' ≤ T
    rw [hend]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hTterminal : T ≤ terminal := by
    have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
      rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
      congr 1
      exact Fin.ext hlength
    change T ≤ GAt ctx.Γ ctx.criticalPath.a'
    rw [hend]
    exact (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2.1
  have hZaT : Za ≤ T := by
    change ZAt ctx.toLocalContext.Γ ctx.toLocalContext.criticalPath.a ≤ T
    rw [← hlocal.2.2.2.1]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  have hQcard : Nat.card Q = 64 := by
    have hh := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) Q T bot_le hQT
    simp only [Subgroup.relIndex_bot_left] at hh
    have hi : Q.relIndex T = 2 := distance_one_terminal_core_index_in_sylow ctx.toLocalContext hlength hlocal
    rw [hi, hlocal.2.2.1] at hh
    omega
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 6) hQcard
  have hVcard : Nat.card V = 32 := distance_one_vstar_card ctx.toLocalContext hlocal
  have hseedcard := (distance_one_seed_data ctx.toLocalContext hlength hfaithful hlocal).1
  change Nat.card (Za ⊓ Q : Subgroup G) = 8 at hseedcard
  have hZacard : Nat.card Za = 16 := hfaithful.1
  have hseed : Za ⊓ Q ≤ V := by
    intro x hx
    exact Subgroup.subset_closure ⟨1, ⟨x, hx⟩, by simp⟩
  have hinf : V ⊓ Za = Za ⊓ Q := by
    rw [inf_comm]
    exact le_antisymm (inf_le_inf_left Za hcont.2.1) (le_inf inf_le_left hseed)
  have hn : terminal ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcont.1.1).mp hcont.1.2
  have hjoincard : Nat.card (V ⊔ Za : Subgroup G) = 64 := by
    have hh := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes V Za
      (hZaT.trans (hTterminal.trans hn))
    rw [hVcard, hZacard, hinf, hseedcard] at hh
    omega
  obtain ⟨hcenter, hzcard, ⟨g, hgE, hgorder⟩, _⟩ :=
    distance_one_vstar_three_action ctx hlength hfaithful hlocal
  have hg : g ∈ terminal := by
    apply SevenSix.twoResidualIn_le (GAt ctx.Γ ctx.criticalPath.a')
    simpa only [EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      GAt, CosetGraphContext.stabilizer] using hgE
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := by
    change g ∈ Subgroup.normalizer (ctx.Γ.twoCoreAt ctx.criticalPath.a' : Set G)
    rw [ctx.Γ.twoCoreAt_def]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (SevenSix.twoCoreIn_le terminal)).mp (SevenSix.twoCoreIn_normal terminal) hg
  have hg3 : g^3=1 := by rw [← hgorder]; exact pow_orderOf_eq_one g
  have hgmap : (left ⊔ right).map (MulAut.conj g).toMonoidHom = left ⊔ right := by
    rw [← hjoin]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hn hg)
  have hgcube (x : G) : (MulAut.conj g) ((MulAut.conj g) ((MulAut.conj g) x)) = x := by
    have hh : (MulAut.conj g)^3 = 1 := by rw [← map_pow, hg3, map_one]
    simpa [pow_succ] using congrArg (fun e : MulAut G => e x) hh
  have hgpres := Subgroup.quaternion_factors_invariant_of_cube_eq_one left right
    hleft hright hinter hcomm (MulAut.conj g) hgmap hgcube
  have hgL := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgpres.1
  have hgR := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgpres.2
  have hfix := (distance_one_vstar_residual_centralizer
    ctx hlength hfaithful hlocal hcenter).2 g hgE hgorder
  have hnontriv (D : Subgroup G) (hD : IsModel D Q8) (hDV : D ≤ V)
      (hgD : g ∈ Subgroup.normalizer (D : Set G)) :
      D.normalizerMonoidHom ⟨g,hgD⟩ ≠ 1 := by
    intro heq
    have hDZ : D ≤ ZAt ctx.Γ ctx.criticalPath.a' := by
      intro d hd
      apply hfix d (hDV hd)
      have hh := congrArg (fun e : MulAut D => (e ⟨d,hd⟩ : G)) heq
      change g*d*g⁻¹=d at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh)
    have hh := Subgroup.card_le_of_le hDZ
    obtain ⟨model⟩ := hD
    have hDcard : Nat.card D = 8 := by
      rw [Nat.card_congr model.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [hDcard, hzcard] at hh
    omega
  have hQL : Q ≤ Subgroup.normalizer (left : Set G) := hpres.trans inf_le_left
  have hQR : Q ≤ Subgroup.normalizer (right : Set G) := hpres.trans inf_le_right
  have hQjoin : Q ≤ V ⊔ Za := by
    intro q hq
    obtain ⟨w, hw, hk⟩ := Subgroup.exists_mul_inv_mem_centralizer_of_inner_restrictions
      left right hcomm q
      (core_restriction_inner left Q hleft.some hQp hQL g hgL hgQ hg3
        (hnontriv left hleft (hjoin ▸ le_sup_left) hgL) q hq)
      (core_restriction_inner right Q hright.some hQp hQR g hgR hgQ hg3
        (hnontriv right hright (hjoin ▸ le_sup_right) hgR) q hq)
    have hwV : w ∈ V := hjoin.symm ▸ hw
    have hkT : w⁻¹*q ∈ T := T.mul_mem (T.inv_mem (hcont.2.2.1 hwV)) (hQT hq)
    have hkV : w⁻¹*q ∈ Subgroup.centralizer (V : Set G) := by rw [hjoin]; exact hk
    have hkj := distance_one_vstar_sylow_centralizer_le_join
      ctx.toLocalContext hlength hfaithful hlocal ⟨hkT, hkV⟩
    have hh := (V ⊔ Za).mul_mem (Subgroup.mem_sup_left hwV) hkj
    simpa using hh
  have heq : Q = V ⊔ Za := Subgroup.eq_of_le_of_card_ge hQjoin (by rw [hjoincard,hQcard])
  apply ctx.criticalPath.critical.2
  change Za ≤ Q
  rw [heq]
  exact le_sup_right


/-- An element of the actual terminal core interchanges the supplied intrinsic
quaternion factors of the exact Vstar. -/
public theorem distance_one_terminal_core_factor_swap
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (left right : Subgroup G)
    (hleft : IsModel left Q8) (hright : IsModel right Q8)
    (hjoin : conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') = left ⊔ right)
    (hinter : Nat.card (left ⊓ right : Subgroup G) = 2)
    (hcomm : ∀ b ∈ left, ∀ c ∈ right, b*c=c*b) :
    ∃ actor : G, actor ∈ QAt ctx.Γ ctx.criticalPath.a' ∧
      left.map (MulAut.conj actor).toMonoidHom = right ∧
      right.map (MulAut.conj actor).toMonoidHom = left := by
  have hnotall := core_not_preserves_factors ctx hlength hfaithful hlocal
    left right hleft hright hjoin hinter hcomm
  obtain ⟨actor, hactor, hnot⟩ := SetLike.not_le_iff_exists.mp hnotall
  have hactorB : actor ∈ GAt ctx.Γ ctx.criticalPath.a' := by
    apply SevenSix.twoCoreIn_le (GAt ctx.Γ ctx.criticalPath.a')
    simpa only [QAt, CosetGraphContext.q, ctx.Γ.twoCoreAt_def,
      GAt, CosetGraphContext.stabilizer] using hactor
  have hn := (distance_one_vstar_containments ctx.toLocalContext hlength).1
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hn.1).mp hn.2 hactorB
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm
  change (conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')).map (MulAut.conj actor).toMonoidHom =
    conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') at hmap
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
    · exact ⟨actor, hactor, hmL, hmR⟩
    · exact (hne (Subgroup.map_injective e.injective (hmL.trans hmR.symm))).elim

end Stellmacher.SectionNine
