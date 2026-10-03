module
public import Stellmacher.SectionNine.DistanceOneInitialCenterFixedVstar
public import Theory.GroupAction.ElementaryEightInvolution

/-!
# The initial-center fixed plane of the selected elementary eight

An elementary eight U inside the exact Vstar, normalized by Z_a but moved by
some Q_d element and self-centralizing inside Vstar, meets Z_a in a four-group.
This intersection is also its full centralizer inside Z_a. The original local
context and faithful/local conclusions remain explicit inputs.

The order8 seed Z_a intersect Q_d is normalized by Q_d, so U is not that seed.
Choose an initial-center involution outside Q_d. Its Vstar fixed subgroup is
exactly the seed; hence it acts nontrivially on U. The elementary-eight
involution theorem gives four fixed elements, whose ambient image is exactly
Z_a intersect U. A Z_a element in Q_d centralizing U lies in Vstar and hence U.
An outside-core centralizing element would instead force all of U into its
Vstar fixed subgroup, the seed, giving the same excluded equality.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), p.48. These precise
fixed-plane data feed the elementary-kernel normalizer lift through the actual
first wreath quotient. No quotient-image noncentrality is assumed here.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven

/-- The actual selected eight meets the initial elementary center in exactly
its four-element centralizer there. -/
public theorem distance_one_initial_eight_fixed_plane
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx)
    (hlocal : DistanceOneLocalConclusion ctx)
    (U : Subgroup G) (hElem : IsElementaryAbelian 2 U) (hUcard : Nat.card U=8)
    (hUV : U ≤ conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a'))
    (hZaN : ZAt ctx.Γ ctx.criticalPath.a ≤ Subgroup.normalizer (U : Set G))
    (hQnot : ¬ QAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (U : Set G))
    (hself : conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') ⊓ Subgroup.centralizer (U : Set G) = U) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a ⊓ U : Subgroup G) = 4 ∧
      ZAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (U : Set G) =
        ZAt ctx.Γ ctx.criticalPath.a ⊓ U := by
  classical
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let Za := ZAt ctx.Γ ctx.criticalPath.a
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let seed := Za ⊓ Q
  change U ≤ V at hUV
  change V ⊓ Subgroup.centralizer (U : Set G)=U at hself
  change Nat.card (Za ⊓ U : Subgroup G)=4 ∧
    Za ⊓ Subgroup.centralizer (U : Set G)=Za ⊓ U
  have hseed : seed ≤ V := by
    intro x hx
    exact Subgroup.subset_closure ⟨1,⟨x,hx⟩,by simp⟩
  have hseedcard : Nat.card seed=8 := (distance_one_seed_data ctx hlength hfaithful hlocal).1
  have hQT : Q ≤ T := by
    have hend : ctx.criticalPath.a'=ctx.criticalPath.firstStep := by
      rw [← ctx.criticalPath.path_end,← ctx.criticalPath.path_first]
      congr 1
      exact Fin.ext hlength
    change QAt ctx.Γ ctx.criticalPath.a' ≤ T
    rw [hend]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hQZa : Q ≤ Subgroup.normalizer (Za : Set G) := by
    apply hQT.trans ((SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1.trans ?_)
    change GAt ctx.Γ ctx.criticalPath.a ≤ Subgroup.normalizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)
    exact stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a
  have hQseed : Q ≤ Subgroup.normalizer (seed : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro q hq a ha
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hQZa hq) a).mp ha.1,
      Q.mul_mem (Q.mul_mem hq ha.2) (Q.inv_mem hq)⟩
  have hUneq : U ≠ seed := by
    intro heq
    apply hQnot
    change Q ≤ Subgroup.normalizer (U : Set G)
    rw [heq]
    exact hQseed
  have hUnle : ¬ U ≤ seed := by
    intro hh
    exact hUneq (Subgroup.eq_of_le_of_card_ge hh (by rw [hUcard,hseedcard]))
  have hneighbor : ctx.criticalPath.a' ∈
      CosetGraphContext.neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [CosetGraphContext.neighborhood,ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hlength)
  let _ : IsElementaryAbelian 2 (ZAt ctx.Γ ctx.criticalPath.a) :=
    SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  let _ : IsElementaryAbelian 2 U := hElem
  have hnotZaQ : ¬ Za ≤ Q := ctx.criticalPath.critical.2
  obtain ⟨s,hsZa,hsQ⟩ := SetLike.not_le_iff_exists.mp hnotZaQ
  have hsZa' : s ∈ ZAt ctx.Γ ctx.criticalPath.a := hsZa
  have hs2 : s^2=1 := elemPow_eq_one_of_isElementaryAbelian s hsZa'
  have hsne : s ≠ 1 := fun hh => hsQ (hh.symm ▸ Q.one_mem)
  have hfixed (c : G) (hcZa : c ∈ Za) (hcQ : c ∉ Q) :
      V ⊓ Subgroup.centralizer ({c} : Set G)=seed :=
    distance_one_initial_center_fixed_vstar ctx hlength hfaithful hlocal c hcZa hcQ
  let R := Subgroup.zpowers s
  have hRZa : R ≤ Za := Subgroup.zpowers_le.mpr hsZa
  let _ : Subgroup.Normalizes R U := ⟨hRZa.trans hZaN⟩
  let rs : R := ⟨s,Subgroup.mem_zpowers s⟩
  have hRcard : Nat.card R=2 := by rw [Nat.card_zpowers]; exact orderOf_eq_prime hs2 hsne
  have hrs : rs ≠ 1 ∧ rs^2=1 :=
    ⟨fun hh => hsne (congrArg Subtype.val hh),Subtype.ext hs2⟩
  have hmove : ∃ u : U, rs • u ≠ u := by
    by_contra hn
    push Not at hn
    apply hUnle
    intro u hu
    apply (hfixed s hsZa hsQ).le
    refine ⟨hUV hu,Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := congrArg Subtype.val (hn ⟨u,hu⟩)
    change s*u*s⁻¹=u at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hcard := fixed_subgroup_card_four_of_nontrivial_involution_on_eight
    (U := U) rs hrs hRcard hUcard hmove
  have hmap : (FixedPoints.subgroup R U).map U.subtype=Za ⊓ U := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      have hsfix : s*(u:G)*s⁻¹=u := congrArg Subtype.val (hu rs)
      have huseed : (u:G) ∈ seed := (hfixed s hsZa hsQ).le
        ⟨hUV u.property,Subgroup.mem_centralizer_singleton_iff.mpr
          (mul_inv_eq_iff_eq_mul.mp hsfix).symm⟩
      exact ⟨huseed.1,u.property⟩
    · intro x hx
      refine ⟨⟨x,hx.2⟩,?_,rfl⟩
      intro r
      apply Subtype.ext
      change (r:G)*x*(r:G)⁻¹=x
      rw [setLike_mul_comm (s := ZAt ctx.Γ ctx.criticalPath.a) (hRZa r.property) hx.1,
        mul_inv_cancel_right]
  refine ⟨?_,?_⟩
  · rw [← hmap,Subgroup.card_map_of_injective U.subtype_injective]
    exact hcard
  · apply le_antisymm
    · intro c hc
      refine ⟨hc.1,?_⟩
      by_cases hcQ : c ∈ Q
      · exact hself.le ⟨hseed ⟨hc.1,hcQ⟩,hc.2⟩
      · exfalso
        apply hUnle
        intro u hu
        exact (hfixed c hc.1 hcQ).le ⟨hUV hu,
          Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hc.2 u hu)⟩
    · exact inf_le_inf_left Za (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
end Stellmacher.SectionNine
