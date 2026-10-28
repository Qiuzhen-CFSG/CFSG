module
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.Sigma
public import Theory.GroupAction.LargeOrbits
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Mixed.SmallSubgroups

/-!
# The original975-point mixed orbits

The native mixed PSL₂(25) subgroup calculation bounds every stabilizer on
Delta by20. Thus every orbit in the975-point remainder has at least780
points, forcing transitivity. Orbit–stabilizer gives an actual Sylow2
stabilizer of order16. An element exchanging the nonadjacent base pair
transports this to the reversed mixed set, with the original action intact.

Source: Aschbacher–Smith J.5.5(4–5), printed pp.446–447.
-/

public noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
variable {G:Type*} [Group G] [Finite G] (F:Subgroup G) (q:G) (hq:q∉F)
    (hs:q•(q•basePoint F)=basePoint F) {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F))

include h

omit [Finite G] in
theorem first_orbit_stabilizer_card {x:Cosets F} (hx:x∈orbit F (q•basePoint F)) :
    Nat.card (stabilizer F x)=20480 := by
  obtain ⟨f,hf⟩:=hx
  have he:=stabilizerEquivStabilizer hf.symm
  have hc:Nat.card (stabilizer F (q•basePoint F))=20480:=by
    have hh:=Tits.ExceptionalParabolics.FullRee.first_card
    rw [←h.first_marked,card_map_of_injective h.marking.injective] at hh
    exact hh
  exact (Nat.card_congr he.toEquiv).symm.trans hc

omit [Finite G] in
theorem mixed_stabilizer_dvd {x:Cosets F} (hx:x∈(sourceGraph F q hq hs).neighborSet (basePoint F)) :
    Nat.card (stabilizer (stabilizer F (g•basePoint F)) x) ∣ 20480 := by
  have hh:=card_comap_dvd_of_injective (stabilizer F x)
    (stabilizer F (g•basePoint F)).subtype (stabilizer F (g•basePoint F)).subtype_injective
  change Nat.card (stabilizer (stabilizer F (g•basePoint F)) x) ∣ Nat.card (stabilizer F x) at hh
  rwa [h.first_orbit_stabilizer_card F q ((sourceGraph_neighbor_base F q hq hs).le hx)] at hh

omit [Finite G] in
include hq hs in
theorem second_pair_exchange :
    ∃a:G,a•basePoint F=g•basePoint F ∧ a•(g•basePoint F)=basePoint F := by
  have hg:=h.second_mem_sigma F q hq hs
  have hh:basePoint F∈sourceSigma F q hq hs (g•basePoint F):=
    ⟨Ne.symm hg.1,fun ht=>hg.2 ht.symm⟩
  have ht:=(sourceSigma_smul F q hq hs g⁻¹ (g•basePoint F) (basePoint F)).mpr hh
  rw [inv_smul_smul] at ht
  obtain ⟨f,hf⟩:g⁻¹•basePoint F∈orbit F (g•basePoint F):=
    (h.sigma_base F q hq hs).le ht
  refine ⟨(f.val)⁻¹*g⁻¹,?_,?_⟩
  · rw [mul_smul]
    exact inv_smul_eq_iff.mpr hf.symm
  · rw [mul_smul,inv_smul_smul]
    exact basePoint_fixed F f⁻¹


omit [Finite G] in
theorem mixed_stabilizer_le_twenty {x:Cosets F}
    (hx:x∈(sourceGraph F q hq hs).neighborSet (basePoint F)) :
    Nat.card (stabilizer (stabilizer F (g•basePoint F)) x)≤20 := by
  obtain ⟨e⟩:=h.second_plus
  have hc:=Tits.Max4Outer.Mixed.card_le_twenty_of_dvd_20480 ((stabilizer (stabilizer F (g•basePoint F)) x).map e.toMonoidHom)
    (by rw [card_map_of_injective e.injective]; exact h.mixed_stabilizer_dvd F q hq hs hx)
  rwa [card_map_of_injective e.injective] at hc

theorem mixed_neighbors_transitive
    (x y: ↥((sourceGraph F q hq hs).neighborSet (basePoint F)∩
      sourceSigma F q hq hs (g•basePoint F))) :
    ∃k:stabilizer F (g•basePoint F),k•x.val=y.val := by
  let E:=stabilizer F (g•basePoint F)
  let S:Set (Cosets F):=(sourceGraph F q hq hs).neighborSet (basePoint F)∩
    sourceSigma F q hq hs (g•basePoint F)
  apply transitive_of_large_orbits S ?_ ?_ x.val y.val x.property y.property
  · intro k z hz
    have hk0:(k.val:G)•basePoint F=basePoint F:=basePoint_fixed F k.val
    have hkg:(k.val:G)•(g•basePoint F)=g•basePoint F:=k.property
    refine ⟨?_,?_⟩
    · have hh:=(sourceGraph_adj_smul F q hq hs (k.val:G) (basePoint F) z).mpr hz.1
      rwa [hk0] at hh
    · have hh:=(sourceSigma_smul F q hq hs (k.val:G) (g•basePoint F) z).mpr hz.2
      rwa [hkg] at hh
  · intro z hz
    have hb:=h.mixed_stabilizer_le_twenty F q hq hs hz.1
    have hc:=Nat.card_congr (orbitProdStabilizerEquivGroup E z)
    rw [Nat.card_prod,h.second_stabilizer_card F q] at hc
    have hsiz:S.ncard=975:=h.mixed_neighbors_card F q hq hs
    rw [hsiz]
    change 975<2*Nat.card (orbit E z)
    nlinarith

theorem mixed_neighbors_orbit
    (x: ↥((sourceGraph F q hq hs).neighborSet (basePoint F)∩
      sourceSigma F q hq hs (g•basePoint F))) :
    orbit (stabilizer F (g•basePoint F)) x.val=
      (sourceGraph F q hq hs).neighborSet (basePoint F)∩sourceSigma F q hq hs (g•basePoint F) := by
  ext y
  constructor
  · rintro ⟨k,rfl⟩
    have hk0:(k.val:G)•basePoint F=basePoint F:=basePoint_fixed F k.val
    have hkg:(k.val:G)•(g•basePoint F)=g•basePoint F:=k.property
    refine ⟨?_,?_⟩
    · have hh:=(sourceGraph_adj_smul F q hq hs (k.val:G) (basePoint F) x.val).mpr x.property.1
      rwa [hk0] at hh
    · have hh:=(sourceSigma_smul F q hq hs (k.val:G) (g•basePoint F) x.val).mpr x.property.2
      rwa [hkg] at hh
  · intro hy
    exact h.mixed_neighbors_transitive F q hq hs x ⟨y,hy⟩

theorem mixed_neighbor_stabilizer_card
    (x: ↥((sourceGraph F q hq hs).neighborSet (basePoint F)∩
      sourceSigma F q hq hs (g•basePoint F))) :
    Nat.card (stabilizer (stabilizer F (g•basePoint F)) x.val)=16 := by
  have hc:=Nat.card_congr (orbitProdStabilizerEquivGroup (stabilizer F (g•basePoint F)) x.val)
  rw [Nat.card_prod,h.mixed_neighbors_orbit F q hq hs x,
    h.mixed_neighbors_card F q hq hs,h.second_stabilizer_card F q] at hc
  omega

theorem mixed_neighbor_stabilizer_sylow
    (x: ↥((sourceGraph F q hq hs).neighborSet (basePoint F)∩
      sourceSigma F q hq hs (g•basePoint F))) :
    ∃P:Sylow 2 (stabilizer F (g•basePoint F)),
      (P:Subgroup (stabilizer F (g•basePoint F)))=stabilizer (stabilizer F (g•basePoint F)) x.val := by
  have hc:Nat.card (stabilizer (stabilizer F (g•basePoint F)) x.val)=
      2^(Nat.card (stabilizer F (g•basePoint F))).factorization 2:=by
    rw [h.mixed_neighbor_stabilizer_card F q hq hs x,h.second_stabilizer_card F q]
    rw [show (15600:ℕ)=2^4*(3*5^2*13) from rfl,
      Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
    have hz:(975:ℕ).factorization 2=0:=Nat.factorization_eq_zero_of_not_dvd (by decide)
    norm_num [hz]
  exact ⟨Sylow.ofCard _ hc,Sylow.coe_ofCard _ hc⟩

theorem reverse_mixed_neighbors_transitive
    (x y: ↥((sourceGraph F q hq hs).neighborSet (g•basePoint F)∩
      sourceSigma F q hq hs (basePoint F))) :
    ∃k:stabilizer F (g•basePoint F),k•x.val=y.val := by
  obtain ⟨a,ha0,hag⟩:=h.second_pair_exchange F q hq hs
  have ht (z: ↥((sourceGraph F q hq hs).neighborSet (g•basePoint F)∩
      sourceSigma F q hq hs (basePoint F))) :
      a•z.val∈(sourceGraph F q hq hs).neighborSet (basePoint F)∩
        sourceSigma F q hq hs (g•basePoint F):=by
    constructor
    · have hh:=(sourceGraph_adj_smul F q hq hs a (g•basePoint F) z.val).mpr z.property.1
      rwa [hag] at hh
    · have hh:=(sourceSigma_smul F q hq hs a (basePoint F) z.val).mpr z.property.2
      rwa [ha0] at hh
  obtain ⟨k,hk⟩:=h.mixed_neighbors_transitive F q hq hs ⟨a•x.val,ht x⟩ ⟨a•y.val,ht y⟩
  have hk0:(k.val:G)•basePoint F=basePoint F:=basePoint_fixed F k.val
  have hkg:(k.val:G)•(g•basePoint F)=g•basePoint F:=k.property
  let l:G:=a⁻¹*(k.val:G)*a
  have hact (z:Cosets F):l•z=a⁻¹•((k.val:G)•(a•z)):=
    (mul_smul (a⁻¹*(k.val:G)) a z).trans (mul_smul a⁻¹ (k.val:G) (a•z))
  have hl0:l•basePoint F=basePoint F:=by
    rw [hact,ha0,hkg]
    exact inv_smul_eq_iff.mpr ha0.symm
  have hlg:l•(g•basePoint F)=g•basePoint F:=by
    rw [hact,hag,hk0]
    exact inv_smul_eq_iff.mpr hag.symm
  have hlx:l•x.val=y.val:=by
    rw [hact]
    exact inv_smul_eq_iff.mpr hk
  exact ⟨⟨⟨l,(stabilizer_quotient F).le hl0⟩,hlg⟩,hlx⟩

theorem reverse_mixed_neighbors_orbit
    (x: ↥((sourceGraph F q hq hs).neighborSet (g•basePoint F)∩
      sourceSigma F q hq hs (basePoint F))) :
    orbit (stabilizer F (g•basePoint F)) x.val=
      (sourceGraph F q hq hs).neighborSet (g•basePoint F)∩sourceSigma F q hq hs (basePoint F) := by
  ext y
  constructor
  · rintro ⟨k,rfl⟩
    have hk0:(k.val:G)•basePoint F=basePoint F:=basePoint_fixed F k.val
    have hkg:(k.val:G)•(g•basePoint F)=g•basePoint F:=k.property
    refine ⟨?_,?_⟩
    · have hh:=(sourceGraph_adj_smul F q hq hs (k.val:G) (g•basePoint F) x.val).mpr x.property.1
      rwa [hkg] at hh
    · have hh:=(sourceSigma_smul F q hq hs (k.val:G) (basePoint F) x.val).mpr x.property.2
      rwa [hk0] at hh
  · intro hy
    exact h.reverse_mixed_neighbors_transitive F q hq hs x ⟨y,hy⟩

/-- The two literal second-stabilizer orbits on the original first suborbit. -/
theorem second_orbits_on_first {x:Cosets F}
    (hx:x∈(sourceGraph F q hq hs).neighborSet (basePoint F)) :
    orbit (stabilizer F (g•basePoint F)) x=
      (sourceGraph F q hq hs).commonNeighbors (basePoint F) (g•basePoint F) ∨
    orbit (stabilizer F (g•basePoint F)) x=
      (sourceGraph F q hq hs).neighborSet (basePoint F)∩sourceSigma F q hq hs (g•basePoint F) := by
  by_cases ha:(sourceGraph F q hq hs).Adj (g•basePoint F) x
  · exact Or.inl (h.common_neighbors_orbit F q hq hs ⟨x,hx,ha⟩)
  · apply Or.inr
    apply h.mixed_neighbors_orbit F q hq hs ⟨x,hx,?_,ha⟩
    intro he
    exact (h.second_mem_sigma F q hq hs).2 (he ▸ hx)

end CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
