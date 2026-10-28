module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentClosure
public import Theory.GroupTheory.CentralQuotientLocalMarking
public import Theory.Quasithin.LocalRank

/-!
# The actual Hall local marking in the component's central quotient

The fixed residual P and moved binary subgroup W are the literal restrictions
of the original source subgroups to K. The marked quotient P/O₂(P) is A₅×A₅,
which is centerless, so the kernel of P -> K/Z(K) lies in O₂(P). Thus its
three- and five-ranks remain two. The identity W=[W,P] prevents its image
from vanishing in the central quotient, and gives a genuine two-local
normalizer containing the perfect image of P.

Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, with the original
paired A₅ residual from 10.2.3. No centerless-component premise is used.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The literal images of the fixed residual and moved module retain their
perfect action and both rank-two markings in the actual central quotient. -/
theorem source_a5_oddNormalizer_component_quotient_local_marking_of_residual_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    let N := normalizer (B : Set G)
    let F := ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
    let P := F.subgroupOf K
    let W := (D.fullModule.subgroupOf N).subgroupOf K
    let q := QuotientGroup.mk' (center K)
    Group.IsPerfect (P.map q) ∧ W.map q ≠ ⊥ ∧
      IsElementaryAbelian 2 (W.map q) ∧ W.map q = ⁅W.map q,P.map q⁆ ∧
      P.map q ≤ normalizer (W.map q : Set (K ⧸ center K)) ∧
      primeRank 3 (P.map q) = 2 ∧ primeRank 5 (P.map q) = 2 := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  let P := F.subgroupOf K
  let W := (D.fullModule.subgroupOf N).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  obtain ⟨hP,_,_,hW,hE,_,hm,_,⟨a⟩,h3,h5⟩ :=
    source_a5_oddNormalizer_component_local_marking_of_residual_le
      D e hn B hBC hodd hBV K hFK
  let : Group.IsPerfect P := hP
  have hc : center (P ⧸ pCore 2 P) = ⊥ := by
    have ht : center (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) = ⊥ := by
      rw [Subgroup.center_prod,alternatingGroup.center_eq_bot (by simp)]
      exact bot_prod_bot
    apply bot_unique
    intro z hz
    have hz' := (centerCongr a ⟨z,hz⟩).property
    change a z ∈ center (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) at hz'
    rw [ht,mem_bot] at hz'
    exact mem_bot.mpr (a.injective (hz'.trans (map_one a).symm))
  obtain ⟨hp,hne,he,hmove,hnorm⟩ :=
    CentralQuotientLocalMarking.moved_image P W hW hE hm
  exact ⟨hp,hne,he,hmove,hnorm,
    (CentralQuotientLocalMarking.primeRank_map P hc (by decide : Odd 3)).trans h3,
    (CentralQuotientLocalMarking.primeRank_map P hc (by decide : Odd 5)).trans h5⟩

/-- The actual quotient normalizer of the nontrivial binary image has enough
three- and five-rank to bound both local ranks of the component quotient below by two. -/
theorem source_a5_oddNormalizer_component_quotient_local_ranks_of_residual_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    2 ≤ twoLocalPrimeRank 3 (K ⧸ center K) ∧
      2 ≤ twoLocalPrimeRank 5 (K ⧸ center K) := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  let P := F.subgroupOf K
  let W := (D.fullModule.subgroupOf N).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  obtain ⟨_,hne,he,_,hnorm,h3,h5⟩ :=
    source_a5_oddNormalizer_component_quotient_local_marking_of_residual_le
      D e hn B hBC hodd hBV K hFK
  let : IsElementaryAbelian 2 (W.map q) := he
  have hl : IsTwoLocal (normalizer (W.map q : Set (K ⧸ center K))) :=
    ⟨W.map q,hne,IsElementaryAbelian.isPGroup 2 (W.map q),rfl⟩
  constructor
  · calc
      2 = primeRank 3 (P.map q) := h3.symm
      _ ≤ primeRank 3 (normalizer (W.map q : Set (K ⧸ center K))) := primeRank_mono 3 hnorm
      _ ≤ twoLocalPrimeRank 3 (K ⧸ center K) := hl.primeRank_le 3
  · calc
      2 = primeRank 5 (P.map q) := h5.symm
      _ ≤ primeRank 5 (normalizer (W.map q : Set (K ⧸ center K))) := primeRank_mono 5 hnorm
      _ ≤ twoLocalPrimeRank 5 (K ⧸ center K) := hl.primeRank_le 5
end CFSG.Quasithin.Chapter10
