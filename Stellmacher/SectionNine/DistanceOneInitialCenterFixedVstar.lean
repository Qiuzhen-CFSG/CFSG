module
public import Stellmacher.SectionNine.DistanceOneVstarFactorSwap
public import Theory.GroupTheory.QuaternionCentralProductDiagonal
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The exact Vstar fixed subgroup of an outside initial-center involution

At distance one, every element of Z_a outside the terminal core fixes exactly
the seed Z_a intersect Q_d inside the actual Vstar. This statement requires
only the original local context and explicit faithful/local conclusions; no
selected elementary eight or normalizer quotient is assumed.

Choose the known initial-center swapping involution s. It lies outside Q_d,
since an element in the seed lies in Vstar and hence preserves each quaternion
factor. The seed has index two in Z_a, so every other outside element c differs
from s by an element of the seed. Thus c also swaps the factors, and c²=1
because Z_a is elementary. The fixed-diagonal theorem identifies its Vstar
centralizer as an elementary eight. It contains the order8 seed centralized
by Z_a, so cardinal equality identifies these exact subgroups.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), p.48. This provides
the fixed-space geometry needed for the initial-center four-plane and
centralizer calculation of the selected U.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven

/-- An outside-core element of the initial elementary center fixes precisely
the original seed inside the exact Vstar. -/
public theorem distance_one_initial_center_fixed_vstar
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx)
    (hlocal : DistanceOneLocalConclusion ctx) :
    let V := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    ∀ c ∈ ZAt ctx.Γ ctx.criticalPath.a, c ∉ QAt ctx.Γ ctx.criticalPath.a' →
      V ⊓ Subgroup.centralizer ({c} : Set G) =
        ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a' := by
  classical
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let Za := ZAt ctx.Γ ctx.criticalPath.a
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let seed := Za ⊓ Q
  change ∀ c ∈ Za, c ∉ Q → V ⊓ Subgroup.centralizer ({c} : Set G) = seed
  obtain ⟨left,right,hleft,hright,hjoin,hinter,hcomm,s,hsZa,_,hsL,_⟩ :=
    distance_one_vstar_factor_swap ctx hlength hfaithful hlocal
  change V = left ⊔ right at hjoin
  have hseed : seed ≤ V := by
    intro x hx
    exact Subgroup.subset_closure ⟨1,⟨x,hx⟩,by simp⟩
  have hseedcard : Nat.card seed=8 := (distance_one_seed_data ctx hlength hfaithful hlocal).1
  have hZacard : Nat.card Za=16 := hfaithful.1
  have hi : Q.relIndex Za=2 := by
    have hh := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) seed Za bot_le inf_le_left
    simp only [Subgroup.relIndex_bot_left] at hh
    change Nat.card seed * (Za ⊓ Q).relIndex Za = Nat.card Za at hh
    rw [Subgroup.inf_relIndex_left,hseedcard,hZacard] at hh
    omega
  have hVnL : V ≤ Subgroup.normalizer (left : Set G) := by
    rw [hjoin]
    apply sup_le left.le_normalizer
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro c hc b hb
    exact hcomm b hb c hc
  have hVnR : V ≤ Subgroup.normalizer (right : Set G) := by
    rw [hjoin]
    apply sup_le ?_ right.le_normalizer
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hne : left ≠ right := by
    intro hh
    have hleftcard : Nat.card left=8 := by
      rw [Nat.card_congr hleft.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← hh,inf_idem,hleftcard] at hinter
    omega
  have hsQ : s ∉ Q := by
    intro hs
    exact hne ((Subgroup.mem_normalizer_iff_map_conj_eq.mp (hVnL (hseed ⟨hsZa,hs⟩))).symm.trans hsL)
  have hneighbor : ctx.criticalPath.a' ∈
      CosetGraphContext.neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [CosetGraphContext.neighborhood,ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hlength)
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  have hs2 : s^2=1 := elemPow_eq_one_of_isElementaryAbelian s hsZa
  intro c hcZa hcQ
  have hc2 : c^2=1 := elemPow_eq_one_of_isElementaryAbelian c hcZa
  have hcsQ : c*s ∈ Q := by
    have hh : (⟨c,hcZa⟩ : Za)*(⟨s,hsZa⟩ : Za) ∈ Q.subgroupOf Za := by
      apply (Subgroup.mul_mem_iff_of_index_two hi).mpr
      change (c ∈ Q ↔ s ∈ Q)
      simp only [hcQ,hsQ]
    exact hh
  have hcsV : c*s ∈ V := hseed ⟨Za.mul_mem hcZa hsZa,hcsQ⟩
  have hcL : left.map (MulAut.conj c).toMonoidHom = right := by
    change left.conjBy c = right
    have hc : c=(c*s)*s := by rw [mul_assoc,← pow_two,hs2,mul_one]
    rw [hc,Subgroup.conjBy_mul]
    change (left.map (MulAut.conj s).toMonoidHom).conjBy (c*s) = right
    rw [hsL]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hVnR hcsV)
  let θ : left ≃* right := (left.equivMapOfInjective (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hcL)
  have hfix : V ⊓ Subgroup.centralizer ({c} : Set G) =
      Subgroup.quaternionDiagonal left right θ hcomm := by
    rw [hjoin]
    exact Subgroup.quaternion_diagonal_eq_inf_centralizer_of_swap left right θ hinter hcomm c hc2
      (fun _ => rfl)
  have hfixcard : Nat.card (V ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) = 8 := by
    rw [hfix]
    exact (Subgroup.quaternion_diagonal_elementary_eight left right hleft.some θ hinter hcomm).2.1
  have hle : seed ≤ V ⊓ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    exact ⟨hseed hx,Subgroup.mem_centralizer_singleton_iff.mpr
      (setLike_mul_comm (s := ZAt ctx.Γ ctx.criticalPath.a) hx.1 hcZa)⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hfixcard,hseedcard])).symm
end Stellmacher.SectionNine
