module

public import Theory.GroupTheory.MinusExtraspecialA5Fusion
import all Theory.GroupTheory.MinusExtraspecialA5Fusion
public import Theory.SpecificGroups.Alternating.EightNineInvolutionCounts.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.OutsideSizes.Model

/-!
# The two local centralizer orders in the extraspecial extension

For a self-centralizing minus extraspecial normal subgroup Q with quotient
A₅, the literal outside involution acts evenly and nontrivially on the five
singular points. Its fixed core has order four. The existing cocycle
calculation corrects every lift of a quotient-centralizer element by an
element of Q. Thus the centralizer maps onto the quotient centralizer of
order four, with kernel of order four, and has order sixteen.

The internal import reuses the original action, kernel and parity proofs;
it neither changes the fusion module nor duplicates its conjugacy theorem.
Source: Aschbacher, *Sporadic Groups* (1994), 46.8, 46.11 and the beginning
of 47.1, printed pp.253–255,259–260.
-/

open Subgroup
open MinusExtraspecial MinusExtraspecial.FixedFourCalculation.Outside
namespace J2OutsideSizesCalculation
variable {H : Type*} [Group H]

private theorem centralizer_card_equiv {K : Type*} [Group K] (e : H ≃* K) (u : H) :
    Nat.card (centralizer ({u} : Set H)) = Nat.card (centralizer ({e u} : Set K)) := by
  apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
  intro x
  simp only [mem_centralizer_singleton_iff]
  change x * u = u * x ↔ e x * e u = e u * e x
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

private theorem alternating_centralizer_card (u : alternatingGroup (Fin 5))
    (hu : orderOf u = 2) :
    Nat.card (centralizer ({u} : Set (alternatingGroup (Fin 5)))) = 4 := by
  let t : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by simp [Equiv.Perm.mem_alternatingGroup, map_mul]⟩
  have ht : orderOf t = 2 := orderOf_eq_prime (by decide) (by decide)
  obtain ⟨g, hg⟩ := isConj_iff.mp (alternatingGroup.five_involutions_isConj u t hu ht)
  have hc := centralizer_card_equiv (MulAut.conj g) u
  change Nat.card (centralizer ({u} : Set (alternatingGroup (Fin 5)))) =
    Nat.card (centralizer ({g * u * g⁻¹} : Set (alternatingGroup (Fin 5)))) at hc
  rw [hg] at hc
  rw [hc]
  have htc := alternatingGroup.EightNineInvolutionCounts.two_mul_card_centralizer
    t (Equiv.swap 0 1) (by decide) (by change _ * _ = _ * _; decide)
  rw [Equiv.Perm.nat_card_centralizer,
    alternatingGroup.involution_cycleType_of_degree_le_six (by decide) t ht] at htc
  norm_num [Nat.factorial] at htc
  omega

private theorem core_card (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q) (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (u : H) (hu : u ^ 2 = 1) (huQ : u ∉ Q) :
    Nat.card ↥(centralizer ({u} : Set H) ⊓ Q) = 4 := by
  let a := modelAction Q e u
  have ha : a ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  have heven : Equiv.Perm.sign (fivePointAction a) = 1 := pointAction_even Q e hc eA u
  have hne : fivePointAction a ≠ 1 := by
    intro heq
    apply huQ
    rw [← pointAction_kernel Q e hc]
    exact heq
  have hfix := fixed_card a ha heven hne
  have hequiv : Nat.card ((centralizer ({u} : Set H)).subgroupOf Q) =
      Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id Model)) := by
    apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
    intro x
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    change ((x : H) * u = u * (x : H)) ↔
      e (MulAut.conjNormal u (e.symm (e x))) = e x
    rw [e.symm_apply_apply, e.injective.eq_iff, Subtype.ext_iff]
    change ((x : H) * u = u * (x : H)) ↔ u * (x : H) * u⁻¹ = (x : H)
    exact ⟨fun h => by rw [← h]; group, fun h => (mul_inv_eq_iff_eq_mul.mp h).symm⟩
  rw [← subgroupOf_map_subtype (centralizer ({u} : Set H)) Q,
    card_map_of_injective Q.subtype_injective, hequiv, hfix]

private theorem centralizer_image (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q) (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (u : H) (hu : u ^ 2 = 1) (huQ : u ∉ Q) :
    (centralizer ({u} : Set H)).map (QuotientGroup.mk' Q) =
      centralizer ({QuotientGroup.mk' Q u} : Set (H ⧸ Q)) := by
  let π := QuotientGroup.mk' Q
  let a := modelAction Q e u
  have ha : a ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  have heven : Equiv.Perm.sign (fivePointAction a) = 1 := pointAction_even Q e hc eA u
  have hne : fivePointAction a ≠ 1 := by
    intro heq
    apply huQ
    rw [← pointAction_kernel Q e hc]
    exact heq
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg π (mem_centralizer_singleton_iff.mp hc)
  · intro b hb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q b
    have hg := mem_centralizer_singleton_iff.mp hb
    change π g * π u = π u * π g at hg
    let v := g * u * g⁻¹
    have hv : v ^ 2 = 1 := by
      change (MulAut.conj g u) ^ 2 = 1
      rw [← map_pow, hu, map_one]
    have hdmem : v * u⁻¹ ∈ Q := by
      apply (QuotientGroup.eq_one_iff _).mp
      change π (v * u⁻¹) = 1
      simp only [v, map_mul, map_inv]
      rw [hg]
      group
    let d : Q := ⟨v * u⁻¹, hdmem⟩
    have hd : d * MulAut.conjNormal u d = 1 := by
      apply Subtype.ext
      change (v * u⁻¹) * (u * (v * u⁻¹) * u⁻¹) = 1
      calc
        _ = v ^ 2 * (u ^ 2)⁻¹ := by simp only [pow_two]; group
        _ = 1 := by rw [hu, hv]; simp
    have hd' : e d * a (e d) = 1 := by
      change e d * e (MulAut.conjNormal u (e.symm (e d))) = 1
      rw [e.symm_apply_apply, ← map_mul, hd, map_one]
    obtain ⟨q, hq⟩ := cocycle_eq_coboundary a ha heven hne (e d) hd'
    let qQ := e.symm q
    have hdQ : d = qQ * (MulAut.conjNormal u qQ)⁻¹ := by
      apply e.injective
      change e d = q * (e (MulAut.conjNormal u (e.symm q)))⁻¹ at hq
      simpa only [map_mul, map_inv, qQ, MulEquiv.apply_symm_apply] using hq
    have hdH := congrArg Subtype.val hdQ
    change v * u⁻¹ = (qQ : H) * (u * (qQ : H) * u⁻¹)⁻¹ at hdH
    have hconj : (qQ : H) * u * (qQ : H)⁻¹ = v := by
      calc
        _ = ((qQ : H) * (u * (qQ : H) * u⁻¹)⁻¹) * u := by group
        _ = v := by rw [← hdH]; group
    refine mem_map.mpr ⟨(qQ : H)⁻¹ * g, ?_, ?_⟩
    · apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (fun x => (qQ : H)⁻¹ * x * g) hconj
      simpa only [v, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh.symm
    · change π ((qQ : H)⁻¹ * g) = π g
      rw [map_mul, map_inv, show π (qQ : H) = 1 from (QuotientGroup.eq_one_iff _).mpr qQ.property]
      simp

public theorem extension_sizes [Finite H] (Q : Subgroup H) [Q.Normal] (e : Q ≃* Model)
    (hc : centralizer (Q : Set H) ≤ Q) (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (u : H) (hu : orderOf u = 2) (huQ : u ∉ Q) :
    Nat.card ↥(centralizer ({u} : Set H) ⊓ Q) = 4 ∧
    Nat.card (centralizer ({u} : Set H)) = 16 := by
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have hcore := core_card Q e hc eA u hu2 huQ
  refine ⟨hcore, ?_⟩
  let C := centralizer ({u} : Set H)
  let π := QuotientGroup.mk' Q
  let f := π.comp C.subtype
  have hk : f.ker = Q.subgroupOf C := by
    ext c
    exact QuotientGroup.eq_one_iff (c : H)
  have hkcard : Nat.card f.ker = 4 := by
    rw [hk, ← card_map_of_injective C.subtype_injective,
      subgroupOf_map_subtype, inf_comm]
    exact hcore
  have hr : f.range = centralizer ({π u} : Set (H ⧸ Q)) := by
    rw [MonoidHom.range_comp, range_subtype]
    exact centralizer_image Q e hc eA u hu2 huQ
  have hou : orderOf (π u) = 2 := orderOf_eq_prime
    (by rw [← map_pow, hu2, map_one]) (fun h => huQ ((QuotientGroup.eq_one_iff u).mp h))
  have hrcard : Nat.card f.range = 4 := by
    rw [hr, centralizer_card_equiv eA]
    exact alternating_centralizer_card (eA (π u)) ((eA.orderOf_eq _).trans hou)
  have hh := f.ker.card_mul_index
  rw [index_ker, hkcard, hrcard] at hh
  exact hh.symm
end J2OutsideSizesCalculation
