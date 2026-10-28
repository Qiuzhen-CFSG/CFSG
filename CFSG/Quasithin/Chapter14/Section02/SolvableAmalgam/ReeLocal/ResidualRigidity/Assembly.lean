module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity.QuotientBound
public import Theory.GroupAction.InvolutionQuotientOrbit
/-!
# Residual and involution assembly for a Sylow-preserving overgroup

The local quotient embeds by the actual quotient map. A Sylow subgroup in
its image pulls back to a cyclic Sylow subgroup of the local order-twenty
quotient. The faithful core-quotient action and local involution fusion then
exclude a larger odd residual. The quotient has order at most twenty,
forcing surjectivity, which lifts because the whole normal core lies in H.

Source: Aschbacher--Smith 14.2.21, printed p.989. The argument uses images
of residuals, and does not divide O²(H) by a subgroup not contained in it.
-/

open Subgroup
open CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity
private theorem sylow_bound {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (S : Sylow 2 B) (hS : (S : Subgroup B) ≤ f.range)
    (hA : Nat.card A = 20) (hcyc : ∀ T : Sylow 2 A, IsCyclic T) :
    IsCyclic S ∧ Nat.card S ≤ 4 := by
  let T := S.comapOfInjective f hf hS
  let φ : T →* S := (f.comp T.toSubgroup.subtype).codRestrict S (fun x => x.property)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y h
      exact Subtype.ext (hf (congrArg Subtype.val h))
    · intro s
      obtain ⟨a, ha⟩ := hS s.property
      refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
      change f a ∈ S
      rw [ha]
      exact s.property
  let e := MulEquiv.ofBijective φ hφ
  have hcard : Nat.card S = Nat.card T := (Nat.card_congr e.toEquiv).symm
  let := hcyc T
  refine ⟨isCyclic_of_surjective φ hφ.2, ?_⟩
  rw [hcard]
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra h
    have hd : 8 ∣ 20 := by
      rw [← hA]
      exact (hn ▸ Nat.pow_dvd_pow 2 (show 3 ≤ n by omega)).trans T.toSubgroup.card_subgroup_dvd_card
    norm_num at hd
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hnle

/-- An order-twenty local quotient and involution fusion exclude every proper overgroup. -/
public theorem range_eq_top_of_fusion
    {H M V : Type*} [Group H] [Finite H] [Group M] [Finite M]
    [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (i : H →* M) (hi : Function.Injective i)
    (QH FH : Subgroup H) [QH.Normal] (Q : Subgroup M) [Q.Normal]
    (hQ : QH.map i = Q)
    (hHq : Nat.card (H ⧸ QH) = 20)
    (hHcyc : ∀ T : Sylow 2 (H ⧸ QH), IsCyclic T)
    (hH : ¬ 3 ∣ Nat.card H)
    (S : Sylow 2 M) (hS : (S : Subgroup M) ≤ i.range)
    (θ : Q →* V) (hθ : θ.ker = (FH.map i).subgroupOf Q)
    (ρ : M ⧸ Q →* MulAut V) (hρ : Function.Injective ρ)
    (hcompat : ∀ (g : M) (q : Q), ρ (QuotientGroup.mk' Q g) (θ q) =
      θ (MulAut.conjNormal g q)) (hV : Nat.card V = 16)
    (j : Q) (hj : j ^ 2 = 1) (hjθ : θ j ≠ 1)
    (hfusion : ∀ x y : H, x ∈ QH → y ∈ QH → x ^ 2 = 1 → y ^ 2 = 1 →
      x ∉ FH → y ∉ FH → IsConj x y) : i.range = ⊤ := by
  have hpre : Q.comap i = QH := by
    rw [← hQ, comap_map_eq_self_of_injective hi]
  let f := QuotientGroup.map QH Q i hpre.ge
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [QuotientGroup.ker_map, hpre, QuotientGroup.map_mk'_self]
  let T := S.mapSurjective (QuotientGroup.mk'_surjective Q)
  have hT : (T : Subgroup (M ⧸ Q)) ≤ f.range := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, ha⟩ := hS hs
    exact ⟨QuotientGroup.mk' QH a, by change QuotientGroup.mk' Q (i a) = _; rw [ha]⟩
  obtain ⟨hTc, hTcard⟩ := sylow_bound f hf T hT hHq hHcyc
  have h5 : 5 ∣ Nat.card (M ⧸ Q) := by
    have hd := Subgroup.card_dvd_of_injective f hf
    rw [hHq] at hd
    exact (by decide : 5 ∣ 20).trans hd
  have hno := Theory.GroupAction.not_transitive_of_involution_fusion i Q θ
    (ρ.comp (QuotientGroup.mk' Q)) hcompat hV hH j hj hjθ
    (Theory.GroupAction.mapped_involution_fusion i hi QH FH Q hQ θ hθ hfusion)
  have hc : Nat.card (M ⧸ Q) ≤ 20 := by
    apply card_le_twenty_of_intransitive T hTc hTcard ρ hρ hV h5 (θ j) hjθ
    intro htrans
    apply hno
    intro y hy
    obtain ⟨a, ha⟩ := htrans y hy
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective Q a
    exact ⟨g, by change ρ (QuotientGroup.mk' Q g) (θ j) = y; rw [hg, ha]⟩
  have hfrange : f.range = ⊤ := by
    apply eq_top_of_le_card
    have hh : Nat.card f.range = 20 :=
      (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hHq
    rwa [hh]
  have hmap : i.range.map (QuotientGroup.mk' Q) = ⊤ := by
    apply top_le_iff.mp
    intro y _
    obtain ⟨a, rfl⟩ := (MonoidHom.range_eq_top.mp hfrange) y
    induction a using QuotientGroup.induction_on with
    | _ a => exact ⟨i a, ⟨a, rfl⟩, rfl⟩
  have hker : (QuotientGroup.mk' Q).ker ≤ i.range := by
    rw [QuotientGroup.ker_mk', ← hQ]
    exact QH.map_le_range i
  have he := comap_map_eq_self hker
  rw [hmap, comap_top] at he
  exact he.symm
end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity
