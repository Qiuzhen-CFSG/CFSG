module

public import Theory.GroupTheory.CenterFreeOddImageCore

/-!
# Central core subgroups in a center-free group

A normal subgroup `M` contained in and centralizing a normal two-subgroup `Q`
is contained in any subgroup bounding `[M,E]`, provided the normal subgroup
`E` supplements a Sylow two-subgroup and has odd image modulo `Q`.

The subgroup `M` is abelian and `C_M(E)` is trivial. Schur–Zassenhaus supplies
an odd complement `R` to `Q ∩ E` in `E`. Since `Q` centralizes `M`, also
`C_M(R)` is trivial, and coprime decomposition gives `M = [M,R] ≤ [M,E]`.
No normality or centrality assumption on the commutator bound is needed.

This is the central-core collapse used in Stellmacher (8.6), printed p.42,
equation (2), in `refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup

public theorem le_of_centerfree_odd_image_central_subgroup
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (E Q M V : Subgroup G) [E.Normal] [Q.Normal] [M.Normal]
    (hcover : E ⊔ (S : Subgroup G) = ⊤) (hQ : IsPGroup 2 Q)
    (hodd : Odd (Nat.card (E.map (QuotientGroup.mk' Q))))
    (hcenter : center G = ⊥) (hMQ : M ≤ Q)
    (hMC : M ≤ centralizer (Q : Set G)) (hcomm : ⁅M, E⁆ ≤ V) : M ≤ V := by
  classical
  have hMp : IsPGroup 2 M := hQ.of_injective (inclusion hMQ) (inclusion_injective hMQ)
  have hCbot : M ⊓ centralizer (E : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_centerfree_sylow_supplement S E M hcover hMp hcenter
  have hMM : ⁅M, M⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hMC.trans (centralizer_le hMQ))
  let _ : IsMulCommutative M := commutator_self_eq_bot_iff.mp hMM
  have hsolvM : Group.IsSolvable M :=
    Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := M)).comm x y
  let K := Q.subgroupOf E
  have hKp : IsPGroup 2 K := hQ.comap_of_injective E.subtype E.subtype_injective
  have hKodd : Odd K.index := by
    change Odd (Q.subgroupOf E).index
    rw [index_eq_card, ← natCard_map_mk'_eq E Q]
    exact hodd
  have hKcop : Nat.Coprime (Nat.card K) K.index := by
    obtain ⟨n, hn⟩ := hKp.exists_card_eq
    rw [hn]
    exact hKodd.coprime_two_left.pow_left n
  obtain ⟨R0, hR0⟩ := exists_right_complement'_of_coprime hKcop
  let R := R0.map E.subtype
  have hRE : R ≤ E := map_subtype_le _
  have hRodd : Odd (Nat.card R) := by
    rw [card_map_of_injective E.subtype_injective, ← hR0.symm.index_eq_card]
    exact hKodd
  have hEfactor : E = (Q ⊓ E) ⊔ R := by
    have hm := congrArg (fun H : Subgroup E => H.map E.subtype) hR0.sup_eq_top
    change (Q.subgroupOf E ⊔ R0).map E.subtype = (⊤ : Subgroup E).map E.subtype at hm
    rw [map_sup, subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm.symm
  have hRcop : Nat.Coprime (Nat.card R) (Nat.card M) := by
    obtain ⟨n, hn⟩ := hMp.exists_card_eq
    rw [hn]
    exact hRodd.coprime_two_right.pow_right n
  have hRfix : M ⊓ centralizer (R : Set G) = ⊥ := by
    apply bot_unique
    rw [← hCbot]
    refine le_inf inf_le_left ?_
    apply le_centralizer_iff.mp
    rw [hEfactor]
    exact sup_le
      ((inf_le_left.trans (le_centralizer_iff.mp hMC)).trans (centralizer_le inf_le_left))
      (le_centralizer_iff.mp inf_le_right)
  have hMdecomp := eq_commutator_sup_centralizer_of_solvable_coprime M R
    le_normalizer_of_normal hsolvM hRcop
  rw [hRfix, sup_bot_eq] at hMdecomp
  rw [hMdecomp]
  exact (commutator_mono le_rfl hRE).trans hcomm

end Subgroup
