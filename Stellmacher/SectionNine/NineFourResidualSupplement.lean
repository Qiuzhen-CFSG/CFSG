module
public import Stellmacher.SectionNine.NineInitialEdgeCoreProduct

/-!
# The next residual lies in the initial-core actor join

At critical distance greater than one, an actor generating the next
stabilizer together with the initial edge also generates a group containing
the next two-residual when joined only with the initial vertex core.

The two initial cores generate the edge, and the initial core has index two
in it. The next core is normal in its stabilizer, so the normal subgroup
index formula shows that the initial-core actor join has index dividing
two in the next stabilizer. It is therefore normal of two-power index
and contains the two-residual by its defining minimality.

This is the residual-containment inference in (9.4)(4), printed p.51 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem relIndex_sup_of_normal
    {G : Type*} [Group G] [Finite G] (K T : Subgroup G) [K.Normal] :
    T.relIndex (K ⊔ T) = T.relIndex K := by
  have hmul :
      K.relIndex T * T.relIndex (K ⊔ T) = K.relIndex T * T.relIndex K := by
    calc
      K.relIndex T * T.relIndex (K ⊔ T) =
          (T ⊓ K).relIndex (K ⊔ T) := by
        rw [← Subgroup.inf_relIndex_left (H := T) (K := K)]
        exact Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
      _ = (T ⊓ K).relIndex K * K.relIndex (K ⊔ T) :=
        (Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
      _ = K.relIndex T * T.relIndex K := by
        simp [Subgroup.inf_relIndex_right, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite : K.relIndex T ≠ 0)) hmul

private theorem index_dvd_two_of_core_supplement {G : Type*} [Group G] [Finite G] (A Q L : Subgroup G) [Q.Normal]
    (hAL : A ≤ L) (hgen : Q ⊔ L = ⊤)
    (hindex : A.relIndex (Q ⊔ A) = 2) : L.index ∣ 2 := by
  have hL : L.index = L.relIndex Q := by
    rw [← Subgroup.relIndex_top_right, ← hgen, relIndex_sup_of_normal]
  have hA : A.relIndex Q = 2 := by rwa [relIndex_sup_of_normal] at hindex
  rw [hL, ← hA]
  exact Subgroup.relIndex_dvd_of_le_left Q hAL

public theorem nine_four_residual_le_core_actor_join
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (actor : G)
    (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hgenerate : (GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep) ⊔ Subgroup.zpowers actor =
      GAt ctx.Γ ctx.criticalPath.firstStep) :
    EAt ctx.Γ ctx.criticalPath.firstStep ≤
      QAt ctx.Γ ctx.criticalPath.a ⊔ Subgroup.zpowers actor := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Qa := QAt Γ cp.a
  let Qn := QAt Γ cp.firstStep
  let L := Qa ⊔ Subgroup.zpowers actor
  obtain ⟨hproduct, hcard⟩ := nine_initial_edge_core_product ctx hb
  have hQa : Qa ≤ P :=
    ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans
      cp.S_le_edge_stabilizers).trans inf_le_right
  have hQn : Qn ≤ P := by
    change Γ.twoCoreAt cp.firstStep ≤ P
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hL : L ≤ P := sup_le hQa (Subgroup.zpowers_le.mpr hactor)
  have hgen : Qn ⊔ L = P := by
    change Qn ⊔ (Qa ⊔ Subgroup.zpowers actor) = P
    rw [← sup_assoc, sup_comm Qn Qa, hproduct]
    exact hgenerate
  have hindex : Qa.relIndex (Qn ⊔ Qa) = 2 := by
    have hcount := (Qa.subgroupOf (Qn ⊔ Qa)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show Qa ≤ Qn ⊔ Qa from le_sup_right)).toEquiv] at hcount
    change Qa.relIndex (Qn ⊔ Qa) * Nat.card Qa = Nat.card (Qn ⊔ Qa : Subgroup G) at hcount
    rw [sup_comm Qn Qa, hproduct, show Nat.card (GAt Γ cp.a ⊓ GAt Γ cp.firstStep : Subgroup G) =
      2 * Nat.card Qa from hcard] at hcount
    rw [sup_comm Qn Qa, hproduct]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcount
  let QA := Qa.subgroupOf P
  let QN := Qn.subgroupOf P
  let LP := L.subgroupOf P
  let _ : QN.Normal := by
    change ((Γ.twoCoreAt cp.firstStep).subgroupOf P).Normal
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_normal P
  have hgenP : QN ⊔ LP = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQn hL, hgen, Subgroup.subgroupOf_self]
  have hindexP : QA.relIndex (QN ⊔ QA) = 2 := by
    rw [← Subgroup.subgroupOf_sup hQn hQa,
      Subgroup.relIndex_subgroupOf (sup_le hQn hQa)]
    exact hindex
  have hLP : LP.index ∣ 2 := index_dvd_two_of_core_supplement QA QN LP
    (Subgroup.subgroupOf_mono P le_sup_left) hgenP hindexP
  have hres : twoResidualSubgroup P ≤ LP := by
    apply sInf_le
    rcases (Nat.dvd_prime Nat.prime_two).mp hLP with hone | htwo
    · exact ⟨Subgroup.normal_of_index_eq_one hone, 0, by simpa using hone⟩
    · exact ⟨Subgroup.normal_of_index_eq_two htwo, 1, by simpa using htwo⟩
  change Γ.twoResidualAt cp.firstStep ≤ L
  rw [Γ.twoResidualAt_def]
  change (twoResidualSubgroup P).map P.subtype ≤ L
  rw [← Subgroup.map_subgroupOf_eq_of_le hL]
  exact Subgroup.map_mono hres

end Stellmacher.SectionNine
