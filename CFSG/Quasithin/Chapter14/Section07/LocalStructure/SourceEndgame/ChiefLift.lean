module

public import Theory.GroupTheory.BinaryAlternatingChiefCentralization

/-!
# The chief-section lift in the original 14.7.71 centralizer

For C = H ∩ C_G(U), abelianness of U gives U ≤ C and relative normality
makes C normal in H. The source index-four intersection and order-two
star image give U-index at most two in D = Uα ∩ C. The normalizer bound
places [t,C] in D. The finite-group lifting theorem therefore proves
[K,C] ≤ U on the original groups, with the literal map qH : H → S₅.

The even involution condition is retained: a transposition does not give
this displacement theorem. No elementary structure or factored action on
C/U is assumed; the needed chief quotient is constructed by the lower
lifting theorem. No CriticalFusion/Setup input is used.

The hypotheses are the earlier local inputs of 14.7.69–70 and 14.5.15(4).
This discharges the centralization step, not the remaining factor placement,
factor counting, or Ru recognition arguments. The printed C_H(Uα) in the
intermediate commutator is tautological; the required subgroup is C_H(U).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.71(1), printed p.1075 (PDF p.1092).
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame

/-- The original perfect K centralizes C_H(U)/U from the source intersection
index and the even involution in the literal star image of Uα. -/
theorem centralizer_commutator_le
    {G : Type*} [Group G] [Finite G]
    (H QH U Uα K : Subgroup G) (qH : H →* Equiv.Perm (Fin 5))
    (hq : Function.Surjective qH) (hqker : qH.ker = QH.subgroupOf H)
    (hQH : QH ≤ H) (hp : IsPGroup 2 QH) (hUQ : U ≤ QH)
    [IsMulCommutative U] [(U.subgroupOf H).Normal]
    (hKH : K ≤ H) [Group.IsPerfect K] [(K.subgroupOf H).Normal]
    (hKeven : ∀ k : K, qH ⟨k, hKH k.property⟩ ∈ alternatingGroup (Fin 5))
    (hCQ : H ⊓ centralizer (U : Set G) ≤ QH)
    (hCN : H ⊓ centralizer (U : Set G) ≤ normalizer Uα)
    (hUαH : Uα ≤ H) (h70 : U.relIndex Uα = 4)
    (h69 : Nat.card ((Uα.subgroupOf H).map qH) = 2)
    (t : H) (ht : (t : G) ∈ Uα) (htord : orderOf (qH t) = 2)
    (hteven : qH t ∈ alternatingGroup (Fin 5)) :
    ⁅K, H ⊓ centralizer (U : Set G)⁆ ≤ U := by
  let C := H ⊓ centralizer (U : Set G)
  let D := Uα ⊓ C
  have hUH : U ≤ H := hUQ.trans hQH
  have hUC : U ≤ C := le_inf hUH (by
    intro u hu v hv
    exact congrArg Subtype.val (mul_comm (⟨v,hv⟩ : U) ⟨u,hu⟩))
  have hCeq : C.subgroupOf H = centralizer (U.subgroupOf H : Set H) := by
    ext c
    constructor
    · intro hc u hu
      exact Subtype.ext (hc.2 u hu)
    · intro hc
      refine ⟨c.property, ?_⟩
      intro u hu
      exact congrArg Subtype.val (hc ⟨u,hUH hu⟩ hu)
  have hCnormal : (C.subgroupOf H).Normal := by rw [hCeq]; infer_instance
  let _ := hCnormal
  have hperfect : Group.IsPerfect (K.subgroupOf H) :=
    Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      (subgroupOfEquivOfLe hKH).symm.surjective
  let _ := hperfect
  have hstar : QH.relIndex Uα = 2 := by
    rw [← relIndex_ker, hqker, relIndex_subgroupOf hUαH] at h69
    exact h69
  have hquot : U.relIndex (QH ⊓ Uα) = 2 := by
    have hh := relIndex_inf_mul_relIndex U QH Uα
    rw [inf_eq_left.mpr hUQ, h70, hstar] at hh
    omega
  have hD : D ≤ QH ⊓ Uα := le_inf (inf_le_right.trans hCQ) inf_le_left
  have hindex : U.relIndex D ≤ 2 :=
    (relIndex_le_of_le_right hD (by rw [hquot]; decide)).trans_eq hquot
  have hpker : IsPGroup 2 qH.ker := by rw [hqker]; exact hp.comap_subtype
  have hCker : C.subgroupOf H ≤ qH.ker := by
    rw [hqker]
    exact fun c hc => hCQ hc
  have hcomm : ⁅zpowers t,C.subgroupOf H⁆ ≤ D.subgroupOf H := by
    have hn : C.subgroupOf H ≤ normalizer (Uα.subgroupOf H) := by
      intro c hc
      rw [mem_normalizer_iff]
      intro u
      exact mem_normalizer_iff.mp (hCN hc) u
    have hl : ⁅zpowers t,C.subgroupOf H⁆ ≤ Uα.subgroupOf H :=
      (commutator_mono (zpowers_le.mpr (show t ∈ Uα.subgroupOf H from ht))
        (le_refl (C.subgroupOf H))).trans
        (le_normalizer_iff_commutator_le_left.mp hn)
    have hr : ⁅zpowers t,C.subgroupOf H⁆ ≤ C.subgroupOf H :=
      commutator_le_right _ _
    exact fun x hx => ⟨hl hx, hr hx⟩
  have hh := BinaryAlternatingChiefCentralization.commutator_le qH hq hpker
    (C.subgroupOf H) (U.subgroupOf H) (K.subgroupOf H)
    (fun u hu => hUC hu) hCker
    (fun k => hKeven ⟨k,k.property⟩) t htord hteven (D.subgroupOf H)
    (fun d hd => hd.2) (by rwa [relIndex_subgroupOf (inf_le_right.trans inf_le_left)]) hcomm
  have hm := map_mono (f := H.subtype) hh
  rw [map_commutator, map_subgroupOf_eq_of_le hKH,
    map_subgroupOf_eq_of_le (show C ≤ H from inf_le_left),
    map_subgroupOf_eq_of_le hUH] at hm
  exact hm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
