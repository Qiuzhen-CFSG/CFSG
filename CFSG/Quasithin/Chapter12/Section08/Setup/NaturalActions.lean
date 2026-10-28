module

public import CFSG.Quasithin.Chapter12.Section08.Setup.Normalizers
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.Core
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The literal natural-action kernels in the source setup

The original natural module supplies all automorphisms of V from L and
identifies C_L(V) with O₂(L). To identify C_LT(V), restrict LT → LT/L to
its action kernel. Its kernel embeds into O₂(L), and its image is a two-group,
so C_LT(V) is a normal two-group. Conversely O₂(LT) centralizes R₂(LT).
Thus the literal LT action has kernel O₂(LT), without assuming that equality.

The final applications use the existing binarySeedAction with its actual
flag and normalizer maps, and the existing NormalL1 geometry action.
Source: Aschbacher–Smith, Hypothesis 12.8.1(1), Notation 12.8.2 and
Lemma 12.8.3(1), printed pp.849–850.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08
open Section02 InvariantFlag
universe u
variable {G : Type u} [Group G]

/-- The kernel of the flag-independent action is the literal centralizer. -/
theorem setupSeedAction_ker (J V : Subgroup G) (hJV : J ≤ normalizer (V : Set G)) :
    (setupSeedAction J V hJV).ker = (centralizer (V : Set G)).subgroupOf J := by
  ext j
  change setupSeedAction J V hJV j = 1 ↔ (j : G) ∈ centralizer (V : Set G)
  constructor
  · intro hj v hv
    have he := congrArg (fun a : MulAut V => (a ⟨v, hv⟩ : G)) hj
    change (j : G) * v * (j : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hj
    ext v
    change (j : G) * (v : G) * (j : G)⁻¹ = v
    rw [← hj v v.property, mul_inv_cancel_right]

namespace InvariantFlag.AmbientNaturalMarking
variable {L V : Subgroup G} {hLV : L ≤ normalizer (V : Set G)} {n : ℕ}
variable [IsElementaryAbelian 2 V]

/-- Full action on V follows from the original natural marking. -/
theorem full_action (A : AmbientNaturalMarking L hLV n) (a : MulAut V) :
    ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G) := by
  let e : Additive V ≃ₗ[ZMod 2] Additive V :=
    { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
  obtain ⟨l, hl⟩ := A.geometryAction.surjective e
  refine ⟨l, l.property, fun v => ?_⟩
  have he := A.geometryAction.conjugation l (Additive.ofMul v)
  rw [hl] at he
  exact he.symm

/-- Faithfulness of the actual quotient action identifies the literal L-kernel. -/
theorem centralizer_eq_core (A : AmbientNaturalMarking L hLV n) :
    L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
  have hk : (centralizer (V : Set G)).subgroupOf L = pCore 2 L := by
    rw [← A.geometryAction.kernel]
    ext l
    change (l : G) ∈ centralizer (V : Set G) ↔ A.geometryAction.action l = 1
    constructor
    · intro hl
      apply LinearEquiv.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [A.geometryAction.conjugation, ← hl v.toMul v.toMul.property,
        mul_inv_cancel_right]
      rfl
    · intro hl v hv
      have he := A.geometryAction.conjugation l (Additive.ofMul ⟨v, hv⟩)
      rw [hl] at he
      exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  have he := congrArg (map L.subtype) hk
  simpa only [subgroupOf_map_subtype, inf_comm, pCoreIn] using he

end InvariantFlag.AmbientNaturalMarking

namespace HigherRankHypothesis
variable [Finite G] {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
variable (h : HigherRankHypothesis K T L V n)
include h

theorem full_L_action (a : MulAut V) :
    ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G) := by
  let := h.chosen.elementary
  exact h.naturalMarking.full_action a

theorem centralizer_L : L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
  let := h.chosen.elementary
  exact h.naturalMarking.centralizer_eq_core

theorem full_LT_action (structural : Structural1222 K) :
    Function.Surjective (setupSeedAction (L ⊔ (T : Subgroup G)) V
      (sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural))) := by
  intro a
  obtain ⟨x, hx, he⟩ := h.full_L_action a
  refine ⟨⟨x, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hx⟩, ?_⟩
  ext v
  exact he v

/-- The full LT action has two-group kernel, by the extension LT/L. -/
theorem action_kernel_isPGroup (structural : Structural1222 K) :
    IsPGroup 2 (setupSeedAction (L ⊔ (T : Subgroup G)) V
      (sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural))).ker := by
  let J := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf J
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer
    (show L ≤ J from le_sup_left)).mpr
      (sup_le L.le_normalizer (h.sylow_normalizes structural))
  have hgen : N ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hquot : IsPGroup 2 (J ⧸ N) := isPGroup_quotient_of_sup_eq_top N
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype hgen
  let f := setupSeedAction J V
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural))
  let q := (QuotientGroup.mk' N).comp f.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* L :=
      (J.subtype.comp (f.ker.subtype.comp q.ker.subtype)).codRestrict L (by
        intro x
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 L := by
      intro x
      have hc : (x.val.val : G) ∈ centralizer (V : Set G) := by
        exact (setupSeedAction_ker J V _).le x.val.property
      have hx : (r x : G) ∈ L.pCoreIn 2 :=
        h.centralizer_L ▸ show (r x : G) ∈ L ⊓ centralizer (V : Set G)
          from ⟨(r x).property, hc⟩
      obtain ⟨y, hy, he⟩ := hx
      exact (Subtype.ext he : y = r x) ▸ hy
    let r' : q.ker →* pCore 2 L := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 L => (x.val : G)) hab
  have hp := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at hp
  exact hp.of_equiv topEquiv

/-- The literal equality C_LT(V)=O₂(LT), as required by LocalKernel. -/
theorem centralizer_LT (structural : Structural1222 K) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let f := setupSeedAction J V
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural))
  have hk : f.ker ≤ pCore 2 J := le_sSup ⟨inferInstance, h.action_kernel_isPGroup structural⟩
  have hm := map_mono (f := J.subtype) hk
  rw [setupSeedAction_ker, subgroupOf_map_subtype, inf_comm] at hm
  exact le_antisymm hm (le_inf (map_subtype_le _) h.chosen.core_centralizes)

/-- Application to the existing action used in the parabolic and local proofs. -/
theorem binarySeedAction_surjective (F : InvariantFlag T V n) :
    Function.Surjective (F.binarySeedAction L h.chosen.normalizes) := by
  intro a
  obtain ⟨x, hx, he⟩ := h.full_L_action a
  refine ⟨⟨x, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hx⟩, ?_⟩
  ext v
  exact he v

end HigherRankHypothesis
end CFSG.Quasithin.Chapter12.Section08
