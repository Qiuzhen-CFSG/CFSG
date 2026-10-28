module

public import Theory.GroupTheory.PStar.RadicalActionReduction

/-!
# The central-Sylow branch of fixed-core refinement

When a two-group acts on a two-star group and the action commutator has odd
order, fixed points cover its quotient and have odd kernel. The odd-kernel
extension theorem makes the fixed subgroup itself two-star. If instead the
hypothesis is a central Sylow two-subgroup of the action commutator, transfer
and two-perfectness first prove that the commutator has odd order.

This establishes the terminal central-Sylow branch in the simultaneous
GLS II, Chapter B, 5.10--5.11 induction. It does not assume balance, the
refinement conclusion or the general extension criterion.
Source: `refs/KGroup/GLS2/ChapterB.tex`, the second paragraph on PDF page 34.
-/

public section
open Subgroup Theory.GroupTheory

namespace Theory.GroupTheory
variable {G A : Type*} [Group G] [Group A] [Finite G]
  [MulDistribMulAction A G]

/-- The fixed subgroup is two-star when the action commutator has odd order. -/
theorem IsPStar.fixedPoint_of_coprime_commutator
    (hG : IsPStar 2 G) (hA : IsPGroup 2 A)
    (hcop : Nat.Coprime 2 (Nat.card (commutatorAction A G))) :
    IsPStar 2 (fixedPointSubgroup A G) := by
  let N := commutatorAction A G
  let : N.Normal := commutatorAction_normal
  let C := fixedPointSubgroup A G
  let f := (QuotientGroup.mk' N).comp C.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    have hh := congrArg (Subgroup.map (QuotientGroup.mk' N))
      (PStarAction.commutator_sup_fixed_eq_top_of_coprime hA hcop)
    change (N ⊔ C).map (QuotientGroup.mk' N) = (⊤ : Subgroup G).map (QuotientGroup.mk' N) at hh
    simpa only [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective N),
      f, MonoidHom.range_comp, range_subtype] using hh
  have hker : f.ker = N.comap C.subtype := by
    ext x
    exact QuotientGroup.eq_one_iff (x : G)
  have hkc : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hker]
    exact hcop.of_dvd_right (N.card_comap_dvd_of_injective C.subtype C.subtype_injective)
  exact isPStar_of_surjective_coprime_kernel f hf hkc (hG.quotient N)

/-- The central-Sylow terminal branch of the GLS 5.10 induction. -/
theorem IsPStar.commutator_sup_twoStarCore_fixed_of_central_sylow
    (hG : IsPStar 2 G) (hA : IsPGroup 2 A)
    (P : Sylow 2 (commutatorAction A G))
    (hc : (P : Subgroup (commutatorAction A G)).map (commutatorAction A G).subtype ≤
      center G) :
    commutatorAction A G ⊔ (pStarCore 2 (fixedPointSubgroup A G)).map
      (fixedPointSubgroup A G).subtype = ⊤ := by
  have hPc : (P : Subgroup (commutatorAction A G)) ≤ center (commutatorAction A G) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc (mem_map_of_mem _ hx)) (y : G))
  have hcop := PStarAction.coprime_card_of_central_sylow
    (hG.isPPerfect_commutatorAction (A := A)) P hPc
  rw [pStarCore_eq_top (hG.fixedPoint_of_coprime_commutator hA hcop),
    ← MonoidHom.range_eq_map, range_subtype]
  exact PStarAction.commutator_sup_fixed_eq_top_of_coprime hA hcop
end Theory.GroupTheory
