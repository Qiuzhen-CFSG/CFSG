module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerKernel
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The literal square root supplied by a non-elementary R₀

The source residual centralizer R₀ has order four and contains the graph
involution f. If it is not elementary abelian, it is cyclic; its generator
has square exactly f by uniqueness of the cyclic involution. This retains
membership in the original R₀ and the actual graph-element marking.

The separate elementary-pair contradiction discharges the non-elementarity
premise. This module supplies the final elementary lifting step of F.5.5,
Aschbacher–Smith, printed p.302.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1

private theorem cyclic_of_card_four_not_elementary {B : Type*} [Group B] [Finite B]
    (hB : Nat.card B = 4) (hne : ¬ IsElementaryAbelian 2 B) : IsCyclic B := by
  by_contra hnc
  apply hne
  let : IsMulCommutative B := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hB
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro b
  have hd := orderOf_dvd_natCard b
  rw [hB] at hd
  have h4 : orderOf b ≠ 4 := fun h => hnc (isCyclic_of_orderOf_eq_card b (h.trans hB.symm))
  have hdiv : orderOf b ∣ 2 := by
    have hs := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf b ∣ 2^2 by simpa using hd)
    obtain ⟨j,hj,he⟩ := hs
    rw [he]
    interval_cases j <;> norm_num at he h4 ⊢; omega
  exact orderOf_dvd_iff_pow_eq_one.mp hdiv

variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_Rzero_cyclic_of_not_elementary (R:Sylow 2 (C c i)) (hR:Tf c i≤R)
    (hnot : ¬IsElementaryAbelian 2 (Rzero c i R)) : IsCyclic (Rzero c i R) :=
  cyclic_of_card_four_not_elementary (source_Rzero_card c i z h R hR) hnot

theorem source_Rzero_square_root_of_not_elementary (R:Sylow 2 (C c i)) (hR:Tf c i≤R)
    (hnot : ¬IsElementaryAbelian 2 (Rzero c i R)) :
    ∃r:G,r∈Rzero c i R ∧ orderOf r=4 ∧ r^2=Source.graphElement c i := by
  let := source_Rzero_cyclic_of_not_elementary c i z h R hR hnot
  obtain ⟨r,hr⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic (Rzero c i R))
  rw [source_Rzero_card c i z h R hR] at hr
  let f:Rzero c i R:=⟨Source.graphElement c i,source_graph_mem_Rzero c i z h R hR⟩
  have hf : orderOf f=2 := (orderOf_coe f).symm.trans (source_graph_order c i h.embedding_injective)
  have hsq : r^2=f := IsCyclic.eq_of_orderOf_eq_two (by rw [orderOf_pow,hr]; decide) hf
  exact ⟨r,r.property,(orderOf_coe r).trans hr,congrArg Subtype.val hsq⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
