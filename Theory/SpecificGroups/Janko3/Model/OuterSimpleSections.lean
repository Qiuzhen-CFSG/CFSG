module
public import Theory.GroupTheory.SylowOuterSimpleSections
public import Theory.SpecificGroups.Janko3.Model.Order
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Orders
public import Theory.ElementaryAbelian.GeneratorRank
public import Mathlib.GroupTheory.Schreier

/-!
# The small Frattini quotient of the actual J₃ Sylow subgroup

The existing word subgroup has certified order 128 and five specified
generators. The actual model order makes it a Sylow two-subgroup; its
Frattini quotient therefore has order at most 32, and 27 does not divide
its full automorphism group. No additional finite certificate is needed.
Source: the ATLAS J₃ Sylow model used in Aschbacher–Smith 4.4.3, printed p.621.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Janko3.TwoLocal

theorem sylowCandidate_isPGroup : IsPGroup 2 sylowCandidate :=
  IsPGroup.of_card (n := 7) (by rw [sylowCandidate_card]; norm_num)

def sourceSylow : Sylow 2 Model := sylowCandidate_isPGroup.toSylow (by
  have hc := sylowCandidate.index_mul_card
  rw [sylowCandidate_card,model_card] at hc
  omega)

theorem sourceSylow_frattini_card_le :
    Nat.card (sourceSylow ⧸ frattini sourceSylow) ≤ 32 := by
  classical
  have hgen : Group.rank sylowCandidate ≤ 5 := by
    let s := Finset.univ.image sylowGenerator
    have he : (s : Set Model) = Set.range sylowGenerator := by simp [s]
    have hb := Subgroup.rank_closure_finset_le_card s
    have heq : Subgroup.closure (s : Set Model) = sylowCandidate := congrArg Subgroup.closure he
    have hrank := Subgroup.rank_congr heq.symm
    exact (hrank.le.trans hb).trans (by simpa [s] using
      (Finset.card_image_le (f := sylowGenerator) (s := Finset.univ)))
  have hr : Group.rank (sourceSylow ⧸ frattini sourceSylow) ≤ 5 :=
    (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini sourceSylow))
      (QuotientGroup.mk'_surjective _)).trans hgen
  let : Fact (IsPGroup 2 sourceSylow) := ⟨sourceSylow.isPGroup'⟩
  let : IsElementaryAbelian 2 (sourceSylow ⧸ frattini sourceSylow) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  let : CommGroup (sourceSylow ⧸ frattini sourceSylow) := IsMulCommutative.instCommGroup
  exact (Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank'
    (sourceSylow ⧸ frattini sourceSylow)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 _)))).trans
    (pow_le_pow_right' (by decide : 1 ≤ (2:ℕ)) hr)

theorem not_twentyseven_dvd_sourceSylow_aut : ¬27 ∣ Nat.card (MulAut sourceSylow) :=
  sourceSylow.isPGroup'.not_twentyseven_dvd_card_mulAut_of_frattini_card_le_thirtytwo
    sourceSylow_frattini_card_le
end Sporadic.Janko3.TwoLocal
