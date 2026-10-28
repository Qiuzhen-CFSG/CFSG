module
public import Theory.Representation.BinaryOffender.ComponentPermutationObstruction
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Fixed vectors of a product of binary involutions

If the fixed spaces of two involutions are disjoint, their product fixes
only zero. A vector fixed by the product has the same displacement under
both involutions; that displacement is fixed by both, and hence vanishes.
The original vector then belongs to both fixed spaces as well.

Source application: the small-actor cases of Delgado--Goldschmidt--Stellmacher,
Groups and Graphs (1985), (11.3)(h), printed pp.170--171.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary_neg_pair (v : V) : -v = v := by
  have hh : v + v = 0 := by
    calc
      v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul,one_smul]
      _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide,zero_smul]
  exact neg_eq_of_add_eq_zero_left hh

theorem involution_product_fixed_eq_bot (ρ : Representation (ZMod 2) G V)
    (t s : G) (ht : t*t=1) (hs : s*s=1)
    (hd : Disjoint (fixedSpace ρ (zpowers t)) (fixedSpace ρ (zpowers s))) :
    fixedSpace ρ (zpowers (t*s)) = ⊥ := by
  apply bot_unique
  intro v hv
  have hvts := (mem_fixedSpace_zpowers_iff ρ (t*s) v).mp hv
  have hts : ρ s v = ρ t v := by
    have hh := congrArg (ρ t) hvts
    rw [←Module.End.mul_apply,←map_mul,←mul_assoc,ht,one_mul] at hh
    exact hh
  have hst : ρ s (ρ t v) = v := by
    rw [←hts,←Module.End.mul_apply,←map_mul,hs,map_one]
    rfl
  have hw : ρ t v-v = 0 := hd.le_bot
    ⟨(mem_fixedSpace_zpowers_iff _ _ _).mpr (involution_fixes_displacement ρ ht v),
      (mem_fixedSpace_zpowers_iff _ _ _).mpr (by
        rw [map_sub,hst,hts,sub_eq_add_neg,sub_eq_add_neg,
          binary_neg_pair,binary_neg_pair,add_comm])⟩
  have htv := sub_eq_zero.mp hw
  exact hd.le_bot ⟨(mem_fixedSpace_zpowers_iff _ _ _).mpr htv,
    (mem_fixedSpace_zpowers_iff _ _ _).mpr (hts.trans htv)⟩

end Representation
