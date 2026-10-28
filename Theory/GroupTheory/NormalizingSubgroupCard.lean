module
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
/-!
# Relative normalizer order through its literal conjugation homomorphism.
Source: Aschbacher, Sporadic Groups (1994),45.7(3),printed p.245.
-/
public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
omit [Finite G] in
theorem card_normalizing_subgroup_dvd (H S:Subgroup G) (hHS:H≤normalizer (S:Set G)) :
    Nat.card H∣Nat.card (H⊓centralizer (S:Set G):Subgroup G)*Nat.card (MulAut S) := by
  let f:H→*MulAut S:=S.normalizerMonoidHom.comp (inclusion hHS)
  let C:=H⊓centralizer (S:Set G)
  have hker:f.ker=C.subgroupOf H:=by
    ext x
    change S.normalizerMonoidHom ⟨x,hHS x.property⟩=1 ↔ _
    rw[←MonoidHom.mem_ker,normalizerMonoidHom_ker]
    change (x:G)∈centralizer (S:Set G) ↔ (x:G)∈H∧(x:G)∈centralizer (S:Set G)
    simp only[x.property,true_and]
  have hc:Nat.card f.ker=Nat.card C:=by
    rw[hker,Nat.card_congr (subgroupOfEquivOfLe (show C≤H from inf_le_left)).toEquiv]
  have hh:=f.ker.card_mul_index
  rw[index_ker,hc] at hh
  rw[←hh]
  exact Nat.mul_dvd_mul_left _ f.range.card_subgroup_dvd_card
end Subgroup
