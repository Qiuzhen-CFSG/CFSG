module
public import Theory.Frattini.InvolutorySupplement
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Commutators of two elementary factors

For two abelian subgroups E and F, the derived subgroup of their join is
[E,F]. If they normalize each other, this subgroup lies in E ∩ F and is
central. For elementary two-subgroups with finite two-group join, the
ambient Frattini subgroup is also [E,F]. The last assertion follows from
the involutory-supplement formula with the Frattini subgroup of E trivial.

Only the join needs to be finite; no ambient finiteness is assumed.
Source application: the two-seed group V in Delgado--Goldschmidt--Stellmacher,
*Groups and Graphs* (1985), (11.3), printed pp.168--171.
-/

open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

public theorem commutator_join_of_abelian (E F : Subgroup G)
    [IsMulCommutative E] [IsMulCommutative F] :
    ⁅E ⊔ F, E ⊔ F⁆ = ⁅E, F⁆ := by
  have hn : E ⊔ F ≤ normalizer ((⁅E, F⁆ : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (commutator_le_sup E F)).mp inferInstance
  have hEE : ⁅E, E⁆ = ⊥ := commutator_self_eq_bot_iff.mpr inferInstance
  have hFF : ⁅F, F⁆ = ⊥ := commutator_self_eq_bot_iff.mpr inferInstance
  have hE : ⁅E ⊔ F, E⁆ ≤ ⁅E, F⁆ :=
    commutator_sup_le_of_relative_normal (E ⊔ F) E F E ⁅E, F⁆ hn
      le_sup_left le_sup_right (hEE ▸ bot_le) (commutator_comm F E).le
  have hF : ⁅E ⊔ F, F⁆ ≤ ⁅E, F⁆ :=
    commutator_sup_le_of_relative_normal (E ⊔ F) E F F ⁅E, F⁆ hn
      le_sup_left le_sup_right le_rfl (hFF ▸ bot_le)
  apply le_antisymm
  · exact commutator_sup_le_of_relative_normal (E ⊔ F) E F (E ⊔ F) ⁅E, F⁆ hn
      le_sup_left le_sup_right ((commutator_comm E (E ⊔ F)) ▸ hE)
        ((commutator_comm F (E ⊔ F)) ▸ hF)
  · exact commutator_mono le_sup_left le_sup_right

public theorem commutator_sup_le_inf_of_abelian_normalizes (E F : Subgroup G)
    [IsMulCommutative E] [IsMulCommutative F]
    (hEF : E ≤ normalizer (F : Set G)) (hFE : F ≤ normalizer (E : Set G)) :
    ⁅E ⊔ F, E ⊔ F⁆ ≤ E ⊓ F := by
  rw [commutator_join_of_abelian E F]
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hFE)
    (le_normalizer_iff_commutator_le_right.mp hEF)

public theorem inf_le_centralizer_sup_of_abelian (E F : Subgroup G)
    [IsMulCommutative E] [IsMulCommutative F] :
    E ⊓ F ≤ centralizer ((E ⊔ F : Subgroup G) : Set G) := by
  apply le_centralizer_iff.mpr
  apply sup_le
  · exact (le_centralizer_iff_isMulCommutative.mpr inferInstance : E ≤ centralizer (E : Set G)).trans
      (centralizer_le inf_le_left)
  · exact (le_centralizer_iff_isMulCommutative.mpr inferInstance : F ≤ centralizer (F : Set G)).trans
      (centralizer_le inf_le_right)

public theorem commutator_sup_central_of_abelian_normalizes (E F : Subgroup G)
    [IsMulCommutative E] [IsMulCommutative F]
    (hEF : E ≤ normalizer (F : Set G)) (hFE : F ≤ normalizer (E : Set G)) :
    ⁅⁅E ⊔ F, E ⊔ F⁆, E ⊔ F⁆ = ⊥ :=
  commutator_eq_bot_iff_le_centralizer.mpr
    ((commutator_sup_le_inf_of_abelian_normalizes E F hEF hFE).trans
      (inf_le_centralizer_sup_of_abelian E F))

public theorem frattini_sup_eq_cross_of_elementary_normalizes (E F : Subgroup G)
    [Finite (E ⊔ F : Subgroup G)] [Finite E]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hP : IsPGroup 2 (E ⊔ F : Subgroup G))
    (hFE : F ≤ normalizer (E : Set G)) :
    (frattini (E ⊔ F : Subgroup G)).map (E ⊔ F : Subgroup G).subtype = ⁅E, F⁆ := by
  let : Fact (IsPGroup 2 E) := ⟨IsElementaryAbelian.isPGroup 2 E⟩
  have hh := frattini_map_eq_of_involutory_supplement (E ⊔ F) E F hP
    (IsElementaryAbelian.isPGroup 2 E) rfl hFE
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx)
  rwa [frattini_eq_bot_of_isElementaryAbelian (R := E) (p := 2), map_bot, bot_sup_eq] at hh

end Subgroup
