module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.StandardMarking
public import Theory.GroupTheory.PCoreJoinFromQuotientCores
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Literal pair stabilizer quotients in I.5.7

The intersection of two original vertex groups maps onto the corresponding
parabolic in either vertex quotient. The kernels are precisely the two
original vertex cores restricted to their intersection. This converts the
order-four minimal-core versus order-two-core argument into the original
ambient identity Qᵢ∨Qⱼ=O₂(Gᵢ∩Gⱼ), with every inclusion retained.

Source: Aschbacher–Smith I.5.7(1), printed p.420. The subsequent model
applications discharge the explicit local core sizes and minimality.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G K L : Type*} [Group G] [Group K] [Group L]
variable {D : Diagram} (S : DSystem D G)

def pairEquivLocal (i j : Fin 3) : S.pair i j ≃* localParabolic S.family i j where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
  left_inv _x := rfl
  right_inv _x := rfl
  map_mul' _x _y := rfl

def pairQuotientMap (i j : Fin 3)
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    S.pair i j →* (localParabolic S.family i j).map (S.localQuotientMap i e) :=
  ((S.localQuotientMap i e).subgroupMap (localParabolic S.family i j)).comp
    (S.pairEquivLocal i j).toMonoidHom

theorem pairQuotientMap_surjective (i j : Fin 3)
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    Function.Surjective (S.pairQuotientMap i j e) :=
  ((S.localQuotientMap i e).subgroupMap_surjective _).comp
    (S.pairEquivLocal i j).surjective

theorem pairQuotientMap_ker (i j : Fin 3)
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    (S.pairQuotientMap i j e).ker = (S.Q i).subgroupOf (S.pair i j) := by
  ext x
  change (S.pairQuotientMap i j e x) = 1 ↔ x.val ∈ S.Q i
  have he : S.pairQuotientMap i j e x = 1 ↔
      S.localQuotientMap i e ⟨x.val, x.property.1⟩ = 1 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [he]
  change (⟨x.val, x.property.1⟩ : S.family i) ∈ (S.localQuotientMap i e).ker ↔ _
  rw [S.localQuotientMap_ker]
  constructor
  · intro h
    exact mem_map.mpr ⟨⟨x.val, x.property.1⟩, h, rfl⟩
  · rintro ⟨a, ha, he⟩
    have hax : a = ⟨x.val, x.property.1⟩ := Subtype.ext he
    exact hax ▸ ha

theorem pairQuotientMap_ker_isTwoGroup (i j : Fin 3)
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    IsPGroup 2 (S.pairQuotientMap i j e).ker := by
  rw [S.pairQuotientMap_ker]
  exact ((S.family i).isPGroup_pCoreIn 2).comap_subtype

theorem pair_core_join_of_local_models [Finite K] [Finite L] (i j : Fin 3)
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K)
    (d : (S.family j ⧸ pCore 2 (S.family j)) ≃* L)
    (hfour : Nat.card (pCore 2
      ((localParabolic S.family i j).map (S.localQuotientMap i e))) = 4)
    (htwo : Nat.card (pCore 2
      ((localParabolic S.family j i).map (S.localQuotientMap j d))) = 2)
    (hmin : ∀ N : Subgroup ((localParabolic S.family i j).map (S.localQuotientMap i e)),
      N.Normal → N ≤ pCore 2 _ → N = ⊥ ∨ N = pCore 2 _) :
    (S.pair i j).pCoreIn 2 = S.Q i ⊔ S.Q j := by
  let flip : S.pair i j ≃* S.pair j i := MulEquiv.subgroupCongr (inf_comm (S.family i) (S.family j))
  let f := S.pairQuotientMap i j e
  let g := (S.pairQuotientMap j i d).comp flip.toMonoidHom
  have hfk : f.ker = (S.Q i).subgroupOf (S.pair i j) := S.pairQuotientMap_ker i j e
  have hgk : g.ker = (S.Q j).subgroupOf (S.pair i j) := by
    rw [← MonoidHom.comap_ker, S.pairQuotientMap_ker]
    rfl
  let : Finite (S.pair i j) := Finite.of_injective
    (inclusion (show S.pair i j ≤ S.family i from inf_le_left)) (inclusion_injective _)
  have hh := f.pCore_eq_sup_kernels g (S.pairQuotientMap_surjective i j e)
    ((S.pairQuotientMap_surjective j i d).comp flip.surjective)
    (S.pairQuotientMap_ker_isTwoGroup i j e)
    (by rw [hgk]; exact ((S.family j).isPGroup_pCoreIn 2).comap_subtype) hfour htwo hmin
  have hi : S.Q i ≤ S.pair i j :=
    le_inf ((S.family i).pCoreIn_le 2) ((S.Q_le_T i).trans (S.T_le j))
  have hj : S.Q j ≤ S.pair i j :=
    le_inf ((S.Q_le_T j).trans (S.T_le i)) ((S.family j).pCoreIn_le 2)
  rw [hfk, hgk] at hh
  change (pCore 2 (S.pair i j)).map (S.pair i j).subtype = _
  rw [hh, Subgroup.map_sup, map_subgroupOf_eq_of_le hi, map_subgroupOf_eq_of_le hj]

end Quasithin.I5.DSystem
