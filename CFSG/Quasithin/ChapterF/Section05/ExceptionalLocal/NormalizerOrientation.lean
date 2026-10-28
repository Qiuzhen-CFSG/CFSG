module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerProduct
public import Theory.SpecificGroups.SymmetricFourProduct.IndexThree
/-!
# Orienting the actual source local comparison

The source vertex intersection contains E₂ of order96 and the marked short
centralizer of order64. Its index in H therefore divides three. When H is
not contained in the vertex, the index is three, and the symmetric-product
parabolic calculation chooses coordinates retaining that literal intersection.

The properness input is supplied separately by the graph-marked vertex model.
This module does not infer agreement between the independently chosen maps.
Source: Aschbacher--Smith F.5.7(1–2), printed p.303.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
local notation "S4" => Equiv.Perm (Fin 4)
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_H_vertex_index (hp : ¬ H c i ≤ i.range) :
    (i.range.subgroupOf (H c i)).index=3 := by
  let J := i.range.subgroupOf (H c i)
  let F := (E c i true).subgroupOf (H c i)
  have hF : Nat.card F=96 :=
    (Nat.card_congr (subgroupOfEquivOfLe (E_plane_le_H c i)).toEquiv).trans
      (normalizer_E_card c i z (sourceMarkedShort c i) (source_fusionFacts c i z h) true)
  have hFJ : F≤J := fun x hx => M_le_completion c i true hx.1
  have h96 : 96∣Nat.card J := hF ▸ card_dvd_of_le hFJ
  let B := Tcentralizer c i (sourceMarkedShort c i)
  have hB : B≤H c i := by
    change Tcentralizer c i (sourceMarkedShort c i)≤H c i
    rw [←source_normalizer_local_plane c i z h]
    exact inf_le_right
  let B' := B.subgroupOf (H c i)
  have hB' : Nat.card B'=64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv).trans
      (source_short_Tcentralizer_card c i h.embedding_injective)
  have hBJ : B'≤J := fun x hx => M_le_completion c i false (sylowImage_le_M c i false hx.1)
  have h64 : 64∣Nat.card J := hB' ▸ card_dvd_of_le hBJ
  have h192 : 192∣Nat.card J := by
    simpa only [show Nat.lcm 96 64=192 by decide] using Nat.lcm_dvd h96 h64
  have hj : J.index∣3 := by
    have hh := Nat.mul_dvd_mul_right h192 J.index
    rw [J.card_mul_index,source_H_card c i z h] at hh
    change 192*J.index∣192*3 at hh
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0<192) hh
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hj with hj|hj
  · exact (hp ((subgroupOf_eq_top).mp (J.index_eq_one.mp hj))).elim
  · exact hj

theorem exists_source_H_vertex_marking (hp : ¬ H c i ≤ i.range) :
    ∃ e : H c i ≃* S4×S4, ∀ a:H c i,
      (a:G)∈i.range ↔ (e a).1∈centralizer
        ({Theory.SpecificGroups.SymmetricSix.DuadCalculation.doubleSwap 0}:Set S4) := by
  let J := i.range.subgroupOf (H c i)
  let e := sourceHEquiv c i z h
  let K := J.map e.toMonoidHom
  have hK : K.index=3 := (J.index_map_equiv e).trans (source_H_vertex_index c i z h hp)
  have hA : (A c i true).subgroupOf (H c i)≤J := by
    intro a ha
    exact M_le_completion c i true (A_le_E c i true ha).1
  have hcore : Theory.SpecificGroups.SymmetricSix.DuadCalculation.core.prod
      Theory.SpecificGroups.SymmetricSix.DuadCalculation.core≤K := by
    rw [←source_H_core_map c i z h e]
    exact map_mono hA
  obtain ⟨u,hu⟩ := SymmetricFourProduct.index_three_marking K hK hcore
  refine ⟨e.trans u,fun a=>?_⟩
  change a∈J ↔ (u (e a)).1∈_
  rw [←hu]
  exact (mem_map_iff_mem e.injective).symm
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
